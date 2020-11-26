use bench_utils::{end_timer, start_timer};
use byteorder::WriteBytesExt;
use log::trace;
use std::marker::PhantomData;

use super::HashToCurve;
use crate::hashers::{
    composite::{CompositeHasher, COMPOSITE_HASHER, CRH},
    DirectHasher, Hasher
};
use crate::{PrivateKey, BLSError};

use algebra::{
    bls12_377::Parameters,
    curves::models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    curves::models::{bls12::Bls12Parameters, SWModelParameters},
    AffineCurve, ConstantSerializedSize, Zero,
};

use algebra::{
    bls12_377::{Bls12_377, Fq12, G1Projective, G2Affine, G2Projective},
    CanonicalDeserialize, CanonicalSerialize, One, PairingEngine, ProjectiveCurve,
    SerializationError,
};

use std::ops::Neg;

use once_cell::sync::Lazy;

const NUM_TRIES: u8 = 255;

/// Composite (Bowe-Hopwood CRH, Blake2x XOF) Try-and-Increment hasher for BLS 12-377.
pub static COMPOSITE_HASH_TO_G1: Lazy<
    TryAndIncrement<CompositeHasher<CRH>, <Parameters as Bls12Parameters>::G1Parameters>,
> = Lazy::new(|| TryAndIncrement::new(&*COMPOSITE_HASHER));

/// Direct (Blake2s CRH, Blake2x XOF) Try-and-Increment hasher for BLS 12-377.
/// Equivalent to Blake2xs.
pub static DIRECT_HASH_TO_G1: Lazy<
    TryAndIncrement<DirectHasher, <Parameters as Bls12Parameters>::G1Parameters>,
> = Lazy::new(|| TryAndIncrement::new(&DirectHasher));

/// A try-and-increment method for hashing to G1 and G2. See page 521 in
/// https://link.springer.com/content/pdf/10.1007/3-540-45682-1_30.pdf.
#[derive(Clone)]
pub struct TryAndIncrement<'a, H, P> {
    hasher: &'a H,
    curve_params: PhantomData<P>,
}

impl<'a, H, P> TryAndIncrement<'a, H, P>
where
    H: Hasher<Error = BLSError>,
    P: SWModelParameters,
{
    /// Instantiates a new Try-and-increment hasher with the provided hashing method
    /// and curve parameters based on the type
    pub fn new(h: &'a H) -> Self {
        TryAndIncrement {
            hasher: h,
            curve_params: PhantomData,
        }
    }
}

impl<'a, H, P> HashToCurve for TryAndIncrement<'a, H, P>
where
    H: Hasher<Error = BLSError>,
    P: SWModelParameters,
{
    type Output = GroupProjective<P>;

    fn hash(
        &self,
        domain: &[u8],
        message: &[u8],
        extra_data: &[u8],
    ) -> Result<Self::Output, BLSError> {
        self.hash_with_attempt(domain, message, extra_data)
            .map(|res| res.0)
    }
}

impl<'a, H, P> TryAndIncrement<'a, H, P>
where
    H: Hasher<Error = BLSError>,
    P: SWModelParameters,
{
    /// Hash with attempt takes the input, appends a counter
    pub fn hash_with_attempt(
        &self,
        domain: &[u8],
        message: &[u8],
        extra_data: &[u8],
    ) -> Result<(GroupProjective<P>, usize), BLSError> {
        let num_bytes = GroupAffine::<P>::SERIALIZED_SIZE;
        let hash_loop_time = start_timer!(|| "try_and_increment::hash_loop");
        let hash_bytes = hash_length(num_bytes);
        println!("Hash bytes {}", hash_bytes);
        let inner_hash = self.hasher.crh(domain, message, hash_bytes)?;

        let mut counter = [0; 1];
        for c in 0..NUM_TRIES {
            (&mut counter[..]).write_u8(c as u8)?;

            // produce a hash with sufficient length
            let msg_for_xof = &[&counter, extra_data, &inner_hash].concat();
            let candidate_hash = self.hasher.xof(domain, msg_for_xof, hash_bytes)?;

            println!("possible bytes {:?}", &candidate_hash[..num_bytes]);
            // handle the Celo deployed bit extraction logic
            // #[cfg(feature = "compat")]
            let candidate_hash = {
                use algebra::serialize::{Flags, SWFlags};

                let mut candidate_hash = candidate_hash[..num_bytes].to_vec();
                let positive_flag = candidate_hash[num_bytes - 1] & 2 != 0;
                if positive_flag {
                    println!("positive");
                    candidate_hash[num_bytes - 1] |= SWFlags::PositiveY.u8_bitmask();
                } else {
                    println!("negative");
                    candidate_hash[num_bytes - 1] &= !SWFlags::PositiveY.u8_bitmask();
                }
                candidate_hash
            };

            if let Some(p) = GroupAffine::<P>::from_random_bytes(&candidate_hash[..num_bytes]) {
                trace!(
                    "succeeded hashing \"{}\" to curve in {} tries",
                    hex::encode(message),
                    c
                );
                end_timer!(hash_loop_time);

                println!("Made point {}", p);

                let scaled = p.scale_by_cofactor();
                if scaled.is_zero() {
                    continue;
                }

                return Ok((scaled, c as usize));
            }
        }
        Err(BLSError::HashToCurveError)
    }
}

/// Given `n` bytes, it returns the value rounded to the nearest multiple of 256 bits (in bytes)
/// e.g. 1. given 48 = 384 bits, it will return 64 bytes (= 512 bits)
///      2. given 96 = 768 bits, it will return 96 bytes (no rounding needed since 768 is already a
///         multiple of 256)
fn hash_length(n: usize) -> usize {
    let bits = (n * 8) as f64 / 256.0;
    let rounded_bits = bits.ceil() * 256.0;
    rounded_bits as usize / 8
}

#[cfg(test)]
mod test {
    use super::*;
    use algebra::{bls12_377::Parameters, CanonicalSerialize, ProjectiveCurve};
    use rand::{Rng, RngCore};

    #[test]
    fn test_hash_length() {
        assert_eq!(hash_length(48), 64);
        assert_eq!(hash_length(96), 96);
    }

    #[test]
    fn hash_to_curve_direct_g1() {
        let h = DirectHasher;
        hash_to_curve_test::<<Parameters as Bls12Parameters>::G1Parameters, _>(h)
    }

    #[test]
    fn hash_to_curve_composite_g1() {
        let h = CompositeHasher::<CRH>::new().unwrap();
        hash_to_curve_test::<<Parameters as Bls12Parameters>::G1Parameters, _>(h)
    }

    #[test]
    fn hash_to_curve_direct_g2() {
        let h = DirectHasher;
        hash_to_curve_test::<<Parameters as Bls12Parameters>::G2Parameters, _>(h)
    }

    #[test]
    fn hash_to_curve_composite_g2() {
        let h = CompositeHasher::<CRH>::new().unwrap();
        hash_to_curve_test::<<Parameters as Bls12Parameters>::G2Parameters, _>(h)
    }

    fn hash_to_curve_test<P: SWModelParameters, X: Hasher<Error = BLSError>>(h: X) {
        let hasher = TryAndIncrement::<X, P>::new(&h);
        let mut rng = rand::thread_rng();
        for length in &[10, 25, 50, 100, 200, 300] {
            let mut input = vec![0; *length];
            rng.fill_bytes(&mut input);
            hasher.hash(&b"domain"[..], &input, &b"extra"[..]).unwrap();
        }
    }

    pub fn generate_test_data<R: Rng>(rng: &mut R) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let msg_size: u8 = rng.gen();
        let mut msg: Vec<u8> = vec![0; msg_size as usize];
        for i in msg.iter_mut() {
            *i = rng.gen();
        }

        let mut domain = vec![0u8; 8];
        for i in domain.iter_mut() {
            *i = rng.gen();
        }

        let extra_data_size: u8 = rng.gen();
        let mut extra_data: Vec<u8> = vec![0; extra_data_size as usize];
        for i in extra_data.iter_mut() {
            *i = rng.gen();
        }

        (domain, msg, extra_data)
    }

    pub fn test_hash_to_group<P: SWModelParameters, H: HashToCurve<Output = GroupProjective<P>>>(
        hasher: &H,
        rng: &mut impl Rng,
        expected_hashes: Vec<Vec<u8>>,
    ) {
        for expected_hash in expected_hashes.into_iter() {
            let (domain, msg, extra_data) = generate_test_data(rng);
            let g = hasher.hash(&domain, &msg, &extra_data).unwrap();
            let mut bytes = vec![];
            g.into_affine().serialize(&mut bytes).unwrap();
            assert_eq!(expected_hash, bytes);
        }
    }
}

#[cfg(all(test, feature = "compat"))]
mod compat_tests {
    #![allow(clippy::op_ref)]

    use super::*;
    use algebra::{
        curves::models::{
            bls12::{G1Affine, G1Projective},
            ModelParameters,
        },
        CanonicalSerialize, Field, FpParameters, FromBytes, PrimeField, ProjectiveCurve,
        SquareRootField,
    };
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    const RNG_SEED: [u8; 16] = [
        0x5d, 0xbe, 0x62, 0x59, 0x8d, 0x31, 0x3d, 0x76, 0x32, 0x37, 0xdb, 0x17, 0xe5, 0xbc, 0x06,
        0x54,
    ];

    pub fn get_point_from_x_g1<P: Bls12Parameters>(
        x: <P::G1Parameters as ModelParameters>::BaseField,
        greatest: bool,
    ) -> Option<G1Affine<P>> {
        // Compute x^3 + ax + b
        let x3b = <P::G1Parameters as SWModelParameters>::add_b(
            &((x.square() * &x) + &<P::G1Parameters as SWModelParameters>::mul_by_a(&x)),
        );

        x3b.sqrt().map(|y| {
            let negy = -y;

            let y = if (y < negy) ^ greatest { y } else { negy };
            G1Affine::<P>::new(x, y, false)
        })
    }

    fn compat_hasher<P: Bls12Parameters>(
        domain: &[u8],
        message: &[u8],
        extra_data: &[u8],
    ) -> Result<(G1Projective<P>, usize), BLSError> {
        const NUM_TRIES: usize = 256;
        const EXPECTED_TOTAL_BITS: usize = 512;
        const LAST_BYTE_MASK: u8 = 1;
        const GREATEST_MASK: u8 = 2;

        let hasher = &*COMPOSITE_HASHER;

        let fp_bits =
            (((<P::Fp as PrimeField>::Params::MODULUS_BITS as f64) / 8.0).ceil() as usize) * 8;
        let num_bits = fp_bits;
        let num_bytes = num_bits / 8;

        //round up to a multiple of 8
        let hash_fp_bits =
            (((<P::Fp as PrimeField>::Params::MODULUS_BITS as f64) / 256.0).ceil() as usize) * 256;
        let hash_num_bits = hash_fp_bits;
        assert_eq!(hash_num_bits, EXPECTED_TOTAL_BITS);
        let hash_num_bytes = hash_num_bits / 8;
        let mut counter: [u8; 1] = [0; 1];
        let hash_loop_time = start_timer!(|| "try_and_increment::hash_loop");
        for c in 0..NUM_TRIES {
            (&mut counter[..]).write_u8(c as u8)?;
            let hash = hasher.hash(
                domain,
                &[&counter, extra_data, &message].concat(),
                hash_num_bytes,
            )?;
            let (possible_x, greatest) = {
                //zero out the last byte except the first bit, to get to a total of 377 bits
                let mut possible_x_bytes = hash[..num_bytes].to_vec();
                let possible_x_bytes_len = possible_x_bytes.len();
                let greatest =
                    (possible_x_bytes[possible_x_bytes_len - 1] & GREATEST_MASK) == GREATEST_MASK;
                possible_x_bytes[possible_x_bytes_len - 1] &= LAST_BYTE_MASK;
                let possible_x = P::Fp::read(possible_x_bytes.as_slice());
                if possible_x.is_err() {
                    continue;
                }

                (possible_x.unwrap(), greatest)
            };
            match get_point_from_x_g1::<P>(possible_x, greatest) {
                None => continue,
                Some(x) => {
                    trace!(
                        "succeeded hashing \"{}\" to G1 in {} tries",
                        hex::encode(message),
                        c
                    );
                    end_timer!(hash_loop_time);
                    let scaled = x.scale_by_cofactor();
                    if scaled.is_zero() {
                        continue;
                    }
                    return Ok((scaled, c));
                }
            }
        }
        Err(BLSError::HashToCurveError)
    }

    fn generate_compat_expected_hashes(num_expected_hashes: usize) -> Vec<Vec<u8>> {
        let mut rng = XorShiftRng::from_seed(RNG_SEED);

        let mut expected_hashes = vec![];
        for _ in 0..num_expected_hashes {
            let (domain, msg, extra_data) = super::test::generate_test_data(&mut rng);
            let expected_hash_point = compat_hasher::<Parameters>(&domain, &msg, &extra_data)
                .unwrap()
                .0;

            let mut expected_hash = vec![];
            expected_hash_point
                .into_affine()
                .serialize(&mut expected_hash)
                .unwrap();
            expected_hashes.push(expected_hash);
        }

        expected_hashes
    }

    #[test]
    fn test_hash_to_curve_g1() {
        let mut rng = XorShiftRng::from_seed(RNG_SEED);
        let expected_hashes = generate_compat_expected_hashes(1000);

        let hasher = TryAndIncrement::<_, <Parameters as Bls12Parameters>::G1Parameters>::new(
            &*COMPOSITE_HASHER,
        );
        super::test::test_hash_to_group(&hasher, &mut rng, expected_hashes)
    }
}

#[cfg(all(test, not(feature = "compat")))]
mod non_compat_tests {
    use super::*;
    use crate::hash_to_curve::try_and_increment::COMPOSITE_HASH_TO_G1;
    use algebra::bls12_377::Parameters;
    use rand::SeedableRng;
    use algebra::FromBytes;
    use rand_xorshift::XorShiftRng;
    use blake2s_simd::Params;

    #[test]
    fn test_hash_to_curve_g1() {

        let epoch_data_hex =
         "fdd542ddf4fdd764cddfee7f0a33f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f20e1fe6aa16efafe6bb2e66ff7bf8499f85cdec99907ce3e22e7cbce5166ee772753d540b1b1515adc70314000e74060ea2ca300f81ec9c7e904a8a676a53e11e336d7b6afea034afd62a07c40e2e0cb8a033a084745612c91fd0b8fe37c0109f7570b75d3f75f93357fbbff25ccc4e7f24ece3c70f611395f768e3273bf3b99aa068a8d8dd2e2868b010238070253671905c0f7483e4e274035b52bf58918b7b9b67d551f50ea1703e50312075f561cd041382a0a6389ec5f781ce70b48b8bf5aa89bbeff9aacf9dbfd2f61263e977772e681b38fc8f9b2739499fbddc95435506c6c9416375c0c10c03910983acb2800be47f2713a01aaa95da94fc4b8cdb5edabfa8052bf18281f9038f8b2e2800ec25151184b64ffc2e3385f40c2fdd542ddf4fdd764cddfee7f0933f1b9bc93330f9c7d44ce979da3ccdcef4ea6aa816263a3b4b8e1628000ce81c0d4594601f03d928fd309504ded4a7d22c66dae6d5fd50794fac540f980c4c197150774108e8ac25822fb171ec7f90212eeaf16eaa6efbf266bfe76ff4b9889cfe59d9c79e0ec2372beec1c65e67e7732550d141b1ba5c50d170304700e04a6ce320a80ef917c9c4e806a6a57ea13316e736dfbaa3ea0d42f06ca07240ebeac38a083705414c612d9bff038ce1790707fb550377dff3559f3b7fb5fc24c7c2eefe4cc03671f91f365e72833f7bb93a96aa0d8d8282d6eb8182080732030759651007c8fe4e374025453bb529f88719b6bdb57f501a57e31503e2071f065c5011d84a3a23096c8fe85c771be8084fbab85bae9fbafc99abfddff1266e2737927671e38fb889c2f3b4799b9df9d4c5503c5c6466971c3c500019c0381a9b38c02e07b241fa713a09ada95fa448cdb5cdbbeaa0f28f58b81f20189832f2b0ee8201c1585b144f62f3c8ef30524dc5f2dd44ddf7f4dd6fcedfe9730139fcb3b39f3c0d947e47cd939caccfdee64aa1a2836364a8b1b2e0608e01c084c9d651400df23f9389d00d5d4aed42762dce6daf6557d40a95f0c940f481c7c59714007e1a8288c25b27fe1719c2f2061d345a42fd25a0e5e83f4db5586ac7979ac2053cd95d8f2efd3e959571ceccaa743e02cf4be3f5d7aaddb0b06fc9aff9e46edff92270e170d1a3f429bbb8b9326a67f311b7db56c441f5011e51b902889114cef7e7af6bc232a9e5460ec6e7d89598d1c2c26f4b03068a9792a28a8e5c104369718a414b534515fd0ff2d8601";


         let extra_data_hex = "000000000080ca";

         let epoch_data = &hex::decode(epoch_data_hex).unwrap();
         let extra_data = &hex::decode(extra_data_hex).unwrap();

        let epoch_data_inner_hash = COMPOSITE_HASHER.crh(b"ULforxof", epoch_data, 64).unwrap();
        println!("Inner hash {:?}", epoch_data_inner_hash);

        let hasher = TryAndIncrement::<_, <Parameters as Bls12Parameters>::G1Parameters>::new(
            &*COMPOSITE_HASHER,
        );

        let epoch_data_hash = hasher.hash(b"ULforxof", epoch_data, extra_data).unwrap();
        println!("Hashed to group {}", epoch_data_hash);

        let privkey_hex = "0c03f813259dd2542a32778cbdb635684e675b972527eefc26e9f4892d16370d";
        let mut privkey_data = &hex::decode(privkey_hex).unwrap();
        let privkey_index = algebra::bls12_377::Fr::deserialize(&**privkey_data).unwrap();
        println!("Secret index {}", privkey_index);
        let priv_key = PrivateKey::from(privkey_index);
        let public_key = priv_key.to_public();
        let mut bytes = vec![];
        public_key.serialize_uncompressed(&mut bytes);
        println!("To public key {:?}", bytes);

        println!("Sign that point {:?}", priv_key.sign_raw(&epoch_data_hash));
        println!("Sign that message {:?}", priv_key.sign(epoch_data, extra_data, &hasher));

        let sig = priv_key.sign(epoch_data, extra_data, &hasher).unwrap();
        let mut sig_bytes = vec![];
        sig.serialize(&mut sig_bytes);
        println!("Sig bytes {:?}", sig_bytes);
        println!("Sig {}", sig.as_ref());

        /*
        let p1 = algebra::bls12_377::G1Affine::prime_subgroup_generator().neg();
        println!("Point in G1 {}", p1);
        match algebra::bls12_377::G1Affine::get_point_from_x(p1.x, false) {
            Some(pp) => println!("reconstruct {}", pp),
            None => println!("didnt work")
        }

        match algebra::bls12_377::G1Affine::get_point_from_x(p1.x, true) {
            Some(pp) => {
                println!("reconstruct {}", pp);
                let mut bytes = vec![];
                pp.serialize(&mut bytes);
                println!("Serialize 2 {:?}", bytes);
            }
            None => println!("didnt work")
        }

        let mut bytes = vec![];
        p1.serialize(&mut bytes);

        println!("Serialize {:?}", bytes);
        println!("Reading {}", algebra::bls12_377::Fq::read(&*bytes).unwrap());

        let p = algebra::bls12_377::G2Affine::prime_subgroup_generator().neg();
        println!("Point in G2 {}", p);

        match algebra::bls12_377::G2Affine::get_point_from_x(p.x, false) {
            Some(pp) => println!("reconstruct {}", pp),
            None => println!("didnt work")
        }

        println!("fq2 one {}", algebra::bls12_377::FQ2_ONE);

        println!("x*y = {}", p.x*p.y);
        let mut rng = XorShiftRng::from_seed([
            0x5d, 0xbe, 0x62, 0x59, 0x8d, 0x31, 0x3d, 0x76, 0x32, 0x37, 0xdb, 0x17, 0xe5, 0xbc,
            0x06, 0x54,
        ]);

        let pre = &hex::decode("1ae3a4617c510eac63b05c06ca1493b1a22d9f300f5138f1ef3622fba094800170b5d44300000008508c000000000010").unwrap();
        let res = COMPOSITE_HASHER.xof(b"ULforxof", pre, 64).unwrap();
        println!("hash result {:?} pre {:?}", res, pre);

        let mut hash_result = Params::new()
                .hash_length(32)
                .max_leaf_length(32)
                .inner_hash_length(32)
                .fanout(0)
                .max_depth(0)
                .personal(b"")
                .node_offset(274877906944)
                .to_state()
                .update(pre)
                .finalize()
                .as_ref()
                .to_vec();
        
        let mut hash_result2 = Params::new()
                .hash_length(32)
                .max_leaf_length(32)
                .inner_hash_length(32)
                .fanout(0)
                .max_depth(0)
                .personal(b"")
                .node_offset(274877906944 + 1)
                .to_state()
                .update(pre)
                .finalize()
                .as_ref()
                .to_vec();
        
        println!("blake2s hash result {:?} {:?}", hash_result, hash_result2);
        */

        /*
        let expected_hashes = vec![
            "a7e17c99126acf78536e64fffe88e1032d834b483584fe5757b1deafa493c97a132572c7825ca4f617f6bcef93b93980",
            "21e328cfedb263f8c815131cc42f0357ab0ba903d855a11de6e7bcd7e61375a818d1b093bcf9fce224536714efad5c80",
            "fcc8bc80a528b32762ad3b3f72d40b069083b833ad4b6e135040414e2634657e1cf1ec070235ba1425f350df8c585d81",
            "9b99c3cee5f7c486f962b1391b4108cd464b05bc24b2e488e9aa04f848467315ed70d83d3abfa63150564ad0c549c480",
            "9df1b6ba0e8d2a42866d78a90b5fdf56cea80b2ec588774ceb7cc4f414d7b49ca55f81169535a4c3a4c7c39148af3e81",
            "f365f54ba587b863d5d5ecef6a2932f4eb225c0cd2c4e727c3fa5b1a30fbcfa8e2a2e0d7a68476ee10d90b3b8846b400",
            "1cb6008bca08b85df6f9a87ca141533145ed88abb0bbace96f4b1ca42d15ba888d4948c21548207a0abd22d5c234d180",
            "1c529f631ddaffde7cbe62bbb8d48cc8dbe59b8548dc69b156d0568c7aae898d8051a3ef31ad17c60a85ad82203a9b81",
            "de54da7a8813a30c267d662d428e28520a159b51a9e226ceb663d460d9065b66a9586cb8b3a9ba0ef0e27c626f20dc00",
            "b68e1db4b648801676a79ac199eaf003757bf2a96cdbb804bfefe0484afdc0cc299d50d660221d1de374e92c44291200",
        ].into_iter().map(|x| hex::decode(&x).unwrap()).collect::<Vec<_>>();

        super::test::test_hash_to_group(&*COMPOSITE_HASH_TO_G1, &mut rng, expected_hashes)
*/
    }

    #[test]
    fn test_hash_to_curve_g2() {
        let mut rng = XorShiftRng::from_seed([
            0x5d, 0xbe, 0x62, 0x59, 0x8d, 0x31, 0x3d, 0x76, 0x32, 0x37, 0xdb, 0x17, 0xe5, 0xbc,
            0x06, 0x54,
        ]);

        let expected_hashes = vec![
            "9c76f364d39ce5747f475088f459a11cb32d39033245c039104dfe88a71047ea078d6f15ed9fc64539410167ffe1800020ec8138f9f8b03c675f4ff33d621c76f41784bf994aa8cf53b2e11961f4c77caaab6681dc29bb2f90e14ecd05a5f500",
            "ffb0b3275d2188bee71e0f626b2bc422ee4ce23692e6d329e085ec74413410cedd354d9571e9de149a286dc48ba83d012ad171f4280acbc3c3d946086fe2a0c9f56d271f0c9bb13e78774cb6244b2e84c24116d8ff76311cf2f76db741ab7200",
            "59af04e977ac914d077d1488639b90dfb5b723bf8516157b9ebc8b584a0f507f20c3b758284fe3c91bc93df86244a9017e06d3f930163642a3c85965aac19ea8a18b0bd08d7bd44e99e343acfe24f98ff6f2401432187a07dd97320f73fa7300",
            "5a1610b23a5a5be0ee255fcc766d0f6d384b3d51b4364d5587102e8905b7233fd5b274973451cb56ca69a945832c1000d0b2744278ffdf5cd33f11bcc4ecc5759b0d5b90f54d454909d73f49c1226e428acfb25995d83ba44826adb8158f1281",
            "d82143317b1a5b90e633a4a208129edd526f9137b9c47221c827aa6317be94cb1bc006ba8afce455be5bf51ee6f184011c535bee7ab3e954731a6a96edb3ea9a6c1d02916817147355a2406757023e27fb2f58fec61f37ddb6125c797bfa5780",
            "48bfa38e3c4a6a7de2a5c4b8c57671c7b1bfb2c225d89786cbcd065b2b7844b910b5cbfc334eff1956bc7245127d970154c38985b770d11994c20072a053f0f720028615753c9c42372580782dd49653b4c0fee2a8e88de1697678a505ffc980",
            "ddc0e29af05439bcb5157802afd9a112394fb190e0dda7b5c7852693da3b3403c911751c24b28af1d05e76326d1117007f14cc765d5c3e73adbbcf7a1d59cf58186d7b576d3e58ccafd2ea527bf31651f4b0d0ba44ee5b54ec6c86c2e1bf1b01",
            "ddc865ffe876a3e19c1401f784eaf88b50c4f04cfaadf7690173a33385cb5af899189478cdbc1abbe8d8a89768e411003a5000c7866f3a5648d7944e97bcbff87f89cd26045dc15494036ce4ce799de532438576bfe32389269a6e3a4ce98201",
            "8de37ce0a7105c14880d9201f2ac1c724e031904f9c88614fa414ad57f00c89e596fadb4f5151c84f4ea04d576931c008fc43faec79d0e300d2192a8e376b25f920f14f467f050e4f2869012fce196e9af5f2041889031e2bbe81c6b3d344480",
            "10341299c41179084a0bfee8b65bac0f48af827daad4f01d3e9925a3b0335736c5d13f44765fecec45941781da5a1000d0bb26a4faa4dc8060b0b2dd0cb6acce7dd10bd081dac7f263b97aec89d6434a55b31a65b3e25f59c40ea92887b03180",
        ].into_iter().map(|x| hex::decode(&x).unwrap()).collect::<Vec<_>>();
        let hasher_g2 = TryAndIncrement::<_, <Parameters as Bls12Parameters>::G2Parameters>::new(
            &*COMPOSITE_HASHER,
        );
        super::test::test_hash_to_group(&hasher_g2, &mut rng, expected_hashes)
    }
}
