use bls_crypto::{hash_to_curve::{HashToCurve, try_and_increment::TryAndIncrement},PrivateKey};
use bls_crypto::hashers::{
    composite::{CompositeHasher, COMPOSITE_HASHER, CRH},
    DirectHasher, Hasher
};
use algebra::{CanonicalDeserialize, CanonicalSerialize};
use algebra::{
    bls12_377::Parameters,
    curves::models::short_weierstrass_jacobian::{GroupAffine, GroupProjective},
    curves::models::{bls12::Bls12Parameters, SWModelParameters},
    AffineCurve, ConstantSerializedSize, Zero,
};

use clap::{App, Arg};

fn main() {
    let matches = App::new("Compute BHHash")
        .about("Compute bhhash and related sig")
        .arg(
            Arg::with_name("key")
                .short("k")
                .value_name("KEY")
                .help("Sets the BLS private key")
                .required(true),
        )
        .arg(
            Arg::with_name("extra-data")
                .short("e")
                .value_name("EXTRA_DATA")
                .help("Sets the extra data")
                .required(true),
        )
        .arg(
            Arg::with_name("epoch-data")
                .short("d")
                .value_name("EPOCH_DATA")
                .help("Sets the epoch data")
                .required(true),
        )
        .get_matches();

    let key = matches.value_of("key").unwrap();
    let epoch_data_hex = matches.value_of("epoch-data").unwrap();
    let extra_data_hex = matches.value_of("extra-data").unwrap();
    let key_bytes = hex::decode(key).unwrap();
    let epoch_data = &hex::decode(epoch_data_hex).unwrap();
    let extra_data = &hex::decode(extra_data_hex).unwrap();

    let hasher = TryAndIncrement::<_, <Parameters as Bls12Parameters>::G1Parameters>::new(
        &*COMPOSITE_HASHER,
    );
    let priv_key = PrivateKey::deserialize(&mut &key_bytes[..]).unwrap();
    // let pk = priv_key.to_public();

    let epoch_data_inner_hash = COMPOSITE_HASHER.crh(b"ULforxof", epoch_data, 64).unwrap();
    println!("Inner hash {:?}", epoch_data_inner_hash);
    println!("Inner hash hex {}", hex::encode(epoch_data_inner_hash));
    let epoch_data_hash = hasher.hash(b"ULforxof", epoch_data, extra_data).unwrap();
    println!("Hashed to group {}", epoch_data_hash);

    println!("Sign that point {:?}", priv_key.sign_raw(&epoch_data_hash));
    println!("Sign that message {:?}", priv_key.sign(epoch_data, extra_data, &hasher));

    let sig = priv_key.sign(epoch_data, extra_data, &hasher).unwrap();
    let mut sig_bytes = vec![];
    sig.serialize(&mut sig_bytes);
    println!("Sig bytes {:?}", sig_bytes);
    println!("Sig {}", sig.as_ref());

    /*
    let mut pk_bytes = vec![];
    pk.serialize(&mut pk_bytes).unwrap();

    let pop = sk.sign_pop(&pk_bytes, try_and_increment).unwrap();
    let mut pop_bytes = vec![];
    pop.serialize(&mut pop_bytes).unwrap();

    pk.verify_pop(&pk_bytes, &pop, try_and_increment).unwrap();

    let pop_hex = hex::encode(&pop_bytes);
    println!("{}", pop_hex);
    */
}
