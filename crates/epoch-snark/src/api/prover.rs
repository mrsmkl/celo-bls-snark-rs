use super::{setup::Parameters, BLSCurve, BLSCurveG1, BLSCurveG2, CPCurve};
use crate::{
    epoch_block::{EpochBlock, EpochTransition},
    gadgets::{EpochData, HashToBits, HashToBitsHelper, SingleUpdate, ValidatorSetUpdate},
};
use algebra::ProjectiveCurve;
use bls_crypto::{
    hash_to_curve::try_and_increment::COMPOSITE_HASH_TO_G1,
    hashers::{Hasher, COMPOSITE_HASHER},
    Signature, SIG_DOMAIN,
};
use bls_gadgets::utils::bytes_to_bits;

use groth16::{create_proof_no_zk, Parameters as Groth16Parameters, Proof as Groth16Proof};
use r1cs_core::SynthesisError;

use tracing::{info, span, Level};

/// Given the SNARK's Public Parameters, the initial epoch, and a list of state transitions,
/// generates a SNARK which proves that the final epoch is correctly calculated from the first
/// epoch. The proof can then be verified only with constant amount of data (the first and last
/// epochs)
pub fn prove(
    parameters: &Parameters<CPCurve, BLSCurve>,
    num_validators: u32,
    initial_epoch: &EpochBlock,
    transitions: &[EpochTransition],
    max_transitions: usize,
) -> Result<Groth16Proof<CPCurve>, SynthesisError> {
    info!(
        "Generating proof for {} epochs (first epoch: {}, {} validators per epoch)",
        transitions.len(),
        initial_epoch.index,
        num_validators,
    );

    let span = span!(Level::TRACE, "prove");
    let _enter = span.enter();

    let mut epochs = transitions
        .iter()
        .map(|transition| to_update(transition))
        .collect::<Vec<_>>();

    let num_epochs = epochs.len();
    if num_epochs < max_transitions {
        epochs = [
            &epochs[..num_epochs - 1],
            &(0..max_transitions - num_epochs)
                .map(|_| to_dummy_update(num_validators))
                .collect::<Vec<_>>(),
            &[epochs[num_epochs - 1].clone()],
        ]
        .concat();
    }

    // Generate a helping proof if a Proving Key for the HashToBits
    // circuit was provided
    let hash_helper = if let Some(ref params) = parameters.hash_to_bits {
        Some(generate_hash_helper(&params, transitions)?)
    } else {
        None
    };

    // Generate the BLS proof
    let asig = Signature::aggregate(transitions.iter().map(|epoch| &epoch.aggregate_signature));
    let mut asig_dummy = (0..max_transitions - num_epochs)
        .map(|_| Signature::from(BLSCurveG1::prime_subgroup_generator()))
        .collect::<Vec<_>>();
    asig_dummy.push(asig);
    let asig = Signature::aggregate(&asig_dummy);

    let circuit = ValidatorSetUpdate::<BLSCurve> {
        initial_epoch: to_epoch_data(initial_epoch),
        epochs,
        aggregated_signature: Some(*asig.as_ref()),
        num_validators,
        hash_helper,
    };
    info!("BLS");
    let bls_proof = create_proof_no_zk(circuit, &parameters.epochs)?;

    Ok(bls_proof)
}

/// Helper which creates the hashproof inside BLS12-377
fn generate_hash_helper(
    params: &Groth16Parameters<BLSCurve>,
    transitions: &[EpochTransition],
) -> Result<HashToBitsHelper<BLSCurve>, SynthesisError> {
    let hash_to_g1 = &COMPOSITE_HASH_TO_G1;
    let composite_hasher = &COMPOSITE_HASHER;

    // Generate the CRH per epoch
    let message_bits = transitions
        .iter()
        .map(|transition| {
            let block = &transition.block;
            let epoch_bytes = block.encode_to_bytes().unwrap();

            // We need to find the counter so that the CRH hash we use will eventually result on an element on the curve
            let (_, counter) = hash_to_g1
                .hash_with_attempt(SIG_DOMAIN, &epoch_bytes, &[])
                .unwrap();
            let crh_bytes = composite_hasher
                .crh(&[], &[&[counter as u8][..], &epoch_bytes].concat(), 0)
                .unwrap();
            // The verifier should run both the crh and the xof here to generate a
            // valid statement for the verify
            bytes_to_bits(&crh_bytes, 384)
                .iter()
                .map(|b| Some(*b))
                .collect()
        })
        .collect::<Vec<_>>();

    // Generate proof of correct calculation of the CRH->Blake hashes
    // to make Hash to G1 cheaper
    let circuit = HashToBits { message_bits };
    info!("CRH->XOF");
    let hash_proof = create_proof_no_zk(circuit, params)?;

    Ok(HashToBitsHelper {
        proof: hash_proof,
        verifying_key: params.vk.clone(),
    })
}

fn to_epoch_data(block: &EpochBlock) -> EpochData<BLSCurve> {
    EpochData {
        index: Some(block.index),
        maximum_non_signers: block.maximum_non_signers,
        public_keys: block
            .new_public_keys
            .iter()
            .map(|pubkey| Some(*pubkey.as_ref()))
            .collect(),
    }
}

fn to_update(transition: &EpochTransition) -> SingleUpdate<BLSCurve> {
    SingleUpdate {
        epoch_data: to_epoch_data(&transition.block),
        signed_bitmap: transition
            .bitmap
            .iter()
            .map(|b| Some(*b))
            .collect::<Vec<_>>(),
    }
}

fn to_dummy_update(num_validators: u32) -> SingleUpdate<BLSCurve> {
    SingleUpdate {
        epoch_data: EpochData {
            maximum_non_signers: 0,
            index: Some(0),
            public_keys: (0..num_validators)
                .map(|_| Some(BLSCurveG2::prime_subgroup_generator()))
                .collect::<Vec<_>>(),
        },
        signed_bitmap: (0..num_validators).map(|_| Some(true)).collect::<Vec<_>>(),
    }
}
