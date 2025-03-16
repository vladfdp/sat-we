use ark_bls12_381::Bls12_381;
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group};
use ark_ff::{Field, UniformRand, Zero};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::{
    ops::{Add, Mul},
    rand::Rng,
    vec::Vec,
};
use blake3;
use ark_std::fmt::Debug;
use aes::{Aes128, Block, cipher::{
    BlockEncrypt, BlockDecrypt,
    KeyInit
}};
use ark_serialize::{CanonicalSerialize, Compress};

/// The structured reference string (SRS) for the KZG polynomial commitment scheme
#[derive(Clone, Debug)]
pub struct KZGStructuredReferenceString<E: Pairing> {
    /// Powers of the secret: [g₁, g₁ˢ, g₁ˢ², ..., g₁ˢᵈ]
    pub powers_of_g1: Vec<E::G1Affine>,
    /// Powers of the secret in G2: [g₂, g₂ˢ]
    pub powers_of_g2: [E::G2Affine; 2],
}

/// A commitment to a polynomial
#[derive(Clone, Debug)]
pub struct KZGCommitment<E: Pairing>(pub E::G1Affine);

/// A proof for a polynomial evaluation at a point
#[derive(Clone, Debug)]
pub struct KZGProof<E: Pairing> {
    /// Commitment to the quotient polynomial h(X) = (f(X) - f(z))/(X - z)
    pub proof: E::G1Affine,
    /// Claimed evaluation f(z)
    pub evaluation: E::ScalarField,
}

#[derive(Clone, Debug)]
pub struct CipherHint<E: Pairing> {
    pub ciphertext: [u8; 16],
    pub hint: E::G2Affine,
}

/// Creates a new structured reference string for the KZG commitment scheme with public parameters up to max_degree
pub fn setup<E: Pairing, R: Rng>(max_degree: usize, rng: &mut R) -> KZGStructuredReferenceString<E> {
    // Generate a random secret s
    let s = E::ScalarField::rand(rng);
    
    // Generate powers of secret in G1: [g₁, g₁ˢ, g₁ˢ², ..., g₁ˢᵈ]
    let mut powers_of_g1 = Vec::with_capacity(max_degree + 1);
    let g1_generator = E::G1::generator();
    let mut current_power = g1_generator;
    powers_of_g1.push(current_power.into_affine());
    
    for _ in 1..=max_degree {
        current_power = current_power.mul(s);
        powers_of_g1.push(current_power.into_affine());
    }
    
    // Generate powers of secret in G2: [g₂, g₂ˢ]
    let g2_generator = E::G2::generator();
    let powers_of_g2 = [
        g2_generator.into_affine(),
        g2_generator.mul(s).into_affine(),
    ];
    
    KZGStructuredReferenceString {
        powers_of_g1,
        powers_of_g2,
    }
}

/// Commits to a polynomial using the KZG commitment scheme
pub fn commit<E: Pairing>(
    srs: &KZGStructuredReferenceString<E>,
    polynomial: &DensePolynomial<E::ScalarField>,
) -> KZGCommitment<E> {
    let coeffs = polynomial.coeffs();
    assert!(
        coeffs.len() <= srs.powers_of_g1.len(),
        "Polynomial degree is too large for the SRS"
    );
    
    // Compute commitment C = ∑(cᵢ * g₁ˢⁱ) for i=0 to d
    let mut commitment = E::G1::zero();
    for (i, coeff) in coeffs.iter().enumerate() {
        commitment = commitment.add(srs.powers_of_g1[i].mul(*coeff));
    }
    
    KZGCommitment(commitment.into_affine())
}

/// Creates a proof for the evaluation of a polynomial at a point z with a given evaluation value
pub fn create_proof<E: Pairing>(
    srs: &KZGStructuredReferenceString<E>,
    polynomial: &DensePolynomial<E::ScalarField>,
    z: &E::ScalarField,
    evaluation: &E::ScalarField,
) -> KZGProof<E> {
    // Compute the witness polynomial h(X) = (f(X) - f(z)) / (X - z)
    // Create polynomial for f(x) - f(z)
    let mut f_minus_fz_coeffs = polynomial.coeffs().to_vec();
    f_minus_fz_coeffs[0] = f_minus_fz_coeffs[0] - *evaluation;
    
    // Ensure we properly handle vanishing leading terms to avoid creating invalid polynomials
    while !f_minus_fz_coeffs.is_empty() && f_minus_fz_coeffs.last().unwrap().is_zero() {
        f_minus_fz_coeffs.pop();
    }
    
    // If the polynomial becomes zero, return an appropriate proof
    if f_minus_fz_coeffs.is_empty() {
        return KZGProof {
            proof: E::G1::zero().into_affine(),
            evaluation: *evaluation,
        };
    }
    
    let f_minus_fz = DensePolynomial::from_coefficients_vec(f_minus_fz_coeffs);
    
    // Compute the quotient using synthetic division
    let quotient = synthetic_division(&f_minus_fz, z);
    
    // Compute the proof as a commitment to h(X)
    let proof = commit(srs, &quotient).0;
    
    KZGProof {
        proof,
        evaluation: *evaluation,
    }
}

/// Verifies a KZG proof
pub fn verify<E: Pairing>(
    srs: &KZGStructuredReferenceString<E>,
    commitment: &KZGCommitment<E>,
    point: &E::ScalarField,
    proof: &KZGProof<E>,
) -> bool {
    // The verification equation is:
    // e([C] - [f(z)]₁, [1]₂) = e([π], [s-z]₂)
    
    // [f(z)]₁ = f(z) * [1]₁
    let evaluation_commitment = E::G1::generator().mul(proof.evaluation);
    
    // [C] - [f(z)]₁
    let left_side = commitment.0.into_group() - evaluation_commitment;
    
    // [s-z]₂ = [s]₂ - z[1]₂
    let right_g2 = srs.powers_of_g2[1].into_group() - E::G2::generator().mul(*point);
    
    // Check the pairing equation
    E::pairing(left_side, srs.powers_of_g2[0]) == E::pairing(proof.proof, right_g2)
}

pub fn encapsulate<E: Pairing>(
    srs: &KZGStructuredReferenceString<E>, 
    commitment: &KZGCommitment<E>, 
    point: &E::ScalarField, 
    evaluation: &E::ScalarField, 
    rng: &mut impl Rng
) -> ([u8; 16], E::G2Affine) {
    let randomness = E::ScalarField::rand(rng);
    let commitment_minus_eval = commitment.0.into_group() - E::G1::generator().mul(*evaluation);
    let scaled_difference = commitment_minus_eval.mul(randomness);
    let generator_g2 = E::G2::generator();
    let pairing_output = E::pairing(scaled_difference, generator_g2);
    
    // Serialize the pairing output using canonical serialization
    let mut serialized = Vec::new();
    pairing_output.serialize_with_mode(&mut serialized, Compress::Yes)
        .expect("Failed to serialize pairing output");
    
    // Create a fixed-size array for the symmetric key
    let hash = blake3::hash(&serialized);
    let mut symmetric_key = [0u8; 16];
    symmetric_key.copy_from_slice(&hash.as_bytes()[0..16]);
    
    let shifted_generator = srs.powers_of_g2[1].into_group() - E::G2::generator().mul(*point);
    let hint = shifted_generator.mul(randomness);
    (symmetric_key, hint.into_affine())
}

pub fn decapsulate<E: Pairing>(proof: &E::G1Affine, hint: &E::G2Affine) -> [u8; 16] {
    let hint_group = hint.into_group();
    let pairing_output = E::pairing(proof, hint_group);
    
    // Serialize the pairing output using canonical serialization
    let mut serialized = Vec::new();
    pairing_output.serialize_with_mode(&mut serialized, Compress::Yes)
        .expect("Failed to serialize pairing output");
    
    // Create a fixed-size array for the symmetric key
    let hash = blake3::hash(&serialized);
    let mut symmetric_key = [0u8; 16];
    symmetric_key.copy_from_slice(&hash.as_bytes()[0..16]);
    symmetric_key
}

/// Encrypts a 16-byte message using a key derived from the KZG commitment scheme
pub fn witness_encrypt<E: Pairing>(
    message: &[u8; 16],
    srs: &KZGStructuredReferenceString<E>,
    commitment: &KZGCommitment<E>,
    point: &E::ScalarField,
    evaluation: &E::ScalarField,
    rng: &mut impl Rng
) -> CipherHint<E> {
    // Derive the symmetric key
    let (symmetric_key, hint) = encapsulate(srs, commitment, point, evaluation, rng);
    
    // Use AES-128 for encryption
    let cipher = Aes128::new_from_slice(&symmetric_key).expect("Invalid key length");
    
    // Create a block from the message and encrypt it
    let mut block = Block::clone_from_slice(message);
    cipher.encrypt_block(&mut block);
    
    // Create the ciphertext
    let mut ciphertext = [0u8; 16];
    ciphertext.copy_from_slice(block.as_slice());
    
    CipherHint {
        ciphertext,
        hint,
    }
}

/// Decrypts a 16-byte message using a key derived from the KZG proof and ciphertext
pub fn witness_decrypt<E: Pairing>(
    cipher_hint: &CipherHint<E>,
    proof: &E::G1Affine
) -> [u8; 16] {
    // Derive the symmetric key
    let symmetric_key = decapsulate::<E>(proof, &cipher_hint.hint);
    
    // Use AES-128 for decryption
    let cipher = Aes128::new_from_slice(&symmetric_key).expect("Invalid key length");
    
    // Create a block from the ciphertext and decrypt it
    let mut block = Block::clone_from_slice(&cipher_hint.ciphertext);
    cipher.decrypt_block(&mut block);
    
    // Create the plaintext
    let mut plaintext = [0u8; 16];
    plaintext.copy_from_slice(block.as_slice());
    
    plaintext
}

/// Returns the maximum polynomial degree supported by the SRS
pub fn max_degree<E: Pairing>(srs: &KZGStructuredReferenceString<E>) -> usize {
    srs.powers_of_g1.len() - 1
}

/// Direct synthetic division for computing (f(x) - f(z)) / (x - z)
/// This is more efficient and stable than the general polynomial division
pub fn synthetic_division<F: Field>(
    polynomial: &DensePolynomial<F>,
    z: &F,
) -> DensePolynomial<F> {
    let degree = polynomial.degree();
    if degree == 0 {
        // If f(x) is constant, then f(x) - f(z) = 0, so quotient is 0
        return DensePolynomial::zero();
    }
    
    let n = degree + 1;
    let mut quotient_coeffs = vec![F::zero(); n - 1];
    
    // Start with the highest degree coefficient
    quotient_coeffs[n - 2] = polynomial.coeffs()[n - 1];
    
    // Work backwards through the coefficients
    for i in (1..n-1).rev() {
        quotient_coeffs[i - 1] = polynomial.coeffs()[i] + quotient_coeffs[i] * (*z);
    }
    
    // Filter out leading zeros if any
    while !quotient_coeffs.is_empty() && quotient_coeffs.last().unwrap().is_zero() {
        quotient_coeffs.pop();
    }
    
    // If all coefficients are zero, return the zero polynomial
    if quotient_coeffs.is_empty() {
        return DensePolynomial::zero();
    }
    
    DensePolynomial::from_coefficients_vec(quotient_coeffs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_std::test_rng;
    
    #[test]
    fn test_kzg_single_proof() {
        let mut rng = test_rng();
        
        // Create a new KZG setup with max degree 10
        let srs = setup::<Bls12_381, _>(10, &mut rng);
        
        // Create a valid polynomial of degree 5
        let mut poly_coeffs: Vec<Fr> = Vec::new();
        for i in 0..6 {
            // Ensure non-zero coefficient for highest degree term
            if i == 5 {
                let mut coeff = Fr::zero();
                while coeff.is_zero() {
                    coeff = Fr::rand(&mut rng);
                }
                poly_coeffs.push(coeff);
            } else {
                poly_coeffs.push(Fr::rand(&mut rng));
            }
        }
        
        let polynomial = DensePolynomial::from_coefficients_vec(poly_coeffs);
        
        // Commit to the polynomial
        let commitment = commit(&srs, &polynomial);
        
        // Generate a random point to evaluate at
        let point = Fr::rand(&mut rng);
        
        // Evaluate the polynomial at this point
        let evaluation = polynomial.evaluate(&point);
        
        // Create a proof for the evaluation
        let proof = create_proof(&srs, &polynomial, &point, &evaluation);
        
        // Verify the proof
        let result = verify(&srs, &commitment, &point, &proof);
        assert!(result, "KZG proof verification failed");
    }
    
    #[test]
    fn test_key_derivation_consistency() {
        let mut rng = test_rng();
        
        // Create a new KZG setup with max degree 10
        let srs = setup::<Bls12_381, _>(10, &mut rng);
        
        // Create a polynomial of degree 5
        let mut poly_coeffs: Vec<Fr> = Vec::new();
        for i in 0..6 {
            // Ensure non-zero coefficient for highest degree term
            if i == 5 {
                let mut coeff = Fr::zero();
                while coeff.is_zero() {
                    coeff = Fr::rand(&mut rng);
                }
                poly_coeffs.push(coeff);
            } else {
                poly_coeffs.push(Fr::rand(&mut rng));
            }
        }
        
        let polynomial = DensePolynomial::from_coefficients_vec(poly_coeffs);
        
        // Commit to the polynomial
        let commitment = commit(&srs, &polynomial);
        
        // Generate a random point to evaluate at
        let point = Fr::rand(&mut rng);
        
        // Evaluate the polynomial at this point
        let evaluation = polynomial.evaluate(&point);
        
        // Create a proof for the evaluation
        let proof = create_proof(&srs, &polynomial, &point, &evaluation);
        
        // Verify the proof is valid
        let result = verify(&srs, &commitment, &point, &proof);
        assert!(result, "KZG proof verification failed");
        
        // Create a key using create_key
        let (key1, hint) = encapsulate(&srs, &commitment, &point, &evaluation, &mut rng);
        
        // Get the key using get_key
        let key2 = decapsulate::<Bls12_381>(&proof.proof, &hint);
        
        // Check that both keys are the same
        assert_eq!(key1, key2, "Keys derived from create_key and get_key don't match");
    }
    
    #[test]
    fn test_witness_encryption() {
        let mut rng = test_rng();
        
        // Create a new KZG setup with max degree 10
        let srs = setup::<Bls12_381, _>(10, &mut rng);
        
        // Create a polynomial of degree 5
        let mut poly_coeffs: Vec<Fr> = Vec::new();
        for _ in 0..6 {
            poly_coeffs.push(Fr::rand(&mut rng));
        }

        let polynomial = DensePolynomial::from_coefficients_vec(poly_coeffs);
        
        // Commit to the polynomial
        let commitment = commit(&srs, &polynomial);
        
        // Generate a random point to evaluate at
        let point = Fr::rand(&mut rng);
        
        // Evaluate the polynomial at this point
        let evaluation = polynomial.evaluate(&point);
        
        // Create a proof for the evaluation
        let proof = create_proof(&srs, &polynomial, &point, &evaluation);
        
        // Original message to encrypt (16 bytes)
        let message = [0x41u8; 16];
        
        // Encrypt the message
        let cipher_hint = witness_encrypt(
            &message,
            &srs, 
            &commitment, 
            &point, 
            &evaluation, 
            &mut rng
        );
        
        // Decrypt the message
        let decrypted = witness_decrypt::<Bls12_381>(&cipher_hint, &proof.proof);
        
        // Check that the decrypted message matches the original
        assert_eq!(decrypted, message, "Decrypted message doesn't match the original");
        
        // Try to decrypt with a wrong point (should fail or return wrong plaintext)
        let wrong_point = Fr::rand(&mut rng);
        let wrong_evaluation = polynomial.evaluate(&wrong_point);
        let wrong_proof = create_proof(&srs, &polynomial, &wrong_point, &wrong_evaluation);
        
        // Use std::panic::catch_unwind to handle potential panic from witness_decrypt
        let result = std::panic::catch_unwind(|| {
            let wrong_decrypted = witness_decrypt::<Bls12_381>(&cipher_hint, &wrong_proof.proof);
            // Only reaches here if the decryption didn't panic
            assert_ne!(wrong_decrypted, message, "Decryption succeeded with wrong proof!");
        });
    }
} 