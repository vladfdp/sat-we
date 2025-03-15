use ark_bls12_381::Fr;
use ark_ec::pairing::Pairing;
use ark_ff::Field;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::rand::Rng;
use ark_std::Zero;
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce
};
use rand::RngCore;

use crate::cnf_sat::CNFFormula;
use crate::we_kzg::{
    create_proof, KZGCommitment,
    KZGStructuredReferenceString, CipherHint, witness_encrypt
};

#[derive(Clone, Debug)]
pub struct WELiteral<E:Pairing> {
    pub cipher_hint: CipherHint<E>, //The subkey and hint
    pub variable_index: usize,  // Which variable (x_k)
    pub is_negated: bool        // Whether it's negated (¬x_k)
}

#[derive(Clone,Debug)]
pub struct WEClause<E:Pairing>{
    literals: Vec<WELiteral<E>>
}

#[derive(Clone, Debug)]
pub struct WEHint<E:Pairing>{
    clauses: Vec<WEClause<E>>,
    num_variables: usize
}

/// Encrypt a message using AES-GCM with authenticated encryption
fn encrypt_aes(message: &[u8], key: &[u8; 32]) -> Vec<u8> {
    // Create cipher instance
    let cipher = Aes256Gcm::new_from_slice(key).expect("Invalid key length");
    
    // Create a random 96-bit nonce (12 bytes)
    let mut nonce_bytes = [0u8; 12];
    // Use rand crate for generating the nonce
    rand::thread_rng().fill_bytes(&mut nonce_bytes);
    let nonce = Nonce::from_slice(&nonce_bytes);
    
    // Encrypt the message
    let ciphertext = cipher.encrypt(nonce, message)
        .expect("Encryption failed");
    
    // Prepend nonce to ciphertext (so we can decrypt later)
    let mut result = Vec::with_capacity(nonce_bytes.len() + ciphertext.len());
    result.extend_from_slice(&nonce_bytes);
    result.extend_from_slice(&ciphertext);
    
    result
}

/// Decrypt a message using AES-GCM with authenticated encryption
pub fn decrypt_aes(ciphertext: &[u8], key: &[u8; 32]) -> Vec<u8> {
    // Need at least a nonce (12 bytes) and some ciphertext
    if ciphertext.len() <= 12 {
        panic!("Ciphertext is too short");
    }
    
    // Create cipher instance
    let cipher = Aes256Gcm::new_from_slice(key).expect("Invalid key length");
    
    // Extract nonce from the first 12 bytes
    let nonce = Nonce::from_slice(&ciphertext[..12]);
    
    // Decrypt the message (ciphertext without the nonce)
    cipher.decrypt(nonce, &ciphertext[12..]).expect("Decryption failed")
}

/// Helper function to create a polynomial from a boolean assignment using Lagrange interpolation
/// The polynomial p(x) is constructed such that p(i) = assignment[i]
/// 
/// # Arguments
/// * `assignment` - A slice of boolean values representing the variable assignment
/// 
/// # Returns
/// A polynomial that evaluates to 1 for true assignments and 0 for false assignments
pub fn create_polynomial_from_assignment(assignment: &[bool]) -> DensePolynomial<Fr> {
    // Create points for interpolation
    let mut points = Vec::with_capacity(assignment.len());
    
    for (i, &value) in assignment.iter().enumerate() {
        let x = Fr::from(i as u64);
        let y = if value { Fr::from(1u64) } else { Fr::from(0u64) };
        points.push((x, y));
    }
    
    // Perform Lagrange interpolation
    let mut result = DensePolynomial::<Fr>::zero();
    
    for (j, (x_j, y_j)) in points.iter().enumerate() {
        let mut term = DensePolynomial::from_coefficients_vec(vec![Fr::from(1u64)]);
        let mut denom = Fr::from(1u64);
        
        for (k, (x_k, _)) in points.iter().enumerate() {
            if j != k {
                // Compute (x - x_k)
                let factor = DensePolynomial::from_coefficients_vec(vec![
                    -*x_k,  // -x_k
                    Fr::from(1u64), // x
                ]);
                
                // Multiply term by (x - x_k)
                term = &term * &factor;
                
                // Update denominator with (x_j - x_k)
                denom *= *x_j - *x_k;
            }
        }
        
        // Scale by y_j / denom
        let scalar = *y_j / denom;
        // Multiply each coefficient by the scalar
        let scaled_coeffs = term.coeffs().iter().map(|c| *c * scalar).collect();
        term = DensePolynomial::from_coefficients_vec(scaled_coeffs);
        
        // Add to result
        result = result + term;
    }
    
    result
}

pub fn sat_encryption<'a, E:Pairing>(
    message: &'a [u8],
    formula: &CNFFormula,
    srs: &KZGStructuredReferenceString<E>,
    commitment: &KZGCommitment<E>,
    rng: &mut impl Rng
) -> (Vec<u8>, WEHint<E>) {
    // Generate a random key for each clause
    let mut master_key = [0u8; 32];
    //let mut clause_keys = Vec::new();

    let mut we_hint = WEHint { clauses: Vec::new(), num_variables: formula.num_variables };
    
    // For each clause, generate a random key and XOR it into the master key
    for i in 0..formula.clauses.len() {
        let clause = &formula.clauses[i];
        let mut clause_key = [0u8; 32];
        rng.fill_bytes(&mut clause_key);
        
        // XOR this key into the master key
        for i in 0..32 {
            master_key[i] ^= clause_key[i];
        }
        
        //clause_keys.push(clause_key);

        let mut clause_hint = WEClause { literals: Vec::new() };
        for j in 0..clause.literals.len() {
            let literal = &clause.literals[j];

            let cipher_hint = if literal.is_negated {
                witness_encrypt(
                    &clause_key,
                    &srs, 
                    &commitment, 
                    &E::ScalarField::from(literal.variable_index as u64), 
                    &E::ScalarField::ZERO, 
                    rng
                )
            } else {
                witness_encrypt(
                    &clause_key,
                    &srs, 
                    &commitment, 
                    &E::ScalarField::from(literal.variable_index as u64), 
                    &E::ScalarField::ONE, 
                    rng
                )
            };

            clause_hint.literals.push(WELiteral {
                cipher_hint,
                variable_index: literal.variable_index,
                is_negated: literal.is_negated
            });
        }
        
        we_hint.clauses.push(clause_hint);
    }
    
    // Encrypt the message with the master key using AES-GCM
    let encrypted_message = encrypt_aes(message, &master_key);
    
    (encrypted_message, we_hint)
}

pub fn sat_decryption<'a, E:Pairing>(
    ciphertext: &'a [u8],
    hint: &WEHint<E>,
    polynomial: &DensePolynomial<E::ScalarField>,
    srs: &KZGStructuredReferenceString<E>
) -> Vec<u8> {
    // Initialize master key (all zeros)
    let mut master_key = [0u8; 32];
    
    // For each clause in the hint
    for clause in &hint.clauses {
        let mut clause_satisfied = false;
        let mut recovered_clause_key: Option<[u8; 32]> = None;
        
        // Try to decrypt using any satisfied literal in the clause
        for literal in &clause.literals {
            // Get the variable assignment from the polynomial
            let point = E::ScalarField::from(literal.variable_index as u64);
            let eval = polynomial.evaluate(&point);
            
            // Check if the literal is satisfied
            let literal_satisfied = if literal.is_negated {
                eval == E::ScalarField::ZERO
            } else {
                eval == E::ScalarField::ONE
            };
            
            if literal_satisfied {
                // Create proof for this point
                let proof = create_proof(srs, polynomial, &point, &eval);
                
                // Try to decrypt the clause key with the proof
                // Since we're using panic-based error handling now, just call the function directly
                // If it panics, the entire decryption will fail, which is the desired behavior
                let clause_key = crate::we_kzg::witness_decrypt(&literal.cipher_hint, &proof.proof);
                recovered_clause_key = Some(clause_key);
                clause_satisfied = true;
                break; // We only need one satisfied literal per clause
            }
        }
        
        // If the clause is satisfied, XOR the recovered key into the master key
        if clause_satisfied {
            if let Some(clause_key) = recovered_clause_key {
                // XOR this key into the master key
                for i in 0..32 {
                    master_key[i] ^= clause_key[i];
                }
            }
        } else {
            // If any clause is not satisfied, we can't decrypt the message
            panic!("Cannot decrypt - formula not satisfied by the provided assignment");
        }
    }
    
    // Decrypt the message with the master key using AES-GCM
    decrypt_aes(ciphertext, &master_key)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;
    use crate::we_kzg::{commit, setup};
    use ark_ff::Zero;
    use ark_std::test_rng;
    use crate::cnf_sat::{CNFFormula, Clause, Literal};

    #[test]
    fn test_polynomial_creation() {
        // Test with a simple assignment
        let assignment = vec![true, false, true];
        let polynomial = create_polynomial_from_assignment(&assignment);
        
        // Check if the polynomial evaluates correctly at the assignment points
        for (i, &value) in assignment.iter().enumerate() {
            let point = Fr::from(i as u64);
            let eval = polynomial.evaluate(&point);
            let expected = if value { Fr::from(1u64) } else { Fr::from(0u64) };
            assert_eq!(eval, expected, "Polynomial evaluation should match assignment at point {}", i);
        }
        
        // Test interpolation works even for larger assignments
        let large_assignment = vec![true, false, true, false, true, false, true, false, true, false];
        let large_poly = create_polynomial_from_assignment(&large_assignment);
        
        for (i, &value) in large_assignment.iter().enumerate() {
            let point = Fr::from(i as u64);
            let eval = large_poly.evaluate(&point);
            let expected = if value { Fr::from(1u64) } else { Fr::from(0u64) };
            assert_eq!(eval, expected, "Large polynomial evaluation should match assignment at point {}", i);
        }
        
        // Test with empty assignment
        let empty_assignment: Vec<bool> = vec![];
        let empty_poly = create_polynomial_from_assignment(&empty_assignment);
        assert_eq!(empty_poly, DensePolynomial::<Fr>::zero(), "Empty assignment should create zero polynomial");
        
        // Test with single value assignment
        let single_assignment = vec![true];
        let single_poly = create_polynomial_from_assignment(&single_assignment);
        assert_eq!(single_poly.evaluate(&Fr::from(0u64)), Fr::from(1u64), 
                   "Single value polynomial should evaluate to the correct value");
    }

    #[test]
    fn test_encrypt_decrypt_aes() {
        let test_message = b"This is a test message";
        let key = [0x41u8; 32];
        
        let ciphertext = encrypt_aes(test_message, &key);
        let decrypted = decrypt_aes(&ciphertext, &key);
        
        assert_eq!(test_message, decrypted.as_slice(), "Decrypted message should match original");
    }

    #[test]
    fn test_simple_sat_encryption() {
        let mut rng = test_rng();
        
        // Create a very simple CNF formula: (x₀)
        let formula = CNFFormula::new(
            vec![
                Clause::new(vec![
                    Literal::new_positive(0),
                ]),
            ],
            1
        );
        
        // Create a satisfying assignment
        let assignment = vec![true]; // x₀=true
        
        // Verify the assignment satisfies the formula
        assert!(formula.evaluate(&assignment), "Assignment should satisfy the formula");
        
        // Create a polynomial that encodes this assignment
        let polynomial = create_polynomial_from_assignment(&assignment);
        
        // Setup KZG and commit to the polynomial
        let max_degree = 10;
        let srs = setup::<Bls12_381, _>(max_degree, &mut rng);
        let commitment = commit(&srs, &polynomial);
        
        // Create a test message
        let test_message = b"This is a test message!";
        
        // Encrypt the message using sat_encryption
        let (ciphertext, hint) = sat_encryption::<Bls12_381>(
            test_message,
            &formula,
            &srs,
            &commitment,
            &mut rng
        );
        
        // Decrypt the message using sat_decryption
        let decrypted_message = sat_decryption::<Bls12_381>(
            &ciphertext,
            &hint,
            &polynomial,
            &srs
        );
        
        // Verify the decrypted message matches the original
        assert_eq!(test_message, decrypted_message.as_slice(), 
            "Decrypted message should match the original message");
    }

    #[test]
    fn test_sat_encryption_with_multiple_clauses() {
        let mut rng = test_rng();
        
        // Create a CNF formula: (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂)
        let formula = CNFFormula::new(
            vec![
                Clause::new(vec![
                    Literal::new_positive(0),
                    Literal::new_positive(1),
                ]),
                Clause::new(vec![
                    Literal::new_negative(0),
                    Literal::new_positive(2),
                ]),
            ],
            3
        );
        
        // Create a satisfying assignment
        let assignment = vec![true, false, true]; // x₀=true, x₁=false, x₂=true
        
        // Verify the assignment satisfies the formula
        assert!(formula.evaluate(&assignment), "Assignment should satisfy the formula");
        
        // Create a polynomial that encodes this assignment
        let polynomial = create_polynomial_from_assignment(&assignment);
        
        // Setup KZG and commit to the polynomial
        let max_degree = 10;
        let srs = setup::<Bls12_381, _>(max_degree, &mut rng);
        let commitment = commit(&srs, &polynomial);
        
        // Create a test message
        let test_message = b"This is a test message for multiple clauses!";
        
        // Encrypt the message using sat_encryption
        let (ciphertext, hint) = sat_encryption::<Bls12_381>(
            test_message,
            &formula,
            &srs,
            &commitment,
            &mut rng
        );
        
        // Decrypt the message using sat_decryption
        let decrypted_message = sat_decryption::<Bls12_381>(
            &ciphertext,
            &hint,
            &polynomial,
            &srs
        );
        
        // Verify the decrypted message matches the original
        assert_eq!(test_message, decrypted_message.as_slice(), 
            "Decrypted message should match the original message");
    }

    #[test]
    fn test_sat_encryption_with_unsatisfiable_assignment() {
        let mut rng = test_rng();
        
        // Create a CNF formula: (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂)
        let formula = CNFFormula::new(
            vec![
                Clause::new(vec![
                    Literal::new_positive(0),
                    Literal::new_positive(1),
                ]),
                Clause::new(vec![
                    Literal::new_negative(0),
                    Literal::new_positive(2),
                ]),
            ],
            3
        );
        
        // Create a NON-satisfying assignment
        // x₀=true, x₁=false, x₂=false fails because (¬x₀ ∨ x₂) is false
        let assignment = vec![true, false, false];
        
        // Verify the assignment does NOT satisfy the formula
        assert!(!formula.evaluate(&assignment), "Assignment should NOT satisfy the formula");
        
        // Create a polynomial that encodes this assignment
        let polynomial = create_polynomial_from_assignment(&assignment);
        
        // Setup KZG and commit to the polynomial
        let max_degree = 10;
        let srs = setup::<Bls12_381, _>(max_degree, &mut rng);
        let commitment = commit(&srs, &polynomial);
        
        // Create a test message
        let test_message = b"This message should not be decryptable!";
        
        // Encrypt the message using sat_encryption
        let (ciphertext, hint) = sat_encryption::<Bls12_381>(
            test_message,
            &formula,
            &srs,
            &commitment,
            &mut rng
        );
        
        // Attempt to decrypt with the non-satisfying assignment
        // This should panic, so we use std::panic::catch_unwind to verify it
        let decryption_result = std::panic::catch_unwind(|| {
            sat_decryption::<Bls12_381>(
                &ciphertext,
                &hint,
                &polynomial,
                &srs
            )
        });
        
        // Verify decryption fails with panic
        assert!(decryption_result.is_err(), 
            "Decryption should panic with a non-satisfying assignment");
    }

    #[test]
    fn test_sat_encryption_comprehensive() {
        let mut rng = test_rng();
        
        // Create a more complex CNF formula
        // (x₀ ∨ x₁ ∨ x₂) ∧ (¬x₀ ∨ ¬x₁) ∧ (¬x₁ ∨ x₃) ∧ (x₂ ∨ x₃ ∨ ¬x₄)
        let formula = CNFFormula::new(
            vec![
                Clause::new(vec![
                    Literal::new_positive(0),
                    Literal::new_positive(1),
                    Literal::new_positive(2),
                ]),
                Clause::new(vec![
                    Literal::new_negative(0),
                    Literal::new_negative(1),
                ]),
                Clause::new(vec![
                    Literal::new_negative(1),
                    Literal::new_positive(3),
                ]),
                Clause::new(vec![
                    Literal::new_positive(2),
                    Literal::new_positive(3),
                    Literal::new_negative(4),
                ]),
            ],
            5
        );
        
        // Create a satisfying assignment
        // x₀=false, x₁=false, x₂=true, x₃=true, x₄=true
        let assignment = vec![false, false, true, true, true];
        
        // Verify the assignment satisfies the formula
        assert!(formula.evaluate(&assignment), "Assignment should satisfy the formula");
        
        // Create a polynomial that encodes this assignment
        let polynomial = create_polynomial_from_assignment(&assignment);
        
        // Setup KZG and commit to the polynomial
        let max_degree = 10;
        let srs = setup::<Bls12_381, _>(max_degree, &mut rng);
        let commitment = commit(&srs, &polynomial);
        
        // Create a larger test message
        let test_message = b"This is a comprehensive test of the SAT encryption scheme.";
        
        // Encrypt the message
        let (ciphertext, hint) = sat_encryption::<Bls12_381>(
            test_message,
            &formula,
            &srs,
            &commitment,
            &mut rng
        );
        
        // Decrypt the message
        let decrypted_message = sat_decryption::<Bls12_381>(
            &ciphertext,
            &hint,
            &polynomial,
            &srs
        );
        
        // Verify the decrypted message matches the original
        assert_eq!(test_message, decrypted_message.as_slice(), 
            "Decrypted message should match the original message");
    }
} 