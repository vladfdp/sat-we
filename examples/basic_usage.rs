use ark_bls12_381::{Bls12_381, Fr};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::rand::{rngs::StdRng, SeedableRng};
use sat_we::{
    cnf_sat::{CNFFormula, Clause, Literal},
    sat_encryption::{create_polynomial_from_assignment, sat_encryption, sat_decryption},
    we_kzg::{setup, commit},
};

fn main() {
    // This example demonstrates the full workflow of SAT-based witness encryption using
    // KZG polynomial commitments. We'll first choose a number, convert it to a bit vector,
    // transform it into a polynomial, and commit to it. Then we'll use the commitment
    // and a SAT formula to encrypt a message. Finally, we'll decrypt the message using
    // the original polynomial as our witness. This showcases how we can encrypt messages
    // that can only be decrypted by someone who knows a witness satisfying a condition,
    // in this case, knowing a number less than 50.

    let mut rng = StdRng::from_entropy();

    // =============================================================================
    // PART 1: Create a polynomial commitment from a number
    // =============================================================================
    println!("PART 1: Creating a polynomial commitment from a number");
    
    // Choose a number (41) that is less than 50
    let number = 41;
    println!("Chosen number: {}", number);
    
    // Convert number to bit vector (6 bits is enough for numbers up to 63)
    let bit_length = 6;
    let bits = int_to_bits_be(number, bit_length);
    println!("Bit representation: {:?}", bits);
    
    // Create a polynomial from the bit representation
    let polynomial = create_polynomial_from_assignment(&bits);
    println!("Created polynomial of degree {}", polynomial.degree());
    
    // Setup the KZG commitment scheme
    let srs = setup::<Bls12_381, _>(bit_length, &mut rng);
    
    // Commit to the polynomial
    let commitment = commit(&srs, &polynomial);
    println!("Created commitment to the polynomial");

    // =============================================================================
    // PART 2: SAT Encryption
    // =============================================================================
    println!("\nPART 2: SAT Encryption");
    
    // Create a formula that checks if a number is less than 50
    let formula = create_less_than_50_formula();
    println!("Created formula with {} variables and {} clauses", 
             formula.num_variables, formula.clauses.len());
    
    // Message to encrypt
    let message = b"This is a secret message that can only be decrypted if you know a number less than 50!";
    println!("Original message: {}", String::from_utf8_lossy(message));
    
    // Encrypt the message using the formula and commitment
    let (ciphertext, hint) = sat_encryption(
        message,
        &formula,
        &srs,
        &commitment,
        &mut rng
    );
    println!("Encrypted message ({} bytes) and generated hint", ciphertext.len());

    // =============================================================================
    // PART 3: SAT Decryption
    // =============================================================================
    println!("\nPART 3: SAT Decryption");
    
    // Decrypt the message using the witness (our polynomial)
    let decrypted = sat_decryption(
        &ciphertext,
        &hint,
        &polynomial,
        &srs
    );
    
    println!("Decrypted message: {}", String::from_utf8_lossy(&decrypted));
    println!("Decryption successful: {}", message == &decrypted[..]);
} 

/// Converts an integer to a vector of booleans in big-endian format (most significant bit first)
/// 
/// # Arguments
/// * `n` - The integer to convert
/// * `bit_length` - The number of bits to use in the representation
/// 
/// # Returns
/// A vector of booleans where each element represents a bit (true = 1, false = 0)
fn int_to_bits_be(n: u64, bit_length: usize) -> Vec<bool> {
    let mut result = Vec::with_capacity(bit_length);
    
    for i in (0..bit_length).rev() {
        // Extract bit at position i (starting from MSB)
        let bit = (n >> i) & 1 == 1;
        result.push(bit);
    }
    
    result
} 

/// Creates a CNF formula that is satisfied only by numbers less than 50
fn create_less_than_50_formula() -> CNFFormula {
    
    let mut clauses = Vec::new();
    
    clauses.push(Clause::new(vec![
        Literal::new_negative(0),
        Literal::new_negative(1),
        Literal::new_negative(2),
    ]));
    
    clauses.push(Clause::new(vec![
        Literal::new_negative(0),
        Literal::new_negative(1),
        Literal::new_negative(3),
    ]));
    
    clauses.push(Clause::new(vec![
        Literal::new_negative(0),
        Literal::new_negative(1),
        Literal::new_negative(4),
    ]));
    
    
    // Create and return the full CNF formula
    CNFFormula::new(clauses, 6) // 6 variables: x0, x1, x2, x3, x4, x5
}