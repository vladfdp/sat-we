/// Represents a literal (a variable or its negation)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Literal {
    pub variable_index: usize,  // Which variable (x_k)
    pub is_negated: bool        // Whether it's negated (¬x_k)
}

impl Literal {
    /// Create a new positive literal (variable without negation)
    pub fn new_positive(variable_index: usize) -> Self {
        Literal {
            variable_index,
            is_negated: false
        }
    }
    
    /// Create a new negative literal (negated variable)
    pub fn new_negative(variable_index: usize) -> Self {
        Literal {
            variable_index,
            is_negated: true
        }
    }
    
    /// Evaluate the literal under a given assignment
    pub fn evaluate(&self, assignment: &[bool]) -> bool {
        if self.variable_index >= assignment.len() {
            panic!("Variable index out of bounds in assignment");
        }
        
        let var_value = assignment[self.variable_index];
        if self.is_negated {
            !var_value
        } else {
            var_value
        }
    }
}

/// Represents a clause (an OR of literals)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub literals: Vec<Literal>  // List of literals in this clause
}

impl Clause {
    /// Create a new clause from a vector of literals
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }
    
    /// Evaluate the clause under a given assignment
    /// A clause is satisfied if at least one of its literals is true
    pub fn evaluate(&self, assignment: &[bool]) -> bool {
        self.literals.iter().any(|literal| literal.evaluate(assignment))
    }
}

/// Represents a complete CNF formula (an AND of clauses)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CNFFormula {
    pub clauses: Vec<Clause>,
    pub num_variables: usize    // Total number of variables in formula
}

impl CNFFormula {
    /// Create a new CNF formula from a vector of clauses and the number of variables
    pub fn new(clauses: Vec<Clause>, num_variables: usize) -> Self {
        CNFFormula {
            clauses,
            num_variables
        }
    }
    
    /// Evaluate the formula under a given assignment
    /// A CNF formula is satisfied if all of its clauses are satisfied
    pub fn evaluate(&self, assignment: &[bool]) -> bool {
        if assignment.len() < self.num_variables {
            panic!("Assignment does not cover all variables in the formula");
        }
        
        self.clauses.iter().all(|clause| clause.evaluate(assignment))
    }
    
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_literal_evaluation() {
        let pos_literal = Literal::new_positive(0);
        let neg_literal = Literal::new_negative(1);
        
        // Test with variable 0 = true, variable 1 = false
        let assignment = vec![true, false];
        
        assert!(pos_literal.evaluate(&assignment)); // x₀ = true when assignment[0] = true
        assert!(neg_literal.evaluate(&assignment)); // ¬x₁ = true when assignment[1] = false
        
        // Test with variable 0 = false, variable 1 = true
        let assignment = vec![false, true];
        
        assert!(!pos_literal.evaluate(&assignment)); // x₀ = false when assignment[0] = false
        assert!(!neg_literal.evaluate(&assignment)); // ¬x₁ = false when assignment[1] = true
    }
    
    #[test]
    fn test_clause_evaluation() {
        // Clause: x₀ ∨ ¬x₁
        let clause = Clause::new(vec![
            Literal::new_positive(0),
            Literal::new_negative(1)
        ]);
        
        // Assignments to test:
        // [true, true]   => x₀ = true, ¬x₁ = false => clause is true
        // [true, false]  => x₀ = true, ¬x₁ = true  => clause is true
        // [false, true]  => x₀ = false, ¬x₁ = false => clause is false
        // [false, false] => x₀ = false, ¬x₁ = true => clause is true
        assert!(clause.evaluate(&vec![true, true]));
        assert!(clause.evaluate(&vec![true, false]));
        assert!(!clause.evaluate(&vec![false, true]));
        assert!(clause.evaluate(&vec![false, false]));
    }
    
    #[test]
    fn test_cnf_formula_evaluation() {
        // Formula: (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂)
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
        
        // Assignments to test:
        // [true, false, true]   => (true ∨ false) ∧ (false ∨ true) => true ∧ true => true
        // [true, false, false]  => (true ∨ false) ∧ (false ∨ false) => true ∧ false => false
        // [false, true, false]  => (false ∨ true) ∧ (true ∨ false) => true ∧ true => true
        // [false, false, true]  => (false ∨ false) ∧ (true ∨ true) => false ∧ true => false
        assert!(formula.evaluate(&vec![true, false, true]));
        assert!(!formula.evaluate(&vec![true, false, false]));
        assert!(formula.evaluate(&vec![false, true, false]));
        assert!(!formula.evaluate(&vec![false, false, true]));
    }
    
    #[test]
    fn test_satisfiability() {
        // Formula: (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ ¬x₁)
        // This formula is unsatisfiable (equivalent to x₀ ∧ ¬x₀)
        let unsatisfiable_formula = CNFFormula::new(
            vec![
                Clause::new(vec![  // x₀ ∨ x₁
                    Literal::new_positive(0),
                    Literal::new_positive(1),
                ]),
                Clause::new(vec![  // ¬x₀ ∨ x₁
                    Literal::new_negative(0),
                    Literal::new_positive(1),
                ]),
                Clause::new(vec![  // x₀ ∨ ¬x₁
                    Literal::new_positive(0),
                    Literal::new_negative(1),
                ]),
                Clause::new(vec![  // ¬x₀ ∨ ¬x₁
                    Literal::new_negative(0),
                    Literal::new_negative(1),
                ]),
            ],
            2
        );
        
        // Check all possible assignments (2^2 = 4 possibilities)
        assert!(!unsatisfiable_formula.evaluate(&vec![false, false]));
        assert!(!unsatisfiable_formula.evaluate(&vec![false, true]));
        assert!(!unsatisfiable_formula.evaluate(&vec![true, false]));
        assert!(!unsatisfiable_formula.evaluate(&vec![true, true]));
        
        // Formula: (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₂)
        // This formula is satisfiable
        let satisfiable_formula = CNFFormula::new(
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
        
        // Let's check the evaluation of the satisfiable formula with specific assignments
        // [false, true, false] => (false ∨ true) ∧ (true ∨ false) => true ∧ true => true
        assert!(satisfiable_formula.evaluate(&vec![false, true, false]));
        
        // [true, false, true] => (true ∨ false) ∧ (false ∨ true) => true ∧ true => true
        assert!(satisfiable_formula.evaluate(&vec![true, false, true]));
        
        // [true, true, true] => (true ∨ true) ∧ (false ∨ true) => true ∧ true => true
        assert!(satisfiable_formula.evaluate(&vec![true, true, true]));
        
        // [true, true, false] => (true ∨ true) ∧ (false ∨ false) => true ∧ false => false
        // This assignment should NOT satisfy the formula
        assert!(!satisfiable_formula.evaluate(&vec![true, true, false]));
    }
} 