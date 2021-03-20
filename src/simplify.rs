//! # Simplification / preprocessing
//!
//! The first step in SAT solving is try to simplify the input as much as
//! possible.
//!
//! Most of these transformations are from The Art of Computer Programming,
//! Volume 4 Fascicle 6, section 7.2.2.2 subsection "Preprocessing of clauses".
//!
//! There are a bunch of simplification operations, which are done to a
//! fixpoint:
//!
//!  - [x] Unit propation: if there is a clause with just one literal, it must
//!    be true.  This is also the main (currently only) simplification step in
//!    the DPLL loop.
//!
//!  - [ ] Redundant clauses: if a clause is a superset of another clause, it
//!    can be removed.
//!
//!    Example: `(x + y) and (x + y + z)` becomes `(x + y)`.
//!
//!  - [ ] Almost redundant clauses: if a clause is *almost* a superset of
//!    another clause, but one contains `-x` and the other `x`, then `±x` can be
//!    deleted from the bigger clause.
//!
//!    Example: `(x + y) and (-x + y + z)` becomes `(x + y) and (y + z)`
//!
//!  - [x] Pure literals: if the problem contains a literal but not its
//!    negation, it can be assumed to be true.
//!
//!  - [ ] Almost pure literals: if the problem only contains the negation of a
//!    literal *once*, it's worth it to get rid of the variable through
//!    "resolution": turn every pair `(x + A) and (-x + B)` into `(A + B)`.
//!

use crate::data::*;
use crate::vec_map::VecMap;
use indexmap::IndexMap;
use std::cmp::Ordering;
use std::mem;
use tinyvec::TinyVec;

const SIG_BITS: u32 = 64;

/// Clause signatures -- a quick bit set to make checking subset and almost
/// subset faster
///
/// Just map each literal to `var_id % SIG_BITS` then make a bit set
fn signature(cl: &[Literal]) -> u64 {
    cl.iter()
        .map(|&x| 1 << (x.var_id().0 % SIG_BITS))
        .fold(0, |x, y| x | y)
}

#[inline]
fn might_contain(sig: u64, lit: Literal) -> bool {
    sig & (1 << (lit.var_id().0 % SIG_BITS)) != 0
}

#[inline]
fn might_be_subset(a: u64, b: u64) -> bool {
    (a & !b) == 0
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Subset {
    Nope,
    Yep,
    /// Only the sign of this variable differs between them
    Almost(VarId),
}

fn definitely_subset(a: &[Literal], b: &[Literal]) -> Subset {
    debug_assert!(a.len() <= b.len());
    let mut almost = None;
    let mut ai = 0;
    let mut bi = 0;
    while ai < a.len() && bi < b.len() {
        match a[ai].var_id().cmp(&b[bi].var_id()) {
            Ordering::Less => bi += 1,
            Ordering::Greater => return Subset::Nope,
            Ordering::Equal => {
                if a[ai] == a[bi] {
                    // Right sign, all is well
                    ai += 1;
                    bi += 1;
                } else if almost.is_none() {
                    // Wrong sign, but it's ok
                    almost = Some(a[ai].var_id());
                    ai += 1;
                    bi += 1;
                } else {
                    // Wrong sign, and it's not ok
                    return Subset::Nope;
                }
            }
        }
    }

    if ai < a.len() {
        Subset::Nope
    } else if let Some(var) = almost {
        Subset::Almost(var)
    } else {
        Subset::Yep
    }
}

// Something like this
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Soln {
    True,
    False,
    /// Was solved by resolution. TODO: figure out how to get a solution out of
    /// this (might just have to resort to saving the original clauses and using
    /// guess and check)
    Resolution,
}

#[derive(Debug, Clone)]
pub struct Preprocessing {
    clauses: Vec<Clause>,
    sigs: Vec<u64>,
    counts: VecMap<Literal, u32>,
    pure_literal_worklist: Vec<Literal>,
    solutions: IndexMap<VarId, Soln>,
}

impl Preprocessing {
    pub fn new(var_count: u32, clauses: Vec<Clause>) -> Self {
        let sigs = clauses.iter().map(|c| signature(c)).collect();
        let mut counts = VecMap::new(vec![0; var_count as usize * 2]);
        for clause in &clauses {
            for &lit in &clause[..] {
                counts[lit] += 1;
            }
        }
        let mut pure_literal_worklist = Vec::new();
        for var_id in 0..var_count {
            let lit = Literal::new(VarId(var_id));
            if counts[lit] == 0 && counts[!lit] == 0 {
                // ehhh
                // TODO
            } else if counts[lit] == 0 {
                pure_literal_worklist.push(!lit);
            } else if counts[!lit] == 0 {
                pure_literal_worklist.push(lit);
            }
        }
        Self {
            clauses,
            sigs,
            counts,
            pure_literal_worklist,
            solutions: IndexMap::new(),
        }
    }

    pub fn simplify(&mut self) -> Result<(), Unsat> {
        println!("self: {:#?}", self);
        // Apply preprocessing steps to a fixpoint
        while !self.pure_literal_worklist.is_empty() {
            self.pure_lits()?;
            self.unit_clauses()?;
        }

        println!("Eliminated {} vars", self.solutions.len());
        Ok(())
    }

    // TODO: better interface
    pub fn get_clauses(self) -> Vec<Clause> {
        self.clauses
    }
}

impl Preprocessing {
    fn remove_clause(&mut self, index: usize) {
        self.sigs.swap_remove(index);
        let deleted = self.clauses.swap_remove(index);
        for &lit in &deleted {
            self.dec_lit_count(lit);
        }
    }

    fn update_clause(&mut self, index: usize, new_clause: Option<Clause>) {
        let new_clause = match new_clause {
            Some(new_clause) => new_clause,
            None => return self.remove_clause(index),
        };

        for &lit in &new_clause {
            self.inc_lit_count(lit);
        }
        self.sigs[index] = signature(&new_clause);
        let old_clause = mem::replace(&mut self.clauses[index], new_clause);
        for &lit in &old_clause {
            self.dec_lit_count(lit);
        }
    }

    fn inc_lit_count(&mut self, lit: Literal) {
        debug_assert!(self.counts[lit] != 0);
        self.counts[lit] += 1;
    }

    fn dec_lit_count(&mut self, lit: Literal) {
        self.counts[lit] -= 1;
        if self.counts[lit] == 0 && !self.solutions.contains_key(&lit.var_id()) {
            println!("Adding {:?} to pure literal worklist", lit);
            self.pure_literal_worklist.push(!lit);
        }
    }

    fn assign(&mut self, var: VarId, soln: Soln) -> Result<(), Unsat> {
        println!("Assigning {:?} to {:?}", var, soln);
        if let Some(old_value) = self.solutions.insert(var, soln) {
            match old_value {
                Soln::Resolution => unreachable!(),
                _ if old_value != soln => {
                    dbg!((soln, old_value, var));
                    return Err(Unsat);
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn assign_lit(&mut self, lit: Literal) -> Result<(), Unsat> {
        self.assign(
            lit.var_id(),
            if lit.is_negated() {
                Soln::False
            } else {
                Soln::True
            },
        )
    }

    /// Whether a clause contains this literal
    /// Can make use of the signatures as a bloom filter for more efficient
    /// querying
    fn clause_contains(&self, index: usize, lit: Literal) -> bool {
        might_contain(self.sigs[index], lit) && self.clauses[index].iter().any(|&l| l == lit)
    }

    /// Delete all clauses containing this literal, and add it to the
    /// `post_processing` list
    fn process_one_pure_lit(&mut self, lit: Literal) -> Result<(), Unsat> {
        self.assign_lit(lit)?;

        // iterate backwards for easy removal
        for i in (0..self.clauses.len()).rev() {
            if self.clause_contains(i, lit) {
                self.remove_clause(i);
            }
        }

        Ok(())
    }

    /// Process all pure literals
    fn pure_lits(&mut self) -> Result<(), Unsat> {
        println!("Pure literal worklist: {:?}", self.pure_literal_worklist);
        println!("solutions: {:?}", self.solutions);
        while let Some(lit) = self.pure_literal_worklist.pop() {
            println!("Processing pure {:?}", lit);
            self.process_one_pure_lit(lit)?;
        }

        println!("Clauses after pure lits: {:?}", self.clauses);

        Ok(())
    }

    /// Process all unit clauses
    fn unit_clauses(&mut self) -> Result<(), Unsat> {
        let mut worklist = Vec::new();
        // iterate backwards for easy removal
        for i in (0..self.clauses.len()).rev() {
            if self.clauses[i].len() <= 1 {
                // If the clause *does* have length 0, that means UNSAT
                // Don't think it'll ever happen tho
                // TODO: update this depending if it happens
                debug_assert!(self.clauses[i].len() != 0);

                worklist.push(self.clauses[i][0]);
                self.remove_clause(i);
            }
        }

        while let Some(lit) = worklist.pop() {
            self.one_unit(lit, &mut worklist)?;
        }

        Ok(())
    }

    fn one_unit(&mut self, lit: Literal, worklist: &mut Vec<Literal>) -> Result<(), Unsat> {
        self.assign_lit(lit)?;

        // iterate backwards for easy removal
        for clause_ind in (0..self.clauses.len()).rev() {
            // If the clause contains lit, remove the clause
            // Else if the clause contains !lit, remove !lit from the clause
            // and unit prop as necessary

            if !might_contain(self.sigs[clause_ind], lit) {
                continue;
            }
            let mut lit_ind = None;
            for (i, &l) in self.clauses[clause_ind].iter().enumerate() {
                if l == lit {
                    // The clause contains lit so it's trivially true --
                    // remove the clause
                    self.remove_clause(clause_ind);
                    break;
                } else if l == !lit {
                    lit_ind = Some(i);
                    break;
                }
            }
            let lit_ind = match lit_ind {
                Some(i) => i,
                None => continue,
            };

            // Remove !lit from the clause, updating the literal counts
            self.clauses[clause_ind].swap_remove(lit_ind);
            self.dec_lit_count(!lit);

            if self.clauses[clause_ind].is_empty() {
                // It might make the whole thing UNSAT
                return Err(Unsat);
            } else if self.clauses[clause_ind].len() == 1 {
                // Or it might create another unit clause
                worklist.push(self.clauses[clause_ind][0]);
                self.remove_clause(clause_ind);
            } else {
                // Otherwise, update the clause signature
                self.sigs[clause_ind] = signature(&*self.clauses[clause_ind]);
            }
        }

        Ok(())
    }
}
