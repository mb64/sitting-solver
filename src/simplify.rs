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
//!  - [x] Redundant clauses: if a clause is a superset of another clause, it
//!    can be removed.
//!
//!    Example: `(x + y) and (x + y + z)` becomes `(x + y)`.
//!
//!  - [x] Almost redundant clauses: if a clause is *almost* a superset of
//!    another clause, but one contains `-x` and the other `x`, then `±x` can be
//!    deleted from the bigger clause.
//!
//!    Example: `(x + y) and (-x + y + z)` becomes `(x + y) and (y + z)`
//!
//!  - [x] Pure literals: if the problem contains a literal but not its
//!    negation, it can be assumed to be true.
//!
//!  - [x] Almost pure literals: if the problem only contains the negation of a
//!    literal *once*, it's worth it to get rid of the variable through
//!    "resolution": turn every pair `(x + A) and (-x + B)` into `(A + B)`.

use crate::data;
use crate::data::*;
use crate::vec_map::VecMap;
use indexmap::IndexMap;
use std::cmp::Ordering;
use std::mem;
use tinyvec::TinyVec;

const SIG_BITS: u32 = 64;

/// Clause signatures -- a quick bitset to make checking subset and almost
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct Clause {
    clause: data::Clause,
    sig: u64,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Subset {
    Nope,
    Yep,
    /// Only the sign of one literal differs between them
    /// This is the index of it in the bigger clause
    Almost(usize),
}

impl Clause {
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
                    if a[ai] == b[bi] {
                        // Right sign, all is well
                        ai += 1;
                        bi += 1;
                    } else if almost.is_none() {
                        // Wrong sign, but it's ok
                        almost = Some(bi);
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
        } else if let Some(ind) = almost {
            Subset::Almost(ind)
        } else {
            Subset::Yep
        }
    }

    fn is_subset_of(&self, other: &Self) -> Subset {
        if might_be_subset(self.sig, other.sig) {
            Self::definitely_subset(&self.clause[..], &other.clause[..])
        } else {
            Subset::Nope
        }
    }

    fn contains(&self, lit: Literal) -> bool {
        might_contain(self.sig, lit) && self.clause.contains(&lit)
    }

    fn remove(&mut self, ind: usize) -> Result<(), Unsat> {
        self.clause.swap_remove(ind);
        if self.clause.is_empty() {
            Err(Unsat)
        } else {
            self.sig = signature(&self.clause[..]);
            Ok(())
        }
    }

    fn add_lit(&mut self, lit: Literal) {
        debug_assert!(!self.contains(lit) && !self.contains(!lit));

        self.clause.push(lit);
        self.sig |= 1 << (lit.var_id().0 % SIG_BITS);
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
    counts: VecMap<Literal, u32>,
    solutions: IndexMap<VarId, Soln>,
    at_fixpoint: bool,
}

impl Preprocessing {
    pub fn new(var_count: u32, clauses: Vec<data::Clause>) -> Self {
        let clauses: Vec<_> = clauses
            .into_iter()
            .map(|c| Clause {
                sig: signature(&c),
                clause: c,
            })
            .collect();
        let mut counts = VecMap::new(vec![0; var_count as usize * 2]);
        for clause in &clauses {
            for &lit in &clause.clause[..] {
                counts[lit] += 1;
            }
        }
        Self {
            clauses,
            counts,
            solutions: IndexMap::new(),
            at_fixpoint: false,
        }
    }

    pub fn simplify(&mut self) -> Result<(), Unsat> {
        let nclauses = self.clauses.len();
        log::info!(
            "Simplifying problem with {} vars and {} clauses",
            self.num_vars(),
            nclauses,
        );
        log::debug!("self: {:#?}", self);

        self.fixpoint(|this| {
            this.fixpoint(Self::unit_clauses)?;
            this.fixpoint(Self::pure_lits)?;
            this.fixpoint(Self::almost_pure_lits)?;
            this.fixpoint(Self::redundant_clauses)?;
            Ok(())
        })?;

        log::info!(
            "Preprocessing eliminated {} vars and {} clauses",
            self.solutions.len(),
            nclauses - self.clauses.len()
        );
        Ok(())
    }

    // TODO: better interface
    pub fn get_clauses(self) -> Vec<data::Clause> {
        self.clauses.into_iter().map(|c| c.clause).collect()
    }
}

/// Helper utilities
impl Preprocessing {
    fn num_vars(&self) -> usize {
        self.counts.inner.len() / 2
    }

    /// An iterator through literals corresponding to the positive vars
    fn vars(&self) -> impl Iterator<Item = Literal> {
        (0..self.num_vars() as u32).map(|i| Literal::new(VarId(i)))
    }

    fn remove_clause(&mut self, index: usize) {
        let deleted = self.clauses.swap_remove(index);
        for lit in deleted.clause {
            self.counts[lit] -= 1;
        }
    }

    fn assign(&mut self, var: VarId, soln: Soln) -> Result<(), Unsat> {
        log::debug!("Solved {:?}: {:?}", var, soln);
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

    fn fixpoint(&mut self, mut f: impl FnMut(&mut Self) -> Result<(), Unsat>) -> Result<(), Unsat> {
        let old_at_fixpoint = self.at_fixpoint;
        self.at_fixpoint = false;
        while !self.at_fixpoint {
            self.at_fixpoint = true;
            f(self)?;
        }
        self.at_fixpoint &= old_at_fixpoint;
        Ok(())
    }
}

/// Unit clauses
impl Preprocessing {
    /// Process all unit clauses
    fn unit_clauses(&mut self) -> Result<(), Unsat> {
        let mut worklist = Vec::new();

        // iterate backwards for easy removal
        for i in (0..self.clauses.len()).rev() {
            if self.clauses[i].clause.len() <= 1 {
                self.at_fixpoint = false;
                worklist.push(self.clauses[i].clause[0]);
                self.clauses.swap_remove(i);
            }
        }

        while let Some(lit) = worklist.pop() {
            log::debug!("Processing unit clause {:?}", lit);
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

            if !might_contain(self.clauses[clause_ind].sig, lit) {
                continue;
            }
            let mut lit_ind = None;
            for (i, &l) in self.clauses[clause_ind].clause.iter().enumerate() {
                if l == lit {
                    // The clause contains lit so it's trivially true
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
            self.clauses[clause_ind].remove(lit_ind)?;
            self.counts[!lit] -= 1;

            if self.clauses[clause_ind].clause.len() == 1 {
                // It might create another unit clause
                worklist.push(self.clauses[clause_ind].clause[0]);
                self.remove_clause(clause_ind);
            }
        }

        Ok(())
    }
}

/// Redundant clauses and almost redundant clauses
impl Preprocessing {
    fn redundant_clauses(&mut self) -> Result<(), Unsat> {
        self.clauses.sort_by_key(|c| c.clause.len());
        for c in &mut self.clauses {
            c.clause.sort();
        }

        for i in (0..self.clauses.len()).rev() {
            for j in i + 1..self.clauses.len() {
                match self.clauses[i].is_subset_of(&self.clauses[j]) {
                    Subset::Nope => (),
                    Subset::Yep => {
                        self.at_fixpoint = false;
                        self.remove_clause(j);
                    }
                    Subset::Almost(index) => {
                        self.at_fixpoint = false;
                        self.clauses[j].remove(index)?;
                    }
                }
            }
        }

        Ok(())
    }
}

/// Pure literals
impl Preprocessing {
    /// Process all pure literals
    fn pure_lits(&mut self) -> Result<(), Unsat> {
        for var in self.vars() {
            if self.solutions.contains_key(&var.var_id()) {
                continue;
            }

            let pure_lit;
            if self.counts[var] == 0 {
                pure_lit = !var;
            } else if self.counts[!var] == 0 {
                pure_lit = var;
            } else {
                continue;
            };

            log::debug!("Processing pure {:?}", pure_lit);
            self.at_fixpoint = false;

            self.one_pure_lit(pure_lit)?;
        }

        Ok(())
    }

    fn one_pure_lit(&mut self, lit: Literal) -> Result<(), Unsat> {
        self.assign_lit(lit)?;

        // iterate backwards for easy removal
        for i in (0..self.clauses.len()).rev() {
            if self.clauses[i].contains(lit) {
                self.remove_clause(i);
            }
        }

        Ok(())
    }
}

/// If a literal occurs more than 10 times positively and more than 10 times
/// negatively, don't bother trying to solve it by resolution -- it's likely not
/// worth it
const ALMOST_PURE_LIMIT: u32 = 10;

/// Almost pure literals
impl Preprocessing {
    /// Process all almost pure literals
    fn almost_pure_lits(&mut self) -> Result<(), Unsat> {
        for v in self.vars() {
            if self.solutions.contains_key(&v.var_id()) {
                continue;
            }
            if self.counts[v] > ALMOST_PURE_LIMIT && self.counts[!v] > ALMOST_PURE_LIMIT {
                continue;
            }

            log::debug!("Trying almost pure literal {:?}", v);
            self.one_almost_pure_lit(v);
        }

        Ok(())
    }

    fn one_almost_pure_lit(&mut self, lit: Literal) {
        let mut positive_clauses = Vec::new();
        let mut negative_clauses = Vec::new();
        for (i, c) in self.clauses.iter().enumerate() {
            if c.contains(lit) {
                positive_clauses.push(i);
            } else if c.contains(!lit) {
                negative_clauses.push(i);
            }
        }

        let old_len = positive_clauses.len() + negative_clauses.len();

        let mut new_clauses = Vec::new();
        for &p in &positive_clauses {
            for &n in &negative_clauses {
                new_clauses.extend(Self::resolve_two(
                    lit,
                    &self.clauses[p].clause[..],
                    &self.clauses[n].clause[..],
                ));

                // Make sure not to generate more clauses than we started with
                if new_clauses.len() > old_len {
                    log::debug!("{:?} wasn't almost pure enough :(", lit);
                    return;
                }
            }
        }

        // Replace the positive_clauses and negative_clauses with new_clauses
        log::debug!(
            "Success: replacing {} old clauses with {} new clauses",
            old_len,
            new_clauses.len()
        );
        let mut inds = positive_clauses.into_iter().chain(negative_clauses);
        for new_clause in new_clauses {
            let i = inds.next().unwrap();
            for &l in &new_clause.clause {
                self.counts[l] += 1;
            }
            let old_clause = mem::replace(&mut self.clauses[i], new_clause);
            for l in old_clause.clause {
                self.counts[l] -= 1;
            }
        }
        // If there's more old clauses than new clauses, remove them
        for i in inds {
            self.remove_clause(i);
        }
    }

    /// Goal: make a new clause `(c1 - lit) ++ (c2 - !lit)`
    ///
    /// If that clause contains `x` and `!x` for some literal `x`, that's bad --
    /// return `None`
    fn resolve_two(lit: Literal, c1: &[Literal], c2: &[Literal]) -> Option<Clause> {
        let mut result = {
            let clause: TinyVec<_> = c1.iter().copied().filter(|&l| l != lit).collect();
            Clause {
                sig: signature(&clause),
                clause,
            }
        };
        for l in c2.iter().copied().filter(|&l| l != !lit) {
            if result.contains(!l) {
                return None;
            } else if result.contains(l) {
                // don't want duplicates
                continue;
            } else {
                result.add_lit(l);
            }
        }

        Some(result)
    }
}
