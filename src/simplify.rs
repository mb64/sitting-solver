//! # Preprocessing
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
//!  - Unit propagation: if there is a clause with just one literal, it must be
//!    true.  This is also the main (currently only) simplification step in the
//!    DPLL loop.
//!
//!  - Redundant clauses: if a clause is a superset of another clause, it can be
//!    removed.
//!
//!    Example: `(x + y) and (x + y + z)` becomes `(x + y)`.
//!
//!  - Almost redundant clauses: if a clause is *almost* a superset of another
//!    clause, but one contains `-x` and the other `x`, then `±x` can be deleted
//!    from the bigger clause.
//!
//!    Example: `(x + y) and (-x + y + z)` becomes `(x + y) and (y + z)`
//!
//!  - Pure literals: if the problem contains a literal but not its negation, it
//!    can be assumed to be true.
//!
//!  - Almost pure literals: if the problem only contains the negation of a
//!    literal a few times, it's sometimes worth it to get rid of the variable
//!    through "resolution": turn every pair `(x + A) and (-x + B)` into `(A +
//!    B)`.
//!
//! Not yet implemented:
//!
//!  - Equivalent literals: given the clauses `(x + -y)` and `(-x + y)`, `x` and
//!    `y` are equivalent.
//!
//! ## Examples
//!
//! Make a [`Preprocessor`] struct using [`Preprocessor::new`], and run the
//! simplification steps to a fixpoint using [`Preprocessor::simplify`].
//!
//! ```
//! # use sitting_solver::data::*;
//! # use tinyvec::tiny_vec;
//! # use sitting_solver::Preprocessor;
//! let var_count = 2;
//! let x = Literal::new(VarId(0));
//! let y = Literal::new(VarId(1));
//!
//! let clauses = vec![
//!     tiny_vec![x, y],
//!     tiny_vec![x, !y],
//!     tiny_vec![!x, y],
//!     tiny_vec![!x, !y],
//! ];
//!
//! let mut pre = Preprocessor::new(var_count, clauses);
//!
//! // This problem is simple enough for the preprocessor to solve it completely
//! assert_eq!(pre.simplify(), Err(Unsat));
//! ```
//!
//! If the preprocessor doesn't return `Unsat`, get the resulting [`Solver`]
//! and [`Postprocessor`] using [`Preprocessor::finish`].
//!
//! Then, if the core solver doesn't return `Unsat`, use the postprocessor to
//! get a satisfying model using [`Postprocessor::postprocess`].
//!
//! ```
//! # use sitting_solver::data::*;
//! # use tinyvec::tiny_vec;
//! # use sitting_solver::{Preprocessor, VecMap};
//! let var_count = 2;
//! let x = Literal::new(VarId(0));
//! let y = Literal::new(VarId(1));
//!
//! let clauses = vec![
//!     tiny_vec![x, y],
//!     tiny_vec![x, !y],
//!     tiny_vec![!x, y],
//! ];
//!
//! let mut pre = Preprocessor::new(var_count, clauses);
//! pre.simplify().unwrap();
//!
//! // Call the main DPLL solver
//! let (mut solver, post) = pre.finish();
//! solver.solve().unwrap();
//!
//! // Get the satisfying model
//! let model = post.postprocess(&solver);
//!
//! // The only satisfying assignment for this problem is { x ↦ True, y ↦ True }
//! assert_eq!(model, VecMap::new(vec![VarState::True, VarState::True]));
//! ```

use crate::core::Solver;
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
            log::info!("Preprocessing found UNSAT: removed the last var from a clause");
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

#[derive(Debug, Clone, Eq, PartialEq)]
enum Soln {
    True,
    False,
    /// Was solved by resolution.
    ///
    /// In postprocessing, replace it by ``neg `xor` all [c is true | c <-
    /// clauses]``
    Resolution {
        neg: bool,
        clauses: Vec<data::Clause>,
    },
}

/// The main state for the preprocessor.
///
/// See the [module docs][`crate::simplify`] for more info
///
/// Get a `Preprocessor` from [`Preprocessor::new`], preprocess with
/// [`Preprocessor::simplify`], and then turn it into a [`Solver`] and
/// [`Postprocessor`] with [`Preprocessor::finish`]
#[derive(Debug, Clone)]
pub struct Preprocessor {
    original_clauses: Vec<data::Clause>,
    clauses: Vec<Clause>,
    counts: VecMap<Literal, u32>,
    solutions: IndexMap<VarId, Soln>,
    at_fixpoint: bool,
}

/// The main state for the post-processor.
///
/// See the [module docs][`crate::simplify`] for more info
///
/// It is used to undo simplifications intoduced by the preprocssor, after the
/// core solver has reached an answer.
///
/// Get a `Postprocessor` from [`Preprocessor::finish`], and use it to get a
/// model from the solver with [`Postprocessor::postprocess`].
#[derive(Debug, Clone)]
pub struct Postprocessor {
    original_clauses: Vec<data::Clause>,
    solutions: IndexMap<VarId, Soln>,
}

impl Preprocessor {
    pub fn new(var_count: u32, clauses: Vec<data::Clause>) -> Self {
        let original_clauses = clauses;
        let clauses: Vec<_> = original_clauses
            .iter()
            .map(|c| Clause {
                sig: signature(&c),
                clause: c.clone(),
            })
            .collect();
        let mut counts = VecMap::new(vec![0; var_count as usize * 2]);
        for clause in &clauses {
            for &lit in &clause.clause[..] {
                counts[lit] += 1;
            }
        }
        Self {
            original_clauses,
            clauses,
            counts,
            solutions: IndexMap::new(),
            at_fixpoint: false,
        }
    }

    /// Apply simplification steps to a fixpoint.
    pub fn simplify(&mut self) -> Result<(), Unsat> {
        let nclauses = self.clauses.len();
        log::info!(
            "Simplifying problem with {} vars and {} clauses",
            self.num_vars(),
            nclauses,
        );

        self.fixpoint(|this| {
            this.unit_clauses()?;
            this.pure_lits()?;
            this.redundant_clauses()
        })?;

        log::info!(
            "Preprocessing eliminated {} vars and {} clauses",
            self.solutions.len(),
            nclauses - self.clauses.len()
        );
        Ok(())
    }

    /// Build a [`Solver`] and [`Postprocessor`] from the preprocessed problem.
    pub fn finish(self) -> (Solver, Postprocessor) {
        let nvars = self.num_vars() as u32;
        let active_vars: Vec<_> = self
            .vars()
            .map(|l| l.var_id())
            .filter(|v| !self.solutions.contains_key(v))
            .collect();
        let clauses = self.clauses.into_iter().map(|c| c.clause).collect();
        let solver = Solver::new(nvars, &active_vars[..], clauses, self.counts);
        let post = Postprocessor {
            original_clauses: self.original_clauses,
            solutions: self.solutions,
        };
        (solver, post)
    }
}

/// Helper utilities
impl Preprocessor {
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

    fn assign_lit(&mut self, lit: Literal) -> Result<(), Unsat> {
        let soln;
        let bad_soln;
        if lit.is_negated() {
            soln = Soln::False;
            bad_soln = Soln::True;
        } else {
            soln = Soln::True;
            bad_soln = Soln::False;
        }

        log::debug!("Solved {:?}: {:?}", lit.var_id(), soln);

        if let Some(old_value) = self.solutions.insert(lit.var_id(), soln) {
            if old_value == bad_soln {
                log::info!(
                    "Preprocessing found UNSAT: {:?} assigned twice",
                    lit.var_id()
                );
                return Err(Unsat);
            }
        }

        Ok(())
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
impl Preprocessor {
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
impl Preprocessor {
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
impl Preprocessor {
    /// Process all pure literals and almost pure literals
    fn pure_lits(&mut self) -> Result<(), Unsat> {
        for v in self.vars() {
            if self.solutions.contains_key(&v.var_id()) {
                continue;
            }
            if self.counts[v] > ALMOST_PURE_LIMIT && self.counts[!v] > ALMOST_PURE_LIMIT {
                continue;
            }

            if self.counts[v] == 0 {
                self.one_pure_lit(!v)?;
            } else if self.counts[!v] == 0 {
                self.one_pure_lit(v)?;
            } else if !self.one_almost_pure_lit(v)? {
                continue;
            }

            // Handling a pure literal may have created new unit clauses. It's
            // probably better to deal with them now than to have resolution
            // possibly mask simplification opportunities
            // TODO: is it really?
            self.fixpoint(Self::unit_clauses)?;
        }

        Ok(())
    }

    fn one_pure_lit(&mut self, lit: Literal) -> Result<(), Unsat> {
        log::debug!("Processing pure {:?}", lit);
        self.at_fixpoint = false;

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
impl Preprocessor {
    /// Return `true` iff it was solved by resolution
    fn one_almost_pure_lit(&mut self, lit: Literal) -> Result<bool, Unsat> {
        log::debug!("Trying almost pure literal {:?}", lit);

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
                )?);

                // Make sure not to generate more clauses than we started with
                if new_clauses.len() > old_len {
                    log::debug!("{:?} wasn't almost-pure enough :(", lit);
                    return Ok(false);
                }
            }
        }

        log::debug!(
            "Success: replacing {} old clauses with {} new clauses",
            old_len,
            new_clauses.len()
        );

        // Update the counts
        for clause in &new_clauses {
            for &lit in &clause.clause {
                self.counts[lit] += 1;
            }
        }
        for &cid in positive_clauses.iter().chain(negative_clauses.iter()) {
            for &lit in &self.clauses[cid].clause {
                self.counts[lit] -= 1;
            }
        }

        // Update the solutions
        let soln = {
            let clause_inds;
            let neg;
            let to_remove;
            if positive_clauses.len() < negative_clauses.len() {
                clause_inds = &positive_clauses[..];
                neg = !lit.is_negated();
                to_remove = lit;
            } else {
                clause_inds = &negative_clauses[..];
                neg = lit.is_negated();
                to_remove = !lit;
            }

            Soln::Resolution {
                neg,
                clauses: clause_inds
                    .iter()
                    .map(|&cid| {
                        let mut c = mem::take(&mut self.clauses[cid].clause);
                        c.remove(c.iter().position(|&x| x == to_remove).unwrap());
                        c
                    })
                    .collect(),
            }
        };
        self.solutions.insert(lit.var_id(), soln);

        // Replace the positive_clauses and negative_clauses with new_clauses
        let mut inds = positive_clauses.into_iter().chain(negative_clauses);
        for new_clause in new_clauses {
            let i = inds.next().unwrap();
            self.clauses[i] = new_clause;
        }

        // If there's more old clauses than new clauses, remove them
        // Be sure to remove them back to front so that indices don't change
        let mut leftovers: Vec<_> = inds.collect();
        leftovers.sort_by(|a, b| b.cmp(a));
        for i in leftovers {
            self.clauses.swap_remove(i);
        }

        Ok(true)
    }

    /// Goal: make a new clause `(c1 - lit) ++ (c2 - !lit)`
    ///
    /// If that clause contains `x` and `!x` for some literal `x`, that's bad --
    /// return `None`
    fn resolve_two(lit: Literal, c1: &[Literal], c2: &[Literal]) -> Result<Option<Clause>, Unsat> {
        let mut result = {
            let clause: TinyVec<_> = c1.iter().copied().filter(|&l| l != lit).collect();
            Clause {
                sig: signature(&clause),
                clause,
            }
        };
        for l in c2.iter().copied().filter(|&l| l != !lit) {
            if result.contains(!l) {
                return Ok(None);
            } else if result.contains(l) {
                // don't want duplicates
                continue;
            } else {
                result.add_lit(l);
            }
        }

        if result.clause.is_empty() {
            log::info!("Preprocessing found UNSAT: resolved to an empty clause");
            Err(Unsat)
        } else {
            Ok(Some(result))
        }
    }
}

impl Postprocessor {
    /// Postprocess a successful solution from the core solver.
    ///
    /// Call this when [`Solver::solve`] returns `Ok` to get a satisfying model.
    pub fn postprocess(&self, solver: &Solver) -> VecMap<VarId, VarState> {
        let mut subst = solver.substitution.clone();

        // Assign values in the reverse order they were figured out
        for (&var, state) in self.solutions.iter().rev() {
            debug_assert_eq!(subst[var], Unknown);
            match state {
                Soln::False => subst[var] = VarState::False,
                Soln::True => subst[var] = VarState::True,
                Soln::Resolution { neg, clauses } => {
                    let bool_value = clauses
                        .iter()
                        .all(|c| c.iter().any(|&l| Self::true_in_subst(l, &subst)));
                    if bool_value ^ neg {
                        subst[var] = VarState::True;
                    } else {
                        subst[var] = VarState::False;
                    }
                }
            }
        }

        assert!(self.is_good(&subst));

        subst
    }

    fn true_in_subst(lit: Literal, subst: &VecMap<VarId, VarState>) -> bool {
        lit.is_negated() && subst[lit.var_id()] == VarState::False
            || !lit.is_negated() && subst[lit.var_id()] == VarState::True
    }

    fn is_good(&self, subst: &VecMap<VarId, VarState>) -> bool {
        'outer: for clause in &self.original_clauses {
            // Check every literal
            for &lit in clause {
                if Self::true_in_subst(lit, subst) {
                    continue 'outer;
                }
            }
            // None was true
            return false;
        }
        true
    }
}
