//! The core DPLL algorithm

use crate::data::*;
use crate::heuristic::Heuristic;
use crate::vec_map::VecMap;
use tinyvec::TinyVec;

/// The main state for the solver
#[derive(Debug, Clone)]
pub struct Solver {
    clauses: VecMap<ClauseId, Clause>,
    pub substitution: VecMap<VarId, VarState>,
    watched_clauses: VecMap<Literal, Vec<ClauseId>>,

    heuristic: Heuristic,

    /// Trail for backtracking variable choices
    trail: Vec<Literal>,

    /// Indices into the trail marking choice points
    /// The values of the vars at these indices in the trail were chosen instead
    /// of solved
    trailheads: Vec<usize>,

    /// Set of literals yet to process for unit prop, and the clauses they're
    /// unit in
    unit_prop_worklist: Vec<(Literal, ClauseId)>,

    reasons: VecMap<VarId, ClauseId>,

    counter: usize,
}

impl Solver {
    pub(crate) fn new(
        var_count: u32,
        active_vars: &[VarId],
        clauses: Vec<Clause>,
        counts: VecMap<Literal, u32>,
    ) -> Self {
        assert!(clauses.len() < u32::MAX as usize);

        let substitution = VecMap::new(vec![Unknown; var_count as usize]);

        let mut watched_clauses = VecMap::new(vec![Vec::new(); var_count as usize * 2]);
        let mut unit_prop_worklist = Vec::new();
        let priorities = counts;

        // Populate watched clauses
        for (i, clause) in clauses.iter().enumerate() {
            let cid = ClauseId::new(i as u32);

            // Populate watched clauses
            if clause.len() < 2 {
                // assume no clause is empty bc that'd be trivially UNSAT
                unit_prop_worklist.push((clause[0], cid));
            } else {
                watched_clauses[clause[0]].push(cid);
                watched_clauses[clause[1]].push(cid);
            }
        }

        // let vars: Vec<_> = (0..var_count).map(VarId::new).collect();
        let heuristic = Heuristic::new(active_vars, priorities);
        let reasons = VecMap::new(vec![ClauseId(0); var_count as usize]);

        Self {
            clauses: VecMap::new(clauses),
            substitution,
            watched_clauses,
            heuristic,
            trail: Vec::new(),
            trailheads: Vec::new(),
            unit_prop_worklist,
            reasons,
            counter: 0,
        }
    }
}

impl Solver {
    /// Increment the counter, and maybe log stuff idk
    fn tick(&mut self) {
        if self.counter % 100_000 == 0 {
            println!(
                "after {} iterations: {} vars left, {} clauses",
                self.counter,
                self.trail.len() + self.heuristic.len() + 1,
                self.clauses.len()
            );
        }
        self.counter += 1;
    }

    /// Add this variable to the trail
    fn trail(&mut self, lit: Literal) {
        // If there's no trailheads, then we know this variable assignment for
        // certain, and there's no need to ever backtrack it
        if !self.trailheads.is_empty() {
            self.trail.push(lit);
        }
        // println!("Trailing {:?}", lit);
    }

    /// Solve the SAT problem!
    ///
    /// Returns `Ok(())` if it's SAT and `Err(Unsat)` if it's UNSAT
    pub fn solve(&mut self) -> Result<(), Unsat> {
        debug_assert!(self.trail.is_empty());

        while let Some(next_lit) = self.heuristic.pop() {
            self.tick();

            match self.guess(next_lit) {
                Ok(()) => continue,
                Err(mut cid) => loop {
                    let (bad_guess, learned_cid) = self.handle_conflict(cid)?;

                    self.tick();

                    match self.nope_wrong(bad_guess, learned_cid) {
                        Ok(()) => break,
                        Err(new_cid) => cid = new_cid,
                    }
                },
            }
        }

        // Nothing left to guess -- we should be done
        Ok(())
    }

    /// Guess this lit is true, but it should be possible to backtrack
    fn guess(&mut self, lit: Literal) -> Result<(), ClauseId> {
        debug_assert!(self.unit_prop_worklist.is_empty());

        // println!("Trail length: {}", self.trail.len());
        // println!("Guessing {:?}", lit);

        // this is next level
        self.trailheads.push(self.trail.len());
        self.trail.push(lit);

        // For debugging purposes
        self.reasons[lit.var_id()] = ClauseId(u32::MAX);
        self.assign_true(lit)?;
        // if self.assign_true(lit).is_err() {
        //     self.unit_prop_worklist.clear();
        //     return Err(Unsat);
        // }
        self.unit_prop()
    }

    /// When you know this literal is false, since it doesn't work when it's
    /// true
    fn nope_wrong(&mut self, lit: Literal, clause_id: ClauseId) -> Result<(), ClauseId> {
        debug_assert!(self.unit_prop_worklist.is_empty());

        self.trail(!lit);

        self.reasons[lit.var_id()] = clause_id;
        self.assign_true(!lit)?;
        // if self.assign_true(!lit).is_err() {
        //     self.unit_prop_worklist.clear();
        //     return Err(Unsat);
        // }
        self.unit_prop()
    }

    fn lookup(subst: &VecMap<VarId, VarState>, lit: Literal) -> VarState {
        if lit.is_negated() {
            !subst[lit.var_id()]
        } else {
            subst[lit.var_id()]
        }
    }

    fn unit_prop(&mut self) -> Result<(), ClauseId> {
        while let Some((lit, cid)) = self.unit_prop_worklist.pop() {
            let bad_state = if lit.is_negated() { True } else { False };

            if self.substitution[lit.var_id()] == bad_state {
                // was already the other thing, fail
                self.unit_prop_worklist.clear();
                return Err(cid);
            }
            if self.substitution[lit.var_id()] != Unknown {
                // was already the right thing, don't need to update it
                continue;
            }

            self.trail(lit);
            self.reasons[lit.var_id()] = cid;
            self.assign_true(lit)?;
            // self.assign_true(lit).map_err(|cid| {
            //     self.unit_prop_worklist.clear();
            //     cid
            // })?;
        }

        Ok(())
    }

    fn clause_value(subst: &VecMap<VarId, VarState>, clause: &[Literal]) -> VarState {
        let mut result = False;
        for &lit in clause {
            match Self::lookup(subst, lit) {
                False => (),
                True => return True,
                Unknown => result = Unknown,
            }
        }
        result
    }

    /// Assign this literal to be true.
    fn assign_true(&mut self, lit: Literal) -> Result<(), ClauseId> {
        // println!("  Assigning {:?}", lit);

        // set the variable to its new value
        debug_assert_eq!(self.substitution[lit.var_id()], Unknown);
        self.substitution[lit.var_id()] = if lit.is_negated() { False } else { True };

        // Remove the variable from the queue
        self.heuristic.remove(lit.var_id());

        // loop thru this literal's watched clauses
        // (backwards, to make removing things easier)
        // for &clause_id in &self.watched_clauses[lit.var_id()] {
        for wi in (0..self.watched_clauses[!lit].len()).rev() {
            let clause_id = self.watched_clauses[!lit][wi];
            let clause = &mut self.clauses[clause_id][..];

            match Self::clause_value(&self.substitution, clause) {
                False => {
                    self.unit_prop_worklist.clear();
                    return Err(clause_id);
                }
                True => (), // nothing to learn
                Unknown => {
                    // Either unit prop or update watched literals

                    let mut first_unknown = None;
                    for i in 0..clause.len() {
                        if Self::lookup(&self.substitution, clause[i]) != Unknown {
                            continue;
                        }

                        if let Some(first) = first_unknown {
                            // There are two unknowns -- set them as the
                            // watched vars
                            // The first unknown should already be a
                            // watched var, so we just have to update the
                            // second

                            // Remove this clause from this literal's
                            // watched clauses
                            let this_wcs = &mut self.watched_clauses[!lit];
                            this_wcs.swap_remove(wi);

                            // add it to clause[i]'s watched clauses
                            let new_wcs = &mut self.watched_clauses[clause[i]];
                            new_wcs.push(clause_id);

                            // the watched clauses should always appear
                            // first
                            clause.swap(0, first);
                            clause.swap(1, i);

                            first_unknown = None;
                            break;
                        } else {
                            first_unknown = Some(i);
                        }
                    }

                    if let Some(only_unknown) = first_unknown {
                        // Unit prop time
                        self.unit_prop_worklist
                            .push((clause[only_unknown], clause_id));
                    }
                }
            }
        }

        Ok(())
    }

    /// firstUIP conflict analysis
    ///
    /// Returns the clause to learn, with the conflicting variable from the
    /// latest decision level at the front
    fn analyze_conflict(&mut self, bad_cid: ClauseId) -> Result<Clause, Unsat> {
        // Resolve the conflict clause against reason clauses until it only has
        // one variable from the latest decision level
        // println!("Conflict in {:?}", self.clauses[bad_cid]);

        // if there's no latest trailhead, the conflict is unconditional and the
        // whole thing is unsat
        let all_latest_lits = &self.trail[*self.trailheads.last().ok_or(Unsat)?..];

        // The new clause is represented as two vectors for convenience
        let mut new_clause = TinyVec::new();
        let mut new_clause_latest_lits = Vec::new();

        for &lit in &self.clauses[bad_cid] {
            debug_assert!(!all_latest_lits.contains(&lit));
            if all_latest_lits.contains(&!lit) {
                new_clause_latest_lits.push(lit);
            } else {
                new_clause.push(lit);
            }
        }

        assert!(!new_clause_latest_lits.is_empty());
        while new_clause_latest_lits.len() > 1 {
            let mut lit = new_clause_latest_lits.pop().unwrap();
            if lit == !all_latest_lits[0] {
                std::mem::swap(&mut lit, &mut new_clause_latest_lits[0]);
            }
            // Resolve with reason clause
            //println!("---- new clause to resolve with ----");
            //dbg!(lit);
            //println!(
            //    "reason clause: {:?}",
            //    self.clauses[self.reasons[lit.var_id()]]
            //);
            for &l in &self.clauses[self.reasons[lit.var_id()]] {
                // println!("new_clause: {:?}", &new_clause[..]);
                // println!("new_clause_latest_lits: {:?}", &new_clause_latest_lits[..]);
                // dbg!(l);
                debug_assert!(!new_clause.contains(&!l));
                debug_assert!(!new_clause_latest_lits.contains(&!l));
                if l == !lit {
                    continue;
                } else if all_latest_lits.contains(&!l) {
                    if !new_clause_latest_lits.contains(&l) {
                        new_clause_latest_lits.push(l);
                    }
                } else if !new_clause.contains(&l) {
                    new_clause.push(l);
                }
            }
        }

        new_clause.push(new_clause_latest_lits[0]);
        let last_ind = new_clause.len() - 1;
        new_clause.swap(0, last_ind);

        // println!("Learned clause: {:?}", new_clause);

        Ok(new_clause)
    }

    /// Dealing with a conflict involves three things:
    ///  * Conflict analysis
    ///  * Clause learning
    ///  * Backjumping
    ///
    /// Returns the new literal to try, and the clause id of the learned clause
    fn handle_conflict(&mut self, bad_cid: ClauseId) -> Result<(Literal, ClauseId), Unsat> {
        // Do conflict analysis and clause learning, then undo the updates, up
        // through the farthest point that makes the learned clause a unit clause
        //
        // Also set up watched literals for the new clause

        let learned_cid = ClauseId(self.clauses.len() as u32);
        let new_clause = self.analyze_conflict(bad_cid)?;
        self.clauses.inner.push(new_clause);
        let learned_clause = &mut self.clauses[learned_cid][..];

        // Special case: when the learned clause is actually a unit clause
        if learned_clause.len() == 1 {
            // I don't think this will happen
            unreachable!();
        }

        let most_recent_trailhead = *self.trailheads.last().unwrap();

        // Find the farthest point where it's still a unit clause
        let trail = &self.trail;
        let trail_ind = (0..most_recent_trailhead)
            .rfind(|&i| learned_clause.contains(&!trail[i]))
            .unwrap();
        let trailheads = &self.trailheads;
        let trailhead_ind = (1..self.trailheads.len())
            .rfind(|&i| trailheads[i - 1] <= trail_ind)
            .unwrap();
        let new_trail_len = self.trailheads[trailhead_ind];
        self.trailheads.drain(trailhead_ind..);

        // Backtrack
        for lit in self.trail.drain(new_trail_len..) {
            // println!("  Backtracking {:?}", var);
            self.substitution[lit.var_id()] = Unknown;
            self.heuristic.re_add(lit.var_id());
        }

        // Set up watched literals for the new clause
        // One watched literal is the most recent unit literal, and the other is
        // the latest trailed var in the clause
        {
            let watched_lit = !self.trail[trail_ind];
            for i in 1..learned_clause.len() + 1 {
                if learned_clause[i] == watched_lit {
                    learned_clause.swap(1, i);
                    break;
                }
            }
        }
        self.watched_clauses[learned_clause[0]].push(learned_cid);
        self.watched_clauses[learned_clause[1]].push(learned_cid);

        self.reasons[learned_clause[0].var_id()] = learned_cid;

        // println!("Backtracked to trail length {}", self.trail.len());

        Ok((!learned_clause[0], learned_cid))
    }

    /// Check the solution is valid
    pub fn verify(&self) {
        'outer: for clause in &self.clauses.inner {
            for &lit in &clause[..] {
                if Self::lookup(&self.substitution, lit) == True {
                    continue 'outer;
                }
            }
            panic!("Not satisfied: {:?}", clause);
        }
        println!("Yep, it's good");
    }
}
