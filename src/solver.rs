use crate::data::*;
use crate::priority_queue::PriorityQueue;
use crate::vec_map::VecMap;

/// The main state for the solver
#[derive(Debug, Clone)]
pub struct Solver {
    /// semantically: Map<clause id, Clause>
    clauses: VecMap<ClauseId, Clause>,

    /// semantically: Map<variable id, VarState>
    pub substitution: VecMap<VarId, VarState>,

    /// semantically: Map<literal, watched clauses>
    // Memory TODO: optimize for size
    // (VecMap<VarId, Option<Box<Vec<ClauseId>>>> ? Or 32-bit capacity/len?)
    watched_clauses: VecMap<VarId, Vec<ClauseId>>,

    /// Priority queue to figure out which variable to choose next
    /// The `i32` is the number of active clauses it's in, or `i32::MIN` if it
    /// already has a value
    priority_queue: PriorityQueue<VarId, i32>,

    /// true if it appears positively more than negatively
    preferred_direction: VecMap<VarId, bool>,

    /// Trail for backtracking variable choices
    trail: Vec<VarId>,
    /// Indices into the trail marking choice points
    /// The values of the vars at these indices in the trail were chosen instead
    /// of solved
    trailheads: Vec<usize>,

    /// Set of literals yet to process for unit prop
    unit_prop: Vec<Literal>,
}

impl Solver {
    pub fn new(var_count: u32, clauses: Vec<Clause>) -> Self {
        assert!(clauses.len() < u32::MAX as usize);

        let substitution = VecMap::new(vec![Unknown; var_count as usize]);

        let mut watched_clauses = VecMap::new(vec![Vec::new(); var_count as usize]);
        let mut unit_prop = Vec::new();
        let mut priorities = VecMap::new(vec![0; var_count as usize]);
        let mut pos_minus_neg = VecMap::new(vec![0i32; var_count as usize]);

        // Populate watched clauses, priorities, and preferred directions
        for (i, clause) in clauses.iter().enumerate() {
            let cid = ClauseId::new(i as u32);

            // Populate watched clauses
            if clause.len() < 2 {
                // assume no clause is empty bc that'd be trivially UNSAT
                unit_prop.push(clause[0]);
            } else {
                watched_clauses[clause[0].var_id()].push(cid);
                watched_clauses[clause[1].var_id()].push(cid);
            }

            // Populate priorities
            for &lit in &clause[..] {
                priorities[lit.var_id()] += 1;
                if lit.is_negated() {
                    pos_minus_neg[lit.var_id()] -= 1;
                } else {
                    pos_minus_neg[lit.var_id()] += 1;
                }
            }
        }

        let preferred_direction =
            VecMap::new(pos_minus_neg.inner.into_iter().map(|i| i >= 0).collect());

        let vars: Vec<_> = (0..var_count as u32).map(VarId::new).collect();
        let priority_queue = PriorityQueue::new(&vars[..], priorities);

        Self {
            clauses: VecMap::new(clauses),
            substitution,
            watched_clauses,
            priority_queue,
            preferred_direction,
            trail: Vec::new(),
            trailheads: Vec::new(),
            unit_prop,
        }
    }
}

impl Solver {
    /// Add this variable to the trail
    fn trail(&mut self, var: VarId) {
        // If there's no trailheads, then we know this variable assignment for
        // certain, and there's no need to ever backtrack it
        //
        // TODO: bench with and without the if statement
        if !self.trailheads.is_empty() {
            self.trail.push(var);
        }
    }

    /// Solve the SAT problem!
    ///
    /// Returns true if it's SAT and false if it's UNSAT
    pub fn solve(&mut self) -> bool {
        debug_assert!(self.trail.is_empty());

        // In case it started out with any unitary clauses
        if self.unit_prop().is_err() {
            println!("bad from the start");
            return false;
        }

        let mut count: usize = 0;

        while let Some(next_var) = self.priority_queue.pop() {
            count += 1;
            if count % 1_000_000 == 0 {
                println!(
                    "after {} iterations: {}",
                    count,
                    self.trail.len() + self.priority_queue.len() + 1
                );
            }

            match self.guess(next_var) {
                Ok(()) => continue,
                Err(Unsat) => loop {
                    let bad_guess = match self.backtrack() {
                        Ok(bad_guess) => bad_guess,
                        Err(Unsat) => return false,
                    };

                    if self.nope_wrong(bad_guess).is_ok() {
                        break;
                    }

                    count += 1;
                    if count % 1_000_000 == 0 {
                        println!(
                            "after {} iterations: {}",
                            count,
                            self.trail.len() + self.priority_queue.len()
                        );
                    }
                },
            }
        }

        // Nothing left to guess -- we should be done
        debug_assert!(self.substitution.inner.iter().all(|&x| x != Unknown));

        true
    }

    /// Guess this var in its preferred direction, but it should be possible to
    /// backtrack
    fn guess(&mut self, var: VarId) -> Result<(), Unsat> {
        debug_assert!(self.unit_prop.is_empty());

        // println!("Guessing {:?}", Literal::new(var));

        // this is next level
        self.trailheads.push(self.trail.len());
        self.trail.push(var);

        let lit = if self.preferred_direction[var] {
            Literal::new(var)
        } else {
            !Literal::new(var)
        };

        if self.assign_true(lit).is_err() {
            self.unit_prop.clear();
            return Err(Unsat);
        }
        self.unit_prop()
    }

    /// When you know this var is the other way, since it doesn't work when it's
    /// its preferred way
    fn nope_wrong(&mut self, var: VarId) -> Result<(), Unsat> {
        debug_assert!(self.unit_prop.is_empty());

        self.trail(var);

        let lit = if self.preferred_direction[var] {
            !Literal::new(var)
        } else {
            Literal::new(var)
        };

        if self.assign_true(lit).is_err() {
            self.unit_prop.clear();
            return Err(Unsat);
        }
        self.unit_prop()
    }

    fn lookup(subst: &VecMap<VarId, VarState>, lit: Literal) -> VarState {
        if lit.is_negated() {
            !subst[lit.var_id()]
        } else {
            subst[lit.var_id()]
        }
    }

    fn unit_prop(&mut self) -> Result<(), Unsat> {
        while let Some(lit) = self.unit_prop.pop() {
            let bad_state = if lit.is_negated() { True } else { False };

            if self.substitution[lit.var_id()] == bad_state {
                // was already the other thing, fail
                self.unit_prop.clear();
                return Err(Unsat);
            }
            if self.substitution[lit.var_id()] != Unknown {
                // was already the right thing, don't need to update it
                continue;
            }

            self.trail(lit.var_id());
            if self.assign_true(lit).is_err() {
                self.unit_prop.clear();
                return Err(Unsat);
            }
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
    fn assign_true(&mut self, lit: Literal) -> Result<(), Unsat> {
        // println!("  Assigning {:?}", lit);

        // set the variable to its new value
        debug_assert_eq!(self.substitution[lit.var_id()], Unknown);
        self.substitution[lit.var_id()] = if lit.is_negated() { False } else { True };

        // Remove the variable from the queue
        self.priority_queue.remove(lit.var_id());

        // loop thru this literal's watched clauses
        // (backwards, to make removing things easier)
        // for &clause_id in &self.watched_clauses[lit.var_id()] {
        for wi in (0..self.watched_clauses[lit.var_id()].len()).rev() {
            let clause_id = self.watched_clauses[lit.var_id()][wi];
            let clause = &mut self.clauses[clause_id][..];

            // TODO perf: could merge this into a single loop?
            // (would look even uglier)
            match Self::clause_value(&self.substitution, clause) {
                False => return Err(Unsat),
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
                            let this_wcs = &mut self.watched_clauses[lit.var_id()];
                            this_wcs[wi] = this_wcs[this_wcs.len() - 1];
                            this_wcs.pop().unwrap();

                            // add it to clause[i]'s watched clauses
                            let new_wcs = &mut self.watched_clauses[clause[i].var_id()];
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
                        self.unit_prop.push(clause[only_unknown]);
                    }
                }
            }
        }
        Ok(())
    }

    /// Undo the most recent group of updates
    /// Returns the most recent guess that was wrong
    fn backtrack(&mut self) -> Result<VarId, Unsat> {
        // if there's no trailhead, there's no bad guess to undo -- the whole
        // problem is UNSAT
        let most_recent_trailhead = self.trailheads.pop().ok_or(Unsat)?;

        let bad_guess = self.trail[most_recent_trailhead];

        // println!("Backtracking:");

        // for each variable in the most recent section of the trail:
        //    reset the variable to Unknown
        //    re-add it to the priority queue
        for var in self.trail.drain(most_recent_trailhead..) {
            // println!("  Backtracking {:?}", var);
            self.substitution[var] = Unknown;
            self.priority_queue.re_add(var);
        }

        Ok(bad_guess)
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
