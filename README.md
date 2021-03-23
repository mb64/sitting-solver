# Sitting solver

Sitting solver aspires to be a good SAT solver in the future.

To do:
 - [x] Main DPLL loop
 - [x] Watched literals
 - [x] Pre-processing
 - [ ] Post-processing (in progress)
 - [ ] Conflict analysis, for conflict-driven clause learning
 - [ ] Update the heuristic
 - [ ] Backjumping
 - [ ] Restarts?

In the (far) future, I hope to extend it to a simple DPLL(T) SMT solver. This
would involve:
 - A special preprocessing mode that only produces equivalent problems, not
   equisatisfiable problems
 - Likely a special postprocessing mode, too
 - Extensions to the main DPLL solver to allow feedback from the theory solver
 - A LRA solver
 - LRA preprocessing?
 - Other theories that'd be cool to have: nonlinear real arithmetic (likely by
   [ICP + LRA]), UIF by CEGAR

[ICP + LRA]: https://www.cs.colorado.edu/~srirams/papers/FMCAD10.PDF
