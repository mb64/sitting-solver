# Sitting solver

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

Sitting solver aspires to be a good SAT solver in the future.

Resources about SAT solvers:
 - The [Wikipedia page for DPLL] has a concise recursive formulation of the
   basic DPLL algorithm
 - This [series of blog posts] has good explanations of the ideas behind DPLL,
   clause learning, and the two watched literals scheme, but be aware that their
   implementation of clause learning without conflict analysis isn't great
 - This [SAT tutorial paper] is pretty good too; it has simple code examples
   with thorough explanations.  I found its explanation of conflict analysis and
   backjumping particularly useful.
 - [The original MiniSAT paper] is also helpful

[Wikipedia page for DPLL]: https://en.wikipedia.org/wiki/DPLL_algorithm
[series of blog posts]: https://haz-tech.blogspot.com/2010/07/sat-solving-basics.html
[SAT tutorial paper]: http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
[The original MiniSAT paper]: http://minisat.se/downloads/MiniSat.pdf

To do:
 - [x] Main DPLL loop
 - [x] Watched literals
 - [x] Pre-processing
 - [ ] Post-processing (in progress)
 - [x] Conflict analysis and conflict-driven clause learning
 - [ ] Conflict-clause minimization
 - [ ] Update the heuristic: VSIDS
 - [x] Backjumping
 - [ ] Limits for clause learning, + heuristic for which learned clauses to keep
 - [ ] Restarts?

In the (far) future, I hope to extend it to a simple [DPLL(T)] SMT solver. This
would involve:
 - The Tseitin transformation
 - A special preprocessing mode that only produces equivalent problems, not
   equisatisfiable problems
 - Likely a special postprocessing mode, too
 - Extensions to the main DPLL solver to allow feedback from the theory solver
 - A LRA solver
 - Theory-specific preprocessing?
 - Something about quantifiers, idk
 - Other theories that'd be cool to have: nonlinear real arithmetic (likely by
   [ICP + LRA]), UIF by CEGAR

[DPLL(T)]: https://en.wikipedia.org/wiki/DPLL(T)
[ICP + LRA]: https://www.cs.colorado.edu/~srirams/papers/FMCAD10.PDF
