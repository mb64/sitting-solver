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
 - [SATLIB] and the annual [SAT competitions] have huge catalogs of SAT
   benchmarks, in a [convenient format]

[Wikipedia page for DPLL]: https://en.wikipedia.org/wiki/DPLL_algorithm
[series of blog posts]: https://haz-tech.blogspot.com/2010/07/sat-solving-basics.html
[SAT tutorial paper]: http://poincare.matf.bg.ac.rs/~filip/phd/sat-tutorial.pdf
[The original MiniSAT paper]: http://minisat.se/downloads/MiniSat.pdf
[SATLIB]: https://www.cs.ubc.ca/~hoos/SATLIB/
[SAT Competitions]: https://satcompetition.github.io/
[convenient format]: http://www.satcompetition.org/2011/format-benchmarks2011.html

To do:
 - [x] Main DPLL loop
 - [x] Watched literals
 - [x] Pre-processing
 - [x] Post-processing
 - [x] Conflict analysis and conflict-driven clause learning
 - [ ] Conflict-clause minimization
 - [ ] Update the heuristic: VSIDS
 - [x] Backjumping
 - [x] Limits for clause learning, + heuristic for which learned clauses to keep
 - [ ] Restarts?
 - [ ] Profiling + optimization
 - [ ] Better docs

In the (far) future, I hope to extend it to a simple [DPLL(T)] SMT solver. This
would involve:
 - The Tseitin transformation
 - A special preprocessing mode for DPLL(T)
 - Likely a special postprocessing mode, too
 - Extensions to the main DPLL solver to allow feedback from the theory solver
 - Theory solvers: [LRA], congruence closure for UF
 - Theory-specific preprocessing?
 - Something about quantifiers and E-graphs, idk
 - Would also be cool to have: NRA by [ICP + LRA], LIA somehow

[DPLL(T)]: https://en.wikipedia.org/wiki/DPLL(T)
[LRA]: https://yices.csl.sri.com/papers/cav06.pdf
[ICP + LRA]: https://www.cs.colorado.edu/~srirams/papers/FMCAD10.PDF
