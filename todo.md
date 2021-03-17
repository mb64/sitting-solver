## TODO

- Add pre-processing simplification stage, involving unit prop, pure literals,
  and deleting useless clauses
- Add conflict-directed clause learning, in a simple way
   - When backtracking: list all vars trail[trailheads] into a new clause
   - Info will be duplicated, but it's OK
   - Adjust priorities? Really need a better heuristic bc otherwise it'll only
     help vars with high priority
   - For now don't adjust priorities; for later look into better heursitics
     and/or better clause learning mechanisms
   - Honestly this will only be beneficial if there's a better heuristic; the
     issue with the python implementation is it just added clauses in this way,
     and then it never tried something in the future where knowing this clause
     would help.  Need a better heuristic to see the benefits of CDCL
- Every N iterations: Pure literals
- Every M iterations: Print stats
- Every K backtracks: divide scores by 2?
- Watch *literals*, not vars
   - reduce number of clause accesses by 1/2, great for the cache


