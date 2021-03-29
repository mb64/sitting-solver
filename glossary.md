# SAT + SMT Glossary

A bunch of words whose meanings I used to not know.

### Acronyms

*SAT:* The Boolean satisfiability problem

*SMT:* Satisfiability Modulo Theories

*DPLL:* The Davis-Putnam-Logemann-Loveland algorithm, an algorithm for solving
the SAT problem using backtracking search

*CNF:* Conjunctive normal form, the format of the input to DPLL-based SAT
solvers

*BCP:* Boolean constraint propagation, aka unit propagation

*ICP:* Interval constraint propagation, a technique for nonlinear arithmetic
solvers

*CEGAR:* Counter-example guided abstract refinement

*LRA:* Linear real arithmetic

*LIA:* Linear integer arithmetic

*NRA:* Nonlinear real arithmetic

*NIA:* Nonlinear integer arithmetic


### SAT related terms

*Formula:* The problem to be solved

*Variable:* An individual Boolean input to the formula

*Literal:* Either a variable, or the negation of a variable. For example, if `x`
is a variable, then both `x` and `!x` (often written `-x`) are literals. (In
SMT solvers, `s/variable/atom/g`)

*Clause:* The OR of a set of literals. For example, `x or !y` is a clause

*Unit clause:* A clause containing just one literal

*Pure literal:* A literal whose negation never appears in the formula

*Resolution:* From the two clauses `x or A...` and `!x or B...`, deriving a new
clause `A... or B...` that doesn't mention `x`.


### SMT related terms

*Sort:* What SMT solvers call types

*Atom:* A Boolean formula that comes from some theory. For example: `x - y = 5`.
In DPLL(T), each atom in the SMT formula becomes a variable for the DPLL solver.

*Quantifier instantiation:* given a fact like `forall x, ...`, the process of
choosing specific instances of `x` to use.  This typically involves E-matching (?)

*Congruence:* The rule that says if `x = y` then `f(x) = f(y)`. *Ackerman
expansion* replaces terms like `f(x)` with fresh variables `f_x`, so computing
the consequences of congruence is done in *congruence closure*.  This is the
part with the E-graph (?)

*Simplex:* A type of linear arithmetic solver

*Saturation:* A type of theorem proving where you start with a set of clauses,
and use inference rules to add new clauses, to a fixpoint. As opposed to
*backtracking search*
