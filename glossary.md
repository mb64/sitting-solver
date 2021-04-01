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

*EUF:* Equality and uninterpreted functions

*QF_...:* Quantifier-free ...


### SAT related terms

*Formula:* The problem to be solved

*Variable:* An individual Boolean input to the formula

*Literal:* Either a variable, or the negation of a variable. For example, if `x`
is a variable, then both `x` and `!x` (often written `-x`) are literals. (In
SMT solvers, `s/variable/atom/`)

*Clause:* The OR of a set of literals. For example, `x or !y` is a clause

*Assignment:* A mapping from variables to truth values

*Unit clause:* A clause containing just one literal

*Pure literal:* A literal whose negation never appears in the formula

*Resolution:* From the two clauses `x or A...` and `!x or B...`, deriving a new
clause `A... or B...` that doesn't mention `x`


### SMT related terms

*Theory:* Formally, a set of formulas. A theory usually implicitly has some
nice properties, like closure under some deductive system

*Interpreted symbol:* Symbols that have a particular meaning assigned to them by
a theory (like `=` or `+`)

*Uninterpreted symbol:* Symbols that don't have a particular meaning, like `f`
in the formula `f(0) = 0`.

*Constant:* The (implicitly existentially quantified) inputs to a formula. For
example, in `a = 5`, `a` is a constant. (`5` is an "interpreted symbol")

*Variable:* A universally quantified variable in a formula. Not to be confused
with atoms (called variables in the SAT solver) or constants (existentially
quantified variables)

*Model:* A mapping from constants to values

*Sort:* What SMT solvers call types

*Atom:* A Boolean formula that comes from some theory. For example: `a - b = 5`.
In DPLL(T), each atom in the SMT formula becomes a variable for the DPLL solver.

*Quantifier instantiation:* given a fact like `forall x, ...`, the process of
choosing specific instances of `x` to use.  This could involve E-matching (?).
Note that you can refute a formula like this (answer UNSAT), but it's hard to
prove it (answer SAT): for that you need [fancy theorems]

[fancy theorems]: http://leodemoura.github.io/files/citr09.pdf

*Congruence:* The rule that says if `a = b` then `f(a) = f(b)`. *Ackerman
expansion* replaces terms like `f(a)` with fresh variables `f_a`, so computing
the consequences of congruence is done in *congruence closure*.  This is the
part with the E-graph (?)

*Simplex:* A type of linear arithmetic solver (from linear programming)

*Saturation:* A type of theorem proving where you start with a set of clauses,
and use inference rules to add new clauses, to a fixpoint. As opposed to
*backtracking search*

*Skolemization:* A process to get rid of existential quantifiers in a
formula. For example, `forall x, exists y, x = y` can be skolemized by
introducing a new uninterpreted function `y'`, and changing the formula to
`forall x, x = y'(x)`
