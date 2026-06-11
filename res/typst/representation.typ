#import "@preview/physica:0.9.8" : *
#let Var = math.op("var")
#let Row = math.op("Row")
#let Rel = math.op("Rel")
#let lift = math.op("lift")
#let SolutionGroup = math.op("SolutionGroup")
#let equationRelator = math.op("equationRelator")
#let AliceRowProd = math.op("Alice_Row_Prod")
#let obs = math.op("obs")
#let val = math.op("val")

== Goal

The representation file constructs a homomorphism
$ rho : SolutionGroup(S) -> mat(n times n, CC)^times $
from matrices satisfying the analytic identities extracted by the EPR argument.

The generator assignment is
$ rho_0(x_j) = obs_j, wide rho_0(J) = -I. $

Since the solution group is a presented group, this generator assignment gives a
homomorphism only after every defining relator maps to $1$:
$ r in Rel(S) arrow.double.long lift(rho_0)(r) = 1. $

The file is mainly about organizing these relator proofs.

== Matrix units

The target is the group of units
$ mat(n times n, CC)^times. $

An observable matrix satisfies
$ obs_j^2 = I. $

So it is packaged as a unit by taking itself as its own inverse:
$ hat(obs_j) = (obs_j, obs_j), wide
  hat(obs_j)^2 = 1. $

The distinguished generator $J$ is represented by
$ -I. $

Since
$ (-I)^2 = I, $
it also gives a unit:
$ hat(-I)^2 = 1. $

Thus the generator-level map used in Lean is
$ rho_0(x_j) = hat(obs_j), wide rho_0(J) = hat(-I). $

This is `solutionGroupGeneratorImage`.

== The relators

The solution group has generators
$ x_j wide text("for variables") j, wide text("and") wide J. $

There are five kinds of relators.

First, every variable is an involution:
$ x_j^2 = 1. $

Second, $J$ is an involution:
$ J^2 = 1. $

Third, every variable commutes with $J$:
$ x_j J x_j^(-1) J^(-1) = 1, $
equivalently
$ x_j J = J x_j. $

Fourth, variables that occur in a common equation commute:
$ x_j x_k x_j^(-1) x_k^(-1) = 1, $
equivalently
$ x_j x_k = x_k x_j. $

Fifth, each equation gives a row-product relator.
If $V_i$ is the support of row $i$, then
$ product_(j in V_i) x_j = J^(b_i). $

As a relator word this is written
$ (product_(j in V_i) x_j) J^(-b_i) = 1. $

In Lean this is `equationRelator S i`.

== What must be proved

To construct the homomorphism, we must prove that each of these relator families
is killed by $rho_0$.

For variable involutions,
$ lift(rho_0)(x_j^2) = rho_0(x_j)^2
  = hat(obs_j)^2
  = 1. $

This uses observability:
$ obs_j^2 = I. $

For the $J$ involution,
$ lift(rho_0)(J^2) = rho_0(J)^2
  = hat(-I)^2
  = 1. $

This is purely algebraic.

For centrality of $J$,
$ lift(rho_0)(x_j J x_j^(-1) J^(-1)) = 1 $
is the same as
$ rho_0(x_j) rho_0(J) = rho_0(J) rho_0(x_j). $

Since $rho_0(J) = -I$, this holds because scalar matrices commute with every
matrix:
$ obs_j (-I) = (-I) obs_j. $

This is `commute_negOneMatrixUnit`.

For same-equation commutation, assume $j$ and $k$ occur together in a row.
The relator asks for
$ rho_0(x_j) rho_0(x_k) = rho_0(x_k) rho_0(x_j). $

At the matrix level this is
$ obs_j obs_k = obs_k obs_j. $

The observable strategy already carries row-wise commutation, and the Lean proof
translates common-row membership into `sameEquation`.

This is handled by `sameEquation_comm_of_row_comm`.

The only nontrivial family left is the equation relator:
$ lift(rho_0)((product_(j in V_i) x_j) J^(-b_i)) = 1. $

This is equivalent to proving the row identity
$ product_(j in V_i) obs_j = (-1)^(b_i) I. $

The rest of the file is mainly a bridge from the EPR extraction theorem to this
equation-relator proof.

== Universal property step

Let $R_S$ be the set of all relators.
If
$ forall r in R_S, wide lift(rho_0)(r) = 1, $
then the universal property of the presented group gives
$ rho : SolutionGroup(S) -> mat(n times n, CC)^times. $

This is `solutionGroupRepresentationOfRelatorProof`.

The lemma `solutionGroupRelatorProofOfEquationProof` splits the proof by cases
on the five relator families:
$ x_j^2, wide J^2, wide [x_j,J], wide [x_j,x_k], wide
  (product_(j in V_i) x_j) J^(-b_i). $

The first two are solved automatically by the unit packaging.
The $J$-commutation relators use $-I$.
The same-equation commutation relators use the row-wise commutation hypothesis.
The equation relators are supplied separately.

So the practical constructor asks only for:
$ obs_j obs_k = obs_k obs_j
  wide text("when") wide j,k wide text("share an equation"), $
and
$ lift(rho_0)(equationRelator_i) = 1
  wide text("for every") wide i. $

This is `solutionGroupRepresentationOfEquationProof`.

== Equation words and row products

The equation word is the ordered free-group product
$ w_i = product_(j in V_i) x_j. $

The matrix-side row product is
$ Row_i(obs) = product_(j in V_i) obs_j. $

Lean fixes a concrete order using the sorted support list.
This matters because free-group words are ordered, while the mathematical row
product is order-independent only after proving the row observables commute.

The evaluator lemma says
$ val(lift(rho_0)(w_i)) = Row_i(obs). $

This is `lift_equationWord_toLinearSystem_val`.

Therefore, if
$ Row_i(obs) = (-1)^(b_i) I, $
then
$ lift(rho_0)(w_i) = rho_0(J)^(b_i). $

Since
$ rho_0(J) = -I, $
the right hand side is exactly
$ (-I)^(b_i). $

Thus the relator
$ w_i J^(-b_i) $
maps to
$ rho_0(J)^(b_i) rho_0(J)^(-b_i) = 1. $

This is `lift_equationRelator_toLinearSystem_of_row`.

== Where EPR enters

The EPR extraction theorem gives, for each row $i$,
$ Row_i(obs) = (-1)^(b_i) I. $

The representation file obtains this from local-loss annihilation.
Choose some $j in V_i$.
The local loss at $(i,j)$ gives the three identities from the EPR note:
$ A = B^T, wide
  Row = (-1)^(b_i) I, wide
  (-1)^(b_i) Row A B^T = I. $

For the representation construction, only the middle identity is needed:
$ Row = (-1)^(b_i) I. $

The Lean proof identifies the strategy row product with the Alice lift of the
concrete row observable product:
$ AliceRowProd = Row_i(obs) times.o I. $

Then `local_matrix_identities_of_local_loss_annihilate_epr` returns
$ Row_i(obs) = (-1)^(b_i) I. $

This is `rowObservableProduct_eq_sign_of_local_loss`.

== Final constructor

The final construction is:

$ text("local loss kills") wide ket(Omega)
  arrow.double.long Row_i(obs) = (-1)^(b_i) I $

$ Row_i(obs) = (-1)^(b_i) I
  arrow.double.long lift(rho_0)(equationRelator_i) = 1 $

$ text("all relators map to") wide 1
  arrow.double.long
  rho : SolutionGroup("game.toLinearSystem") -> mat(n times n, CC)^times. $

The resulting homomorphism satisfies
$ rho(x_j) = hat(obs_j), wide rho(J) = hat(-I). $

This is `solutionGroupRepresentationOfEPRLoss`.
