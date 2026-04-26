import LCS.Strategy.ObservableStrategy
import LCS.Strategy.ProjectorStrategy
import LCS.Strategy.Equivalence
import LCS.Strategy.ObservableToProjector
import LCS.SolutionGroup
import LCS.Observable
import LCS.Measurement
import LCS.WinningCondition
import LCS.Games.MagicSquare

/-!
# Linear Constraint System (LCS) Games
This is the umbrella entry point for the Lean 4 formalisation of Linear Constraint
System (LCS) games.

The library is organised around four pieces of mathematics:

- the core combinatorial definitions of LCS layouts and games,
- two quantum strategy formalisms, one projector-based and one observable-based,
- the bridge from observable data to projector strategies,
- the local winning and local loss operators together with the sum-of-squares
  decomposition used to study perfect strategies.

The main concrete case study is the Mermin-Peres Magic Square game, formalised in
`LCS.Games.MagicSquare`.
-/


/-!
## Usage
To use this library, simply `import LCS`.

This provides access to:

- core game definitions from `LCS.Basic`
- measurement and observable interfaces from `LCS.Measurement` and `LCS.Observable`
- projector and observable strategy formalisms from the `LCS.Strategy` modules
- equivalence and conversion results between the two strategy viewpoints
- winning-condition constructions and the local loss SOS theorem from `LCS.WinningCondition`
- the concrete Magic Square example from `LCS.Games.MagicSquare`
-/
