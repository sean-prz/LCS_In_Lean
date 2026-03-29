import LCS.Strategy.ObservableStrategy
import LCS.Strategy.ProjectorStrategy
import LCS.Strategy.Equivalence
import LCS.Strategy.ObservableToProjector
import LCS.Observable
import LCS.Measurement
import LCS.WinningCondition
import LCS.Games.MagicSquare

/-!
# Linear Constraint System (LCS) Games
This library formalizes the theory of LCS games, quantum strategies,
and the winning condition derivation for perfect strategies.
-/


/-!
## Usage
To use this library, simply `import LCS`.
This provides access to:
- `LCSLayout`, `LCSGame`, and `LCSStrategy`
- Measurement system properties and Alice/Bob observables
- The Winning Operator and the derivation of identities 4.7.3 and 4.7.4
- The concrete Magic Square instance using Pauli matrices
-/
