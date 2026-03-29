import LCS.Basic
import LCS.Observable
import Mathlib.Algebra.Star.Module

/-!
# Observable-based Strategy for LCS Games

This module defines the data structure for a strategy in a Linear Constraint System (LCS)
game using the observable formalism. In this formalism, players choose observables
(self-adjoint involutive operators) instead of projectors.

## Key Definitions
- `ObservableStrategyData`: The data representing an observable strategy, including:
  - `alice_obs`, `bob_obs`: The observables for Alice and Bob.
  - `sameEquation_comm`: The local commutativity of Alice's observables within an equation.
  - `alice_bob_commute`: The global commutativity between Alice's and Bob's observables.
-/

open scoped BigOperators

namespace ObservableStrategy

structure ObservableStrategyData
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (G : LCSLayout) where
  alice_obs : Fin G.s → R
  bob_obs : Fin G.s -> R
  alice_observable : ∀ j, IsObservable (alice_obs j)
  bob_observable : ∀ j, IsObservable (bob_obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (alice_obs j.1) (alice_obs k.1))
  alice_bob_commute :
    ∀ j k, Commute (alice_obs j) (bob_obs k)


end ObservableStrategy
