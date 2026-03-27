import LCS.Basic
import LCS.Observable
import Mathlib.Algebra.Star.Module

open scoped BigOperators

namespace ObservableStrategy

structure ObservableStrategyData
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (G : LCSLayout) where
  obs : Fin G.s → R
  observable : ∀ j, IsObservable (obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))


end ObservableStrategy
