import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

open BigOperators
open scoped Classical 

variable {R : Type u} [Ring R] [StarRing R]

structure IsMeasurementSystem {I : Type*} [Fintype I] (f : I → R) : Prop where
  sum_one : ∑ x, f x = 1
  idempotent : ∀ x, f x * f x = f x
  orthogonal : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x

def Assignment (V : Fin r → Finset (Fin s)) (i : Fin r) := 
  {f : (v : Fin s) → v ∈ V i → Fin 2 // True} -- Using a slightly more robust subtype

-- We use a structure (Type) so we can define the observables later
structure LCSStrategy (r s : ℕ) (V : Fin r → Finset (Fin s)) where
  E : ∀ i, (Assignment V i → R)
  F : Fin s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j (α : Assignment V i) (β : Fin 2), 
    E i α * F j β = F j β * E i α

-- Now you can define the observables from the paper!
def alice_observable (strat : LCSStrategy r s V) (i : Fin r) (j : Fin s) (hj : j ∈ V i) : R :=
  (∑ x : {α // (α.val j hj) = 0}, strat.E i x.val) - 
  (∑ x : {α // (α.val j hj) = 1}, strat.E i x.val)

def bob_observable (strat : LCSStrategy r s V) (j : Fin s) : R :=
  strat.F j 0 - strat.F j 1
