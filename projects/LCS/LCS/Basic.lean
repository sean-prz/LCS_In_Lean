import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R]
-- ANCHOR: IsMeasurementSystem
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
-- ANCHOR_END: IsMeasurementSystem

-- ANCHOR: LCSLayout
structure LCSLayout where
  r : ℕ
  s : ℕ
  V : Fin r → Finset (Fin s)
-- ANCHOR_END: LCSLayout

-- ANCHOR: Assignment
abbrev Assignment (G : LCSLayout) (i : Fin G.r) : Type :=
  (G.V i) → Fin 2
-- ANCHOR_END: Assignment


-- ANCHOR: LCSGame
structure LCSGame (G : LCSLayout) where
  b : Fin G.r → ZMod 2
-- ANCHOR_END: LCSGame

-- ANCHOR: LCSStrategy
structure LCSStrategy
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
  (G : LCSLayout) where
  E : ∀ i, (Assignment G i → R)
  F : Fin G.s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α
-- ANCHOR_END: LCSStrategy

-- ANCHOR: Alice_A
noncomputable def Alice_A
  {G : LCSLayout}
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment G i) => x j = 0), strat.E i x) -
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment G i) => x j = 1), strat.E i x)
-- ANCHOR_END: Alice_A

-- ANCHOR: Bob_B
def Bob_B
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout}
  (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  strat.F j 0 - strat.F j 1
-- ANCHOR_END: Bob_B
