-- ANCHOR: imported
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Algebra.Basic        -- For the [Algebra ℂ R] typeclass
import Mathlib.Algebra.Module.Basic         -- For the scalar action (•)
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Complex.Basic           -- For the Complex numbers (ℂ)
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
-- ANCHOR_END: imported
open scoped BigOperators

-- From the docs : A *-ring R is a non-unital, non-associative (semi)ring
-- with an involutive star operation
-- which is additive which makes R with its multiplicative structure into a *-multiplication.
variable {R : Type*} [Ring R] [StarRing R]
-- ANCHOR_END: import
-- ANCHOR: IsMeasurementSystem
structure IsMeasurementSystem {I : Type*} [Fintype I] (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
-- ANCHOR_END: IsMeasurementSystem


/-- Assignemnt is an abreviation/aliases for the type, (function type). the type of functions that represents all possible assignments of values to the variables in V i. A type that represents all possible assignments of values to the variables in V i. -/ 
-- ANCHOR: Assignment
abbrev Assignment {r s : ℕ} (V : Fin r → Finset (Fin s)) (i : Fin r) : Type :=
  (V i) → Fin 2
-- ANCHOR_END: Assignment

/-- A strategy for an LCS game consists of:
    1. For each question i, and each possible assignment of values to the variables in V i, we have an element of R (this is the E function).
    2. For each variable j, and each possible outcome (0 or 1), we have an element of R (this is the F function).
    3. For each question i, the family of elements given by E i forms a measurement system.
    4. For each variable j, the family of elements given by F j forms a measurement system.
    5. For each i, j, and each possible assignment α and β, E_(i,α) commutes with F_(j,β).
-/
structure LCSStrategy (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
{r s : ℕ} (V : Fin r → Finset (Fin s)) where
  -- For each equation i in [r],
  -- and each possible combined, simultaneous assignment of values to ALL the variables in V i,
  -- we have an element of R.
  -- (i in [r], α : Assignment V i) ↦ E_(i,α) in R
  E : ∀ i, (Assignment V i → R)
  F : Fin s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α


noncomputable def Alice_A {r s : ℕ} {V : Fin r → Finset (Fin s)}
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (strat : LCSStrategy R V) (i : Fin r) (j : V i) : R :=
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment V i) => x j = 0), strat.E i x) -
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment V i) => x j = 1), strat.E i x)


def Bob_B {r s : ℕ} {V : Fin r → Finset (Fin s)}
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (strat : LCSStrategy R V) (j : Fin s) : R :=
  strat.F j 0 - strat.F j 1



structure LCSGame (r s : ℕ) where
  V : Fin r → Finset (Fin s)
  b : Fin r → ZMod 2  -- Target parity bit

def winning_assignments {r s : ℕ} (game : LCSGame r s) (i : Fin r) : 
  Finset (Assignment game.V i) :=
  Finset.univ.filter (fun α => (∑ j, (α j : ZMod 2)) = game.b i)




-- Lemma 1: Projectors for the same question commute
lemma measurement_system_projectors_commute
  {R : Type*} [Ring R] [StarRing R]
  {I : Type*} [Fintype I] (f : I → R) (h : IsMeasurementSystem f)
  (x y : I) : f x * f y = f y * f x := by
  by_cases hxy : x = y
  · rw [hxy]
  · -- When x ≠ y, use orthogonality and self-adjoint property
    have h_orth : f x * f y = 0 := h.orthogonal x y hxy
    have h_self_x : star (f x) = f x := h.self_adjoint x
    have h_self_y : star (f y) = f y := h.self_adjoint y
    -- Since f x and f y are self-adjoint, (f x * f y)^* = f y * f x
    -- But f x * f y = 0 (orthogonal), so f y * f x = 0
    have h_eq : f y * f x = star (f x * f y) := by 
      rw [star_mul, h_self_y, h_self_x]
    rw [h_orth] at h_eq
    rw [h_eq, star_zero]
    -- Now we have f x * f y = 0 and f y * f x = 0, so they are equal
    rw [h_orth]
    


-- Lemma 2: Sums of commuting projectors commute
lemma sum_of_commuting_projectors_commute
  {R : Type*} [Ring R] [StarRing R]
  {I : Type*} [Fintype I] (f : I → R) (h : IsMeasurementSystem f)
  (S T : Finset I) : 
  (∑ x ∈ S, f x) * (∑ y ∈ T, f y) = (∑ y ∈ T, f y) * (∑ x ∈ S, f x) := by
  -- Use distributivity to expand both sides
  rw [Finset.sum_mul, Finset.mul_sum]
  -- Now we need to show: ∑ x ∈ S, (f x * ∑ y ∈ T, f y) = ∑ x ∈ S, ((∑ y ∈ T, f y) * f x)
  -- This reduces to showing f x * ∑ y ∈ T, f y = (∑ y ∈ T, f y) * f x for each x
  apply Finset.sum_congr rfl
  intro x hx
  -- Now we need to show: f x * ∑ y ∈ T, f y = (∑ y ∈ T, f y) * f x
  -- We can prove this by showing f x commutes with each f y
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  exact measurement_system_projectors_commute f h x y


-- Main lemma: Alice_A observables commute
lemma alice_observables_commute
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {r s : ℕ} {V : Fin r → Finset (Fin s)}
  (strat : LCSStrategy R V) (i : Fin r) (j j' : V i) :
  (Alice_A strat i j) * (Alice_A strat i j') = (Alice_A strat i j') * (Alice_A strat i j) := by
  -- Expand Alice_A using the definition
  rw [Alice_A, Alice_A]
  -- Let A = sum where j = 0, B = sum where j = 1
  -- Let C = sum where j' = 0, D = sum where j' = 1
  let A := ∑ x ∈ Finset.univ.filter (fun x => x j = 0), strat.E i x -- x_j = 0
  let B := ∑ x ∈ Finset.univ.filter (fun x => x j = 1), strat.E i x -- x_j = 1
  let C := ∑ x ∈ Finset.univ.filter (fun x => x j' = 0), strat.E i x -- x_j' = 0
  let D := ∑ x ∈ Finset.univ.filter (fun x => x j' = 1), strat.E i x -- x_j' = 1
  
  -- Show that A and C commute, etc. using Lemma 2
  have h_AC : A * C = C * A := by
    apply sum_of_commuting_projectors_commute
    exact strat.alice_ms i
  have h_AD : A * D = D * A := by
    apply sum_of_commuting_projectors_commute
    exact strat.alice_ms i
  have h_BC : B * C = C * B := by
    apply sum_of_commuting_projectors_commute
    exact strat.alice_ms i
  have h_BD : B * D = D * B := by
    apply sum_of_commuting_projectors_commute
    exact strat.alice_ms i
  
  -- Now compute both sides
  change (A - B) * (C - D) = (C - D) * (A - B)
  simp [mul_sub, sub_mul]
  simp [h_AC, h_AD, h_BC, h_BD]
  abel
 
