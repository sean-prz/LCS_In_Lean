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


-- ANCHOR: winning_assignments
def winning_assignments
  {G : LCSLayout}
  (game : LCSGame G) (i : Fin G.r) : 
  Finset (Assignment G i) :=
  Finset.univ.filter (fun α => (∑ j : G.V i , (α j : ZMod 2)) = game.b i)
-- ANCHOR_END: winning_assignments




-- Lemma 1: Projectors for the same question commute
lemma measurement_system_projectors_commute
  {R : Type*} [Ring R] [StarRing R]
  {I : Type*} [Fintype I] (f : I → R) (h : IsMeasurementSystem f)
  (x y : I) : f x * f y = f y * f x := by
  by_cases hxy : x = y
  · rw [hxy]
  · have h_orth_xy : f x * f y = 0 := h.orthogonal x y hxy
    have h_orth_yx : f y * f x = 0 := h.orthogonal y x (Ne.symm hxy)
    rw [h_orth_xy, h_orth_yx]


-- Lemma 2: Sums of commuting projectors commute
lemma sum_of_commuting_projectors_commute
  {R : Type*} [Ring R] [StarRing R]
  {I : Type*} [Fintype I] (f : I → R) (h : IsMeasurementSystem f)
  (S T : Finset I) : 
  (∑ x ∈ S, f x) * (∑ y ∈ T, f y) = (∑ y ∈ T, f y) * (∑ x ∈ S, f x) := by
  -- Use distributivity to expand both sides
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  exact measurement_system_projectors_commute f h x y


-- Main lemma: Alice_A observables commute
lemma alice_observables_commute
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout}
  (strat : LCSStrategy R G) (i : Fin G.r) (j j' : G.V i) :
  (Alice_A strat i j) * (Alice_A strat i j') = (Alice_A strat i j') * (Alice_A strat i j) := by
  unfold Alice_A
  let A := ∑ x ∈ Finset.univ.filter (fun x => x j = 0), strat.E i x -- x_j = 0
  let B := ∑ x ∈ Finset.univ.filter (fun x => x j = 1), strat.E i x -- x_j = 1
  let C := ∑ x ∈ Finset.univ.filter (fun x => x j' = 0), strat.E i x -- x_j' = 0
  let D := ∑ x ∈ Finset.univ.filter (fun x => x j' = 1), strat.E i x -- x_j' = 1
  change (A - B) * (C - D) = (C - D) * (A - B)
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
  simp [mul_sub, sub_mul]
  simp [h_AC, h_AD, h_BC, h_BD]
  abel

/-- The Winning Operator `v` for a given Strategy and Game. -/
noncomputable def winning_operator
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G) : R :=
  -- We sum over all questions i (Alice) and j (Bob) where j is in Alice's set
  ∑ i : Fin G.r, ∑ j : G.V i,
  let normalization : ℂ := (G.r * (G.V i).card : ℕ)
  (1 / normalization) • (∑ x ∈ winning_assignments game i, strat.E i x * strat.F j (x j))



lemma lemma_4_7_1
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G)
  (i : Fin G.r) :
  (∑ x ∈ winning_assignments game i, strat.E i x) = 
  (1/2 : ℂ) • (1 + (-1 : ℂ)^(game.b i).val • 
  ((G.V i).attach.noncommProd 
    (fun j => Alice_A strat i j) 
    (fun j hj j' hj' _ => alice_observables_commute strat i j j'))) :=
  by sorry
