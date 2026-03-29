import LCS.Basic
import LCS.Observable
import LCS.Common
import LCS.Strategy.ProjectorStrategy
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel

/-!
# Winning Condition and Loss Operators

This module formalizes the concepts of winning and loss operators for an LCS game.
Specifically, it defines the probability of a strategy winning the game
and decomposes it into local contributions from each equation.

## Key Definitions
- `winning_assignments`: The set of local assignments that satisfy the $i$-th linear equation.
- `local_winning_operator`: The operator representing the success probability for a single variable in an equation.
- `winning_operator`: The average success probability across all variables and equations.
- `loss_operator`: The complement of the winning operator ($1 - v$).

## Key Theorems
- `lemma_4_7_1`: Relates the sum of Alice's winning projectors to the product of her observables.
- `lemma_4_7_2`: Connects Alice's marginal projectors to her observables.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

variable {G : LCSLayout} (game : LCSGame G)
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable (strat : LCSStrategy R G)

-- ANCHOR: winning_assignments
def winning_assignments (i : Fin G.r) : Finset (Assignment G i) :=
  Finset.univ.filter (fun α => (∑ j : G.V i, (α j : Fin 2)) = game.b i)
-- ANCHOR_END: winning_assignments

/-- The local winning probability for a single edge (i, j). -/
noncomputable def local_winning_operator (i : Fin G.r) (j : G.V i) : R :=
  ∑ x ∈ winning_assignments game i, strat.E i x * strat.F j (x j)

/-- The local loss operator for a single edge (i, j). -/
noncomputable def local_loss_operator (i : Fin G.r) (j : G.V i) : R :=
  1 - local_winning_operator game strat i j

/-- The total Winning Operator `v` is the average of local winning probabilities. -/
noncomputable def winning_operator : R :=
  ∑ i : Fin G.r, ∑ j : G.V i,
  let normalization : ℂ := (G.r * (G.V i).card : ℕ)
  (1 / normalization) • local_winning_operator game strat i j

/-- The total Loss Operator `1 - v`. -/
noncomputable def loss_operator : R :=
  1 - winning_operator game strat


private lemma measurement_sum_mul_projector (i : Fin G.r)
  (S : Finset (Assignment G i)) (x : Assignment G i) :
  (∑ y ∈ S, strat.E i y) * strat.E i x = if x ∈ S then strat.E i x else 0 := by
  classical
  split_ifs with hx
  · rw [Finset.sum_mul, Finset.sum_eq_single_of_mem x hx]
    · exact (strat.alice_ms i).idempotent x
    · intro y _ hyx; exact (strat.alice_ms i).orthogonal y x hyx
  · rw [Finset.sum_mul, Finset.sum_eq_zero]
    intro y hy
    exact (strat.alice_ms i).orthogonal y x (by rintro rfl; exact hx hy)

private lemma alice_A_mul_projector (i : Fin G.r)
  (j : G.V i) (x : Assignment G i) :
  Alice_A strat i j * strat.E i x = ((-1 : ℂ) ^ (x j).val) • strat.E i x := by
  classical
  unfold Alice_A ObservableOfMeasurementSystem InducedMeasurementSystem
  rw [sub_mul, measurement_sum_mul_projector, measurement_sum_mul_projector]
  match h : x j with
  | 0 => simp [h]
  | 1 => simp [h]

private lemma alice_partial_prod_mul_projector (i : Fin G.r)
  (s : Finset (G.V i)) (x : Assignment G i)
  (comm :
    (s : Set (G.V i)).Pairwise (fun j j' => Commute (Alice_A strat i j) (Alice_A strat i j'))) :
  s.noncommProd (fun j => Alice_A strat i j) comm * strat.E i x =
    (s.prod fun j => (-1 : ℂ) ^ (x j).val) • strat.E i x := by
  classical
  induction s using Finset.cons_induction_on with
  | empty =>
      simp
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Finset.prod_cons, mul_assoc, ih]
      · rw [Algebra.mul_smul_comm, alice_A_mul_projector]
        simp [smul_smul, mul_comm]


private lemma prod_sign_eq_sum_sign_aux {G : LCSLayout} {i : Fin G.r}
  (x : Assignment G i) (s : Finset (G.V i)) :
  (s.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((s.sum fun j => (x j : Fin 2)).val) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, sign_mul]

private lemma prod_sign_eq_sum_sign {G : LCSLayout} (i : Fin G.r) (x : Assignment G i) :
  ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((∑ j : G.V i, (x j : Fin 2)).val) :=
  prod_sign_eq_sum_sign_aux x _


lemma lemma_4_7_1 (i : Fin G.r) :
  (∑ x ∈ winning_assignments game i, strat.E i x) =
  (1/2 : ℂ) • (1 + (-1 : ℂ)^(game.b i).val •
  ((G.V i).attach.noncommProd
    (fun j => Alice_A strat i j)
    (fun j _ j' _ _ => alice_observables_commute strat i j j'))) := by
  classical
  have hsum_one := (strat.alice_ms i).sum_one
  let prodA : R := (G.V i).attach.noncommProd
    (fun j => Alice_A strat i j) (fun j _ j' _ _ => alice_observables_commute strat i j j')
  let rhs : R := (1/2 : ℂ) • (1 + (-1 : ℂ)^(game.b i).val • prodA)
  -- The key step: show per-projector equality, then sum
  suffices h : ∀ x : Assignment G i,
      (∑ y ∈ winning_assignments game i, strat.E i y) * strat.E i x = rhs * strat.E i x by
    calc ∑ x ∈ winning_assignments game i, strat.E i x
        = (∑ x ∈ winning_assignments game i, strat.E i x) * 1 := by exact (mul_one _).symm
      _ = (∑ x ∈ winning_assignments game i, strat.E i x) * ∑ x, strat.E i x := by rw [hsum_one]
      _ = ∑ x, (∑ y ∈ winning_assignments game i, strat.E i y) * strat.E i x :=
            by rw [Finset.mul_sum]
      _ = ∑ x, rhs * strat.E i x := by
            apply Finset.sum_congr rfl
            intro x _
            exact h x
      _ = rhs * ∑ x, strat.E i x := by rw [← Finset.mul_sum]
      _ = rhs := by rw [hsum_one, mul_one]
  intro x
  -- LHS
  rw [measurement_sum_mul_projector strat i (winning_assignments game i) x]
  -- RHS: expand
  have hprod : prodA * strat.E i x =
      ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) • strat.E i x :=
    alice_partial_prod_mul_projector strat i _ x
      (fun j _ j' _ _ => alice_observables_commute strat i j j')
  have hsign : ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) =
      (-1 : ℂ) ^ ((∑ j : G.V i, (x j : Fin 2)).val) :=
    prod_sign_eq_sum_sign i x
  -- Expand rhs * E i x
  -- Directly compute both sides and match via sign_indicator
  conv_rhs =>
    unfold rhs
    rw [smul_mul_assoc, add_mul, one_mul, smul_mul_assoc, hprod, hsign, smul_add,
        smul_smul, smul_smul, ← add_smul]
  have hsign2 : (1/2 : ℂ) + (1/2 : ℂ) * (-1 : ℂ) ^ (game.b i).val *
                  (-1 : ℂ) ^ (∑ j : G.V i, (x j : Fin 2)).val
        = if (∑ j : G.V i, (x j : Fin 2)) = game.b i then 1 else 0 := by
    exact sign_indicator (game.b i) (∑ j : G.V i, (x j : Fin 2))
  rw [hsign2]
  simp [winning_assignments, Finset.mem_filter]

lemma lemma_4_7_2 (i : Fin G.r) (j : G.V i) (y : Fin 2) :
  (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = y), strat.E i x) =
    (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • Alice_A strat i j) := by
  classical
  let A : R := ∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x
  let B : R := ∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), strat.E i x
  -- InducedMeasurementSystem.sum_one gives A + B = 1 directly,
  -- replacing the manual partition argument (hnot + hpart)
  have hind := induced_measurement_system_is_measurement_system
    (strat.E i) (strat.alice_ms i) (fun x => x j)
  have hpart : A + B = 1 := by
    have h := hind.sum_one
    rw [Fin.sum_univ_two] at h
    simp only [InducedMeasurementSystem] at h
    exact h
  unfold Alice_A ObservableOfMeasurementSystem InducedMeasurementSystem
  rcases fin2_eq_zero_or_one y with rfl | rfl
  · change A = _
    simp only [Fin.val_zero, pow_zero, one_smul]
    have hform : 1 + (A - B) = A + A := by rw [← hpart]; abel
    rw [hform, smul_add, ← add_smul]
    norm_num
  · change B = _
    simp only [Fin.val_one, pow_one]
    have hform : 1 + (-1 : ℂ) • (A - B) = B + B := by
      rw [← hpart]; simp only [neg_smul, one_smul]; abel
    rw [hform, smul_add, ← add_smul]
    norm_num

lemma bob_observable_sq (j : Fin G.s) :
  Bob_B strat j * Bob_B strat j = 1 :=
  (bob_is_observable strat j).involutive

lemma alice_observable_sq (i : Fin G.r) (j : G.V i) :
  Alice_A strat i j * Alice_A strat i j = 1 :=
  (alice_is_observable strat i j).involutive
