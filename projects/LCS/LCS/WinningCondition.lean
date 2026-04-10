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

local notation "A[" i ", " j "]" => Alice_A strat i j
local notation "B[" j "]" => Bob_B strat j
local notation "E[" i ", " x "]" => strat.E i x
local notation "F[" j ", " y "]" => strat.F j y
local notation "b[" i "]" => game.b i

-- ANCHOR: winning_assignments
def winning_assignments (i : Fin G.r) : Finset (Assignment G i) :=
  Finset.univ.filter (fun α => (∑ j : G.V i, (α j : Fin 2)) = b[i])
-- ANCHOR_END: winning_assignments

local notation "S[" i "]" => winning_assignments game i

/-- The local winning probability for a single edge (i, j). -/
noncomputable def local_winning_operator (i : Fin G.r) (j : G.V i) : R :=
  ∑ x ∈ S[i], E[i, x] * F[j, x j]

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
  (∑ y ∈ S, E[i, y]) * E[i, x] = if x ∈ S then E[i, x] else 0 := by
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
  A[i, j] * E[i, x] = ((-1 : ℂ) ^ (x j).val) • E[i, x] := by
  classical
  unfold Alice_A ObservableOfMeasurementSystem InducedMeasurementSystem
  rw [sub_mul, measurement_sum_mul_projector, measurement_sum_mul_projector]
  match h : x j with
  | 0 => simp [h]
  | 1 => simp [h]

private lemma alice_partial_prod_mul_projector (i : Fin G.r)
  (s : Finset (G.V i)) (x : Assignment G i)
  (comm :
    (s : Set (G.V i)).Pairwise (fun j j' => Commute A[i, j] A[i, j'])) :
  s.noncommProd (fun j => A[i, j]) comm * E[i, x] =
    (s.prod fun j => (-1 : ℂ) ^ (x j).val) • E[i, x] := by
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
  (∑ x ∈ S[i], E[i, x]) =
  (1/2 : ℂ) • (1 + (-1 : ℂ)^(b[i]).val •
  ((G.V i).attach.noncommProd
    (fun j => A[i, j])
    (fun j _ j' _ _ => alice_observables_commute strat i j j'))) := by
  classical
  have hsum_one := (strat.alice_ms i).sum_one
  let prodA : R := (G.V i).attach.noncommProd
    (fun j => A[i, j]) (fun j _ j' _ _ => alice_observables_commute strat i j j')
  let rhs : R := (1/2 : ℂ) • (1 + (-1 : ℂ)^(b[i]).val • prodA)
  -- The key step: show per-projector equality, then sum
  suffices h : ∀ x : Assignment G i,
      (∑ y ∈ S[i], E[i, y]) * E[i, x] = rhs * E[i, x] by
    calc ∑ x ∈ S[i], E[i, x]
        = (∑ x ∈ S[i], E[i, x]) * 1 := by exact (mul_one _).symm
      _ = (∑ x ∈ S[i], E[i, x]) * ∑ x, E[i, x] := by rw [hsum_one]
      _ = ∑ x, (∑ y ∈ S[i], E[i, y]) * E[i, x] :=
            by rw [Finset.mul_sum]
      _ = ∑ x, rhs * E[i, x] := by
            apply Finset.sum_congr rfl
            intro x _
            exact h x
      _ = rhs * ∑ x, E[i, x] := by rw [← Finset.mul_sum]
      _ = rhs := by rw [hsum_one, mul_one]
  intro x
  -- LHS
  rw [measurement_sum_mul_projector strat i S[i] x]
  -- RHS: expand
  have hprod : prodA * E[i, x] =
      ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) • E[i, x] :=
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
  have hsign2 : (1/2 : ℂ) + (1/2 : ℂ) * (-1 : ℂ) ^ (b[i]).val *
                  (-1 : ℂ) ^ (∑ j : G.V i, (x j : Fin 2)).val
        = if (∑ j : G.V i, (x j : Fin 2)) = b[i] then 1 else 0 := by
    exact sign_indicator (b[i]) (∑ j : G.V i, (x j : Fin 2))
  rw [hsign2]
  simp [winning_assignments, Finset.mem_filter]

lemma lemma_4_7_2 (i : Fin G.r) (j : G.V i) (y : Fin 2) :
  (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = y), E[i, x]) =
    (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • A[i, j]) := by
  classical
  let A : R := ∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), E[i, x]
  let B : R := ∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), E[i, x]
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
  B[j] * B[j] = 1 :=
  (bob_is_observable strat j).involutive

lemma alice_observable_sq (i : Fin G.r) (j : G.V i) :
  A[i, j] * A[i, j] = 1 :=
  (alice_is_observable strat i j).involutive

/-- The product of Alice's observables for all variables in equation `i`. -/
noncomputable def Alice_Row_Prod (i : Fin G.r) : R :=
  (G.V i).attach.noncommProd (fun j => A[i, j]) (fun j _ j' _ _ => alice_observables_commute strat i j j')

/-- The Sum of Squares decomposition of the local loss operator. -/
theorem local_loss_sos (i : Fin G.r) (j : G.V i) :
  local_loss_operator game strat i j =
    (1/8 : ℂ) • (
      (1 - B[j] * A[i, j])^2 +
      (1 - (-1)^(b[i]).val • Alice_Row_Prod strat i)^2 +
      (1 - (-1)^(b[i]).val • (Alice_Row_Prod strat i * A[i, j] * B[j]))^2
    ) := by

  sorry

-- Below we build each individual step of local_loss_sos
private lemma local_loss_sos_step1 (i : Fin G.r) (j : G.V i) :
  local_loss_operator game strat i j =
    1 - ∑ y : Fin 2, F[j, y] * (∑ x ∈ S[i].filter (fun x => x j = y), E[i, x]) := by
  unfold local_loss_operator local_winning_operator
  congr 1
  rw [show (∑ y : Fin 2, F[j, y] * (∑ x ∈ S[i].filter (fun x => x j = y), E[i, x]))
      = ∑ y : Fin 2, ∑ x ∈ S[i].filter (fun x => x j = y), E[i, x] * F[j, y] by
    congr 1; ext y
    rw [Finset.mul_sum]
    congr 1; ext x
    exact (strat.commute i ↑j x y).symm]
  rw [← Finset.sum_fiberwise S[i] (fun x => x j) (fun x => E[i, x] * F[j, x j])]
  congr 1; ext y
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_filter] at hx
  rw [hx.2]

private lemma local_loss_sos_step2 (i : Fin G.r) (j : G.V i) :
    1 - ∑ y : Fin 2, F[j, y] * (∑ x ∈ S[i].filter (fun x => x j = y), E[i, x]) =
    1 - (1 / 4 : ℂ) • ∑ y : Fin 2,
      F[j, y] * ((1 + (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i) *
                 (1 + (-1 : ℂ) ^ y.val • A[i, j])) := by
  classical
  congr 1
  -- Pull (1/4) scalar inside the RHS sum
  rw [Finset.smul_sum]
  -- Now both sides are ∑ y, ...; prove pointwise
  apply Finset.sum_congr rfl
  intro y _
  -- Rewrite the filtered sum as intersection via measurement_intersection
  -- S[i].filter (x j = y) = S[i] ∩ univ.filter (x j = y)
  have hfilt : S[i].filter (fun x => x j = y) =
      S[i] ∩ Finset.univ.filter (fun x => x j = y) := by
    ext x; simp [winning_assignments, Finset.mem_filter, Finset.mem_inter]
  rw [hfilt, ← measurement_intersection (strat.alice_ms i)]
  -- Apply lemma_4_7_1 and lemma_4_7_2
  rw [lemma_4_7_2 strat i j y]
  have h471 := lemma_4_7_1 game strat i
  rw [show ∑ x ∈ S[i], E[i, x] = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i)
      from h471]
  -- Simplify: F * ((1/2 • P) * (1/2 • Q)) = (1/4) • (F * (P * Q))
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_assoc]
  norm_num [mul_assoc]

private lemma local_loss_sos_step3 (i : Fin G.r) (j : G.V i) :
    1 - (1 / 4 : ℂ) • ∑ y : Fin 2,
      F[j, y] * ((1 + (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i) *
                 (1 + (-1 : ℂ) ^ y.val • A[i, j])) =
    1 - (1 / 4 : ℂ) • ∑ y : Fin 2,
      F[j, y] * (1 + (-1 : ℂ) ^ y.val • A[i, j] +
                 (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i +
                 ((-1 : ℂ) ^ y.val * (-1 : ℂ) ^ (b[i]).val) •
                   (Alice_Row_Prod strat i * A[i, j])) := by
  congr 1
  -- Strip (1/4) • scalar from both sides
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  -- Expand (1 + c_b • P) * (1 + c_y • A) by bilinearity,
  -- then reorder the four additive summands with abel.
  simp only [add_mul, mul_add, one_mul, mul_one,
             smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
  abel
