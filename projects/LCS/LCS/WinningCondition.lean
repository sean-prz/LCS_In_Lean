import LCS.Basic
import LCS.Observable
import LCS.Common
import LCS.Strategy.ProjectorStrategy
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Winning Condition and Loss Operators

This module formalizes the concepts of winning and loss operators for an LCS game.
Specifically, it defines the probability of a strategy winning the game
and decomposes it into local contributions from each equation.

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

-- Helper: Alice and Bob observables always commute (generalized)
private lemma alice_bob_commute_gen (i : Fin G.r) (k : G.V i)
    (j_var : Fin G.s) :
    Commute (Alice_A strat i k) (Bob_B strat j_var) := by
  unfold Alice_A Bob_B ObservableOfMeasurementSystem
    InducedMeasurementSystem
  apply Commute.sub_left <;> apply Commute.sub_right
  all_goals {
    apply Commute.sum_left; intro x _; apply strat.commute }

-- Helper: Bob observable commutes with Alice row product
private lemma bob_commute_row_prod (i : Fin G.r) (j : G.V i) :
    Commute B[j] (Alice_Row_Prod strat i) := by
  unfold Alice_Row_Prod
  apply Finset.noncommProd_commute
  intro k _
  exact (alice_bob_commute_gen strat i k j).symm

-- Helper: Alice observable commutes with Alice row product
private lemma alice_commute_row_prod (i : Fin G.r)
    (j : G.V i) :
    Commute (Alice_A strat i j)
      (Alice_Row_Prod strat i) := by
  unfold Alice_Row_Prod
  apply Finset.noncommProd_commute
  intro k _
  exact alice_observables_commute strat i j k

-- Helper: Alice row product is involutive (RP² = 1)
private lemma row_prod_sq (i : Fin G.r) :
    Alice_Row_Prod strat i *
      Alice_Row_Prod strat i = 1 := by
  have hsum := (strat.alice_ms i).sum_one
  have hcomm :
      (((G.V i).attach : Set (G.V i)).Pairwise
        (fun j j' =>
          Commute (Alice_A strat i j)
            (Alice_A strat i j'))) :=
    fun j _ j' _ _ =>
      alice_observables_commute strat i j j'
  suffices h : ∀ x : Assignment G i,
      Alice_Row_Prod strat i *
        Alice_Row_Prod strat i *
          strat.E i x = strat.E i x by
    calc Alice_Row_Prod strat i *
          Alice_Row_Prod strat i
        = _ * 1 := (mul_one _).symm
      _ = _ * ∑ x, strat.E i x := by rw [hsum]
      _ = ∑ x, _ * strat.E i x :=
          Finset.mul_sum _ _ _
      _ = ∑ x, strat.E i x := by
          apply Finset.sum_congr rfl
          intro x _; exact h x
      _ = 1 := hsum
  intro x
  unfold Alice_Row_Prod
  rw [mul_assoc,
      alice_partial_prod_mul_projector strat i _ x hcomm,
      Algebra.mul_smul_comm,
      alice_partial_prod_mul_projector strat i _ x hcomm,
      smul_smul]
  simp only [← Finset.prod_mul_distrib, ← pow_add, ← two_mul, pow_mul,
             neg_one_sq, one_pow, Finset.prod_const_one, one_smul]

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

private lemma local_loss_sos_step4 (i : Fin G.r) (j : G.V i) :
    1 - (1 / 4 : ℂ) • ∑ y : Fin 2,
      F[j, y] * (1 + (-1 : ℂ) ^ y.val • A[i, j] +
                 (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i +
                 ((-1 : ℂ) ^ y.val * (-1 : ℂ) ^ (b[i]).val) •
                   (Alice_Row_Prod strat i * A[i, j])) =
    1 - (1 / 4 : ℂ) • (1 + B[j] * A[i, j] +
                         (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i +
                         B[j] * ((-1 : ℂ) ^ (b[i]).val • (Alice_Row_Prod strat i * A[i, j]))) := by
  congr 1; congr 1
  -- Split ∑ y : Fin 2 into y = 0 and y = 1
  rw [Fin.sum_univ_two]
  -- (-1)^0 = 1, (-1)^1 = -1
  simp only [Fin.val_zero, pow_zero, one_smul, one_mul,
             Fin.val_one, pow_one, neg_smul, neg_mul]
  -- B[j] = F[j, 0] - F[j, 1]  (by definition)
  have hbob : B[j] = strat.F (↑j) 0 - strat.F (↑j) 1 :=
    show ObservableOfMeasurementSystem (strat.F (↑j)) = _ by
      simp [ObservableOfMeasurementSystem]
  -- F[j, 0] + F[j, 1] = 1
  have hone : strat.F (↑j) 0 + strat.F (↑j) 1 = 1 := by
    have h := (strat.bob_ms (↑j)).sum_one
    rw [Fin.sum_univ_two] at h; exact h
  -- Abbreviate for readability
  set F0 := strat.F (↑j) 0
  set F1 := strat.F (↑j) 1
  set Aj := A[i, j]
  set RP := Alice_Row_Prod strat i
  set c := (-1 : ℂ) ^ (b[i]).val
  -- Distribute F * (four-term sum) and normalize negations
  simp only [mul_add, mul_neg, mul_smul_comm]
  -- Collect the 4 pairs using auxiliary identities
  have h1 : F0 * (1 : R) + F1 * 1 = 1 := by rw [mul_one, mul_one, hone]
  have h2 : F0 * Aj + -(F1 * Aj) = B[↑j] * Aj := by
    rw [← sub_eq_add_neg, ← sub_mul, ← hbob]
  have h3 : c • (F0 * RP) + c • (F1 * RP) = c • RP := by
    rw [← smul_add, ← add_mul, hone, one_mul]
  have h4 : c • (F0 * (RP * Aj)) + -(c • (F1 * (RP * Aj))) =
      c • (B[↑j] * (RP * Aj)) := by
    rw [← sub_eq_add_neg, ← smul_sub, ← sub_mul, ← hbob]
  -- Rearrange the 8 terms into the 4 pairs and apply the identities
  calc F0 * 1 + F0 * Aj + c • (F0 * RP) + c • (F0 * (RP * Aj)) +
       (F1 * 1 + -(F1 * Aj) + c • (F1 * RP) + -(c • (F1 * (RP * Aj))))
      = (F0 * 1 + F1 * 1) + (F0 * Aj + -(F1 * Aj)) +
        (c • (F0 * RP) + c • (F1 * RP)) +
        (c • (F0 * (RP * Aj)) + -(c • (F1 * (RP * Aj)))) := by abel
    _ = 1 + B[↑j] * Aj + c • RP + c • (B[↑j] * (RP * Aj)) := by
        rw [h1, h2, h3, h4]

-- Step 5: final algebraic simplification to SOS form
private lemma local_loss_sos_step5 (i : Fin G.r)
    (j : G.V i) :
    1 - (1 / 4 : ℂ) • (1 + B[j] * A[i, j] +
      (-1 : ℂ) ^ (b[i]).val •
        Alice_Row_Prod strat i +
      B[j] * ((-1 : ℂ) ^ (b[i]).val •
        (Alice_Row_Prod strat i * A[i, j]))) =
    (1/8 : ℂ) • (
      (1 - B[j] * A[i, j])^2 +
      (1 - (-1 : ℂ )^(b[i]).val •
        Alice_Row_Prod strat i)^2 +
      (1 - (-1 : ℂ)^(b[i]).val •
        (Alice_Row_Prod strat i *
          A[i, j] * B[j]))^2) := by
  -- Define O1, O2, O3 to make the expression more readable
  let O1 := B[j] * A[i, j]
  let O2 := (-1 : ℂ) ^ (b[i]).val • Alice_Row_Prod strat i
  let O3 := (-1 : ℂ) ^ (b[i]).val • (Alice_Row_Prod strat i * A[i, j] * B[j])

  -- Rearange to be able to rewrite in terms of O1, O2, O3
  rw [mul_smul_comm]
  rw [← mul_assoc]
  rw [(bob_commute_row_prod strat i j).eq]
  rw [mul_assoc]
  nth_rw 2  [(alice_bob_commute_gen strat i j j).symm.eq]
  rw [← mul_assoc]

  -- Perform the rewriting in terms of O1, O2, O3
  change 1 - (1 / 4 : ℂ) • (1 + O1 + O2 + O3) = (1/8 : ℂ) • ((1 - O1)^2 + (1 - O2)^2 + (1 - O3)^2)

  -- Lemmas about O1, O2, O3
  have hO1 : O1 * O1 = 1 := by sorry
  have hO2 : O2 * O2 = 1 := by sorry
  have hO3 : O3 * O3 = 1 := by sorry

  -- expand the square on RHS
  simp only [sq, sub_mul, mul_sub, one_mul, mul_one]
  rw [hO1, hO2, hO3]
  noncomm_ring





  sorry

/-- The Sum of Squares decomposition of the local loss operator. -/
theorem local_loss_sos (i : Fin G.r) (j : G.V i) :
  local_loss_operator game strat i j =
    (1/8 : ℂ) • (
      (1 - B[j] * A[i, j])^2 +
      (1 - (-1)^(b[i]).val • Alice_Row_Prod strat i)^2 +
      (1 - (-1)^(b[i]).val • (Alice_Row_Prod strat i * A[i, j] * B[j]))^2
    ) := by
  rw [local_loss_sos_step1 game strat i j,
      local_loss_sos_step2 game strat i j,
      local_loss_sos_step3 game strat i j,
      local_loss_sos_step4 game strat i j,
      local_loss_sos_step5 game strat i j]
