import LCS.Basic
import LCS.Observables
import Mathlib.Order.Fin.Basic

open scoped BigOperators

-- ANCHOR: winning_assignments
def winning_assignments
  {G : LCSLayout}
  (game : LCSGame G) (i : Fin G.r) :
  Finset (Assignment G i) :=
  Finset.univ.filter (fun α => (∑ j : G.V i, (α j : Fin 2)) = game.b i)
-- ANCHOR_END: winning_assignments


/-- The Winning Operator `v` for a given Strategy and Game. -/
noncomputable def winning_operator
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G) : R :=
  ∑ i : Fin G.r, ∑ j : G.V i,
  let normalization : ℂ := (G.r * (G.V i).card : ℕ)
  (1 / normalization) • (∑ x ∈ winning_assignments game i, strat.E i x * strat.F j (x j))


noncomputable def loss_operator
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G) : R :=
  1 - winning_operator game strat

private lemma fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  have hval : a.val = 0 ∨ a.val = 1 := by
    have hlt : a.val < 2 := a.is_lt
    omega
  rcases hval with h0 | h1
  · left
    exact Fin.ext h0
  · right
    exact Fin.ext h1

private lemma measurement_sum_mul_projector
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G)
  (i : Fin G.r) (S : Finset (Assignment G i)) (x : Assignment G i) :
  (∑ y ∈ S, strat.E i y) * strat.E i x =
    if x ∈ S then strat.E i x else 0 := by
  classical
  by_cases hx : x ∈ S
  · rw [if_pos hx, Finset.sum_mul, Finset.sum_eq_single_of_mem x hx]
    · simpa using (strat.alice_ms i).idempotent x
    · intro y hy hyx
      exact (strat.alice_ms i).orthogonal y x hyx
  · rw [if_neg hx, Finset.sum_mul, Finset.sum_eq_zero]
    intro y hy
    exact (strat.alice_ms i).orthogonal y x (by
      intro hyx
      apply hx
      simpa [hyx] using hy)

private lemma alice_A_mul_projector
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout}
  (strat : LCSStrategy R G) (i : Fin G.r)
  (j : G.V i) (x : Assignment G i) :
  Alice_A strat i j * strat.E i x = ((-1 : ℂ) ^ (x j).val) • strat.E i x := by
  classical
  unfold Alice_A
  by_cases hx0 : x j = 0
  · have hx1 : x j ≠ 1 := by simp [hx0]
    rw [sub_mul]
    rw [measurement_sum_mul_projector strat i _ x, measurement_sum_mul_projector strat i _ x]
    simp [Finset.mem_filter, hx0]
  · have hx1 : x j = 1 := by
      have hx_cases : x j = 0 ∨ x j = 1 := fin2_eq_zero_or_one (x j)
      rcases hx_cases with h | h
      · contradiction
      · exact h
    rw [sub_mul]
    rw [measurement_sum_mul_projector strat i _ x, measurement_sum_mul_projector strat i _ x]
    simp [Finset.mem_filter, hx1]

private lemma alice_partial_prod_mul_projector
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout}
  (strat : LCSStrategy R G) (i : Fin G.r)
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

private lemma prod_sign_eq_sum_sign
  {G : LCSLayout} (i : Fin G.r) (x : Assignment G i) :
  ((G.V i).attach.prod fun j => (-1 : ℂ) ^ (x j).val) =
    (-1 : ℂ) ^ ((∑ j : G.V i, (x j : Fin 2)).val) := by
  classical
  let s : Finset (G.V i) := (G.V i).attach
  change (s.prod fun j => (-1 : ℂ) ^ (x j).val) = (-1 : ℂ) ^ ((s.sum fun j => (x j : Fin 2)).val)
  induction s using Finset.cons_induction_on with
  | empty =>
      simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons, ih]
      have hxa_cases : x a = 0 ∨ x a = 1 := fin2_eq_zero_or_one (x a)
      rcases hxa_cases with hxa | hxa
      · simp [hxa]
      · let t : Fin 2 := s.sum fun j => (x j : Fin 2)
        have ht_cases : t = 0 ∨ t = 1 := fin2_eq_zero_or_one t
        rcases ht_cases with ht | ht <;> simp [hxa, t, ht]

/-- Arithmetic helper: the sign factor `(1/2)(1 + (-1)^b * (-1)^s)` equals the indicator `s = b`. -/
private lemma sign_indicator (b s : Fin 2) :
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ s.val = if s = b then 1 else 0 := by
  rcases fin2_eq_zero_or_one b with rfl | rfl <;>
  rcases fin2_eq_zero_or_one s with rfl | rfl <;>
  simp <;> norm_num

lemma lemma_4_7_1
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G)
  (i : Fin G.r) :
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

lemma lemma_4_7_2
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G)
  (i : Fin G.r) (j : G.V i) (y : Fin 2) :
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
  unfold Alice_A
  rcases fin2_eq_zero_or_one y with rfl | rfl
  · change A = _
    simp only [Fin.val_zero, pow_zero, one_smul]
    have hform : 1 + (A - B) = A + A := by rw [← hpart]; abel
    rw [hform, smul_add, ← add_smul]
    norm_num
  · change B = _
    simp only [Fin.val_one, pow_one]
    have hform : 1 + (-1 : ℂ) • (A - B) = B + B := by rw [← hpart]; module
    rw [hform, smul_add, ← add_smul]
    norm_num
