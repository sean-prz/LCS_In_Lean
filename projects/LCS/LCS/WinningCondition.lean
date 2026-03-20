import LCS.Basic
import LCS.MeasurementLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Fin.Basic

open scoped BigOperators

-- ANCHOR: winning_assignments
def winning_assignments
  {G : LCSLayout}
  (game : LCSGame G) (i : Fin G.r) : 
  Finset (Assignment G i) :=
  Finset.univ.filter (fun α => (∑ j : G.V i , (α j : ZMod 2)) = game.b i)
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

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hval : a.val = 0 ∨ a.val = 1 := by
    have hlt : a.val < 2 := ZMod.val_lt a
    omega
  rcases hval with h0 | h1
  · exact Or.inl ((ZMod.val_eq_zero a).mp h0)
  · exact Or.inr <| by
      have ha : ((a.val : ZMod 2) = a) := ZMod.natCast_zmod_val a
      rw [h1] at ha
      simpa [eq_comm] using ha

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
    (-1 : ℂ) ^ ((∑ j : G.V i, (x j : ZMod 2)).val) := by
  classical
  let s : Finset (G.V i) := (G.V i).attach
  change (s.prod fun j => (-1 : ℂ) ^ (x j).val) = (-1 : ℂ) ^ ((s.sum fun j => (x j : ZMod 2)).val)
  induction s using Finset.cons_induction_on with
  | empty =>
      simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons, ih]
      have hxa_cases : x a = 0 ∨ x a = 1 := fin2_eq_zero_or_one (x a)
      rcases hxa_cases with hxa | hxa
      · simp [hxa]
      · let t : ZMod 2 := s.sum fun j => (x j : ZMod 2)
        have ht_cases : t = 0 ∨ t = 1 := zmod2_eq_zero_or_one t
        rcases ht_cases with ht | ht <;> simp [hxa, t, ht]

lemma lemma_4_7_1
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G)
  (i : Fin G.r) :
  (∑ x ∈ winning_assignments game i, strat.E i x) = 
  (1/2 : ℂ) • (1 + (-1 : ℂ)^(game.b i).val • 
  ((G.V i).attach.noncommProd 
    (fun j => Alice_A strat i j) 
    (fun j _ j' _ _ => alice_observables_commute strat i j j'))) :=
  by
    classical
    let lhs : R := ∑ x ∈ winning_assignments game i, strat.E i x
    let prodA : R :=
      (G.V i).attach.noncommProd
        (fun j => Alice_A strat i j)
        (fun j hj j' hj' _ => alice_observables_commute strat i j j')
    let rhs : R := (1/2 : ℂ) • (1 + (-1 : ℂ)^(game.b i).val • prodA)
    have hsum_one := (strat.alice_ms i).sum_one
    change lhs = rhs
    calc
      lhs = lhs * 1 := by simp [lhs]
      _ = lhs * (∑ x : Assignment G i, strat.E i x) := by rw [hsum_one]
      _ = ∑ x : Assignment G i, lhs * strat.E i x := by rw [Finset.mul_sum]
      _ = ∑ x : Assignment G i, rhs * strat.E i x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hlhs :
            lhs * strat.E i x =
              if x ∈ winning_assignments game i then strat.E i x else 0 := by
          unfold lhs
          simpa using measurement_sum_mul_projector strat i (winning_assignments game i) x
        have hprod :
            prodA * strat.E i x =
              (((G.V i).attach).prod fun j => (-1 : ℂ) ^ (x j).val) • strat.E i x := by
          unfold prodA
          simpa using alice_partial_prod_mul_projector strat i (G.V i).attach x
            (fun j hj j' hj' hne => alice_observables_commute strat i j j')
        have hsign :
            (((G.V i).attach).prod fun j => (-1 : ℂ) ^ (x j).val) =
              (-1 : ℂ) ^ ((∑ j : G.V i, (x j : ZMod 2)).val) := by
          simpa using prod_sign_eq_sum_sign i x
        have hrhs :
            rhs * strat.E i x =
              ((1/2 : ℂ) * (1 + (-1 : ℂ)^(game.b i).val *
                (-1 : ℂ) ^ ((∑ j : G.V i, (x j : ZMod 2)).val))) • strat.E i x := by
          unfold rhs
          rw [smul_mul_assoc, add_mul, one_mul, smul_mul_assoc, hprod, hsign]
          rw [smul_add, smul_smul, smul_smul]
          rw [← add_smul]
          congr 1
          ring
        rw [hlhs, hrhs]
        by_cases hwin : x ∈ winning_assignments game i
        · have hEq : (∑ j : G.V i, (x j : ZMod 2)) = game.b i := by
            simpa [winning_assignments, Finset.mem_filter] using hwin
          have hval : ((∑ j : G.V i, (x j : ZMod 2)).val) = (game.b i).val := by
            simpa using congrArg (fun z : ZMod 2 => z.val) hEq
          rw [if_pos hwin, hval]
          have hb_cases : game.b i = 0 ∨ game.b i = 1 := zmod2_eq_zero_or_one (game.b i)
          rcases hb_cases with hb | hb
          · simp [hb]
            norm_num
          · simp [hb]
            have hval1 : ((1 : ZMod 2).val) = 1 := by decide
            norm_num [hval1]
        · have hne : (∑ j : G.V i, (x j : ZMod 2)) ≠ game.b i := by
            simpa [winning_assignments, Finset.mem_filter] using hwin
          have hsum_cases :
              (∑ j : G.V i, (x j : ZMod 2)) = 0 ∨ (∑ j : G.V i, (x j : ZMod 2)) = 1 := by
            exact zmod2_eq_zero_or_one (∑ j : G.V i, (x j : ZMod 2))
          have hb_cases : game.b i = 0 ∨ game.b i = 1 := by
            exact zmod2_eq_zero_or_one (game.b i)
          rw [if_neg hwin]
          rcases hsum_cases with hsum | hsum <;> rcases hb_cases with hb | hb
          · exact False.elim (hne (hsum.trans hb.symm))
          · have hval1 : ((1 : ZMod 2).val) = 1 := by decide
            rw [hsum, hb]
            norm_num [hval1]
          · rw [hsum, hb]
            norm_num
          · exact False.elim (hne (hsum.trans hb.symm))
      _ = rhs * (∑ x : Assignment G i, strat.E i x) := by rw [← Finset.mul_sum]
      _ = rhs * 1 := by rw [hsum_one]
      _ = rhs := by simp

lemma lemma_4_7_2
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G)
  (i : Fin G.r) (j : G.V i) (y : Fin 2) :
  (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = y), strat.E i x) =
    (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • Alice_A strat i j) := by
  classical
  unfold Alice_A
  set A : R := ∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x
  set B : R := ∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), strat.E i x
  have hsum_one := (strat.alice_ms i).sum_one
  have hnot :
      Finset.univ.filter (fun x : Assignment G i => ¬ x j = 0) =
        Finset.univ.filter (fun x : Assignment G i => x j = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rcases fin2_eq_zero_or_one (x j) with h0 | h1
      · exact False.elim (hx h0)
      · exact h1
    · intro hx
      simp [hx]
  have hpart : A + B = 1 := by
    dsimp [A, B]
    calc
      (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x) +
          (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), strat.E i x)
          =
            (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x) +
            (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => ¬ x j = 0), strat.E i x) := by
              rw [hnot]
      _ = ∑ x : Assignment G i, strat.E i x := by
            rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
              (f := fun x : Assignment G i => strat.E i x) (p := fun x => x j = 0)]
      _ = 1 := hsum_one
  rcases fin2_eq_zero_or_one y with rfl | rfl
  · have hA : A = (1 / 2 : ℂ) • (A + A) := by
      symm
      calc
        (1 / 2 : ℂ) • (A + A) = (1 / 2 : ℂ) • A + (1 / 2 : ℂ) • A := by rw [smul_add]
        _ = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • A := by rw [← add_smul]
        _ = A := by norm_num
    have hform : 1 + (A - B) = A + A := by
      rw [← hpart]
      abel
    calc
      (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x) = A := by rfl
      _ = (1 / 2 : ℂ) • (A + A) := hA
      _ = (1 / 2 : ℂ) • (1 + (A - B)) := by rw [hform]
      _ = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (0 : Fin 2).val • (A - B)) := by simp
      _ = (1 / 2 : ℂ) •
            (1 + (-1 : ℂ) ^ (0 : Fin 2).val •
              ((∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x) -
               (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), strat.E i x))) := by
            simp [A, B]
  · have hB : B = (1 / 2 : ℂ) • (B + B) := by
      symm
      calc
        (1 / 2 : ℂ) • (B + B) = (1 / 2 : ℂ) • B + (1 / 2 : ℂ) • B := by rw [smul_add]
        _ = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • B := by rw [← add_smul]
        _ = B := by norm_num
    have hform : 1 + (-1 : ℂ) • (A - B) = B + B := by
      rw [← hpart]
      simp
      abel
    calc
      (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), strat.E i x) = B := by rfl
      _ = (1 / 2 : ℂ) • (B + B) := hB
      _ = (1 / 2 : ℂ) • (1 + (-1 : ℂ) • (A - B)) := by rw [hform]
      _ = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (1 : Fin 2).val • (A - B)) := by simp
      _ = (1 / 2 : ℂ) •
            (1 + (-1 : ℂ) ^ (1 : Fin 2).val •
              ((∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 0), strat.E i x) -
               (∑ x ∈ Finset.univ.filter (fun x : Assignment G i => x j = 1), strat.E i x))) := by
            simp [A, B]
