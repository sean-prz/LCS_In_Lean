import LCS.Basic

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


noncomputable def InducedMeasurementSystem {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq J] (f : I → R) (g : I → J) : J → R :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => g i = j), f i

lemma induced_measurement_system_is_measurement_system
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  (f : I → R) (h : IsMeasurementSystem f) (g : I → J) :
  IsMeasurementSystem (InducedMeasurementSystem f g) where
  sum_one := by
    dsimp [InducedMeasurementSystem]
    rw [Finset.sum_fiberwise Finset.univ g f, h.sum_one]
  idempotent j := by
    dsimp [InducedMeasurementSystem]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.mul_sum]
    have : ∑ i ∈ Finset.univ.filter (fun i => g i = j), f x * f i = f x * f x := by
      apply Finset.sum_eq_single x
      · intro y _ hxy; exact h.orthogonal x y hxy.symm
      · intro hnx; exact (hnx hx).elim
    rw [this, h.idempotent x]
  orthogonal j1 j2 hj := by
    dsimp [InducedMeasurementSystem]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero (fun x hx => ?_)
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero (fun y hy => ?_)
    apply h.orthogonal
    rintro rfl
    exact hj ((Finset.mem_filter.1 hx).2.symm.trans (Finset.mem_filter.1 hy).2)
  self_adjoint j := by
    dsimp [InducedMeasurementSystem]
    rw [star_sum]
    exact Finset.sum_congr rfl (fun x _ => h.self_adjoint x)


lemma measurement_commute {I} [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (x y : I) : Commute (f x) (f y) := by
  by_cases hxy : x = y
  · rw [hxy]
  · rw [Commute, SemiconjBy, h.orthogonal x y hxy, h.orthogonal y x (Ne.symm hxy)]

lemma measurement_commute_sum {I} [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (A B : Finset I) : Commute (∑ x ∈ A, f x) (∑ y ∈ B, f y) :=
  Commute.sum_left _ _ _ (fun x _ =>
    Commute.sum_right _ _ _ (fun y _ => measurement_commute h x y))


lemma measurement_intersection {I} [Fintype I] [DecidableEq I] {f : I → R}
    (h : IsMeasurementSystem f) (S T : Finset I) :
    (∑ x ∈ S, f x) * (∑ y ∈ T, f y) = ∑ x ∈ (S ∩ T), f x := by
  classical
  rw [Finset.sum_mul]
  have h_mul (x : I) : f x * ∑ y ∈ T, f y = if x ∈ T then f x else 0 := by
    rw [Finset.mul_sum]
    by_cases hxT : x ∈ T
    · rw [if_pos hxT]
      have : ∑ y ∈ T, f x * f y = f x * f x := by
        apply Finset.sum_eq_single x
        · intro b _ hb; exact h.orthogonal x b (Ne.symm hb)
        · intro hnx; exact (hnx hxT).elim
      rw [this, h.idempotent x]
    · rw [if_neg hxT]
      apply Finset.sum_eq_zero
      intro y hy
      apply h.orthogonal
      intro h_eq; subst h_eq; contradiction
  rw [Finset.sum_congr rfl (fun x _ => h_mul x)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_mem_eq_inter]
