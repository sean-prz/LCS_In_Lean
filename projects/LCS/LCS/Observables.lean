import LCS.Basic

noncomputable def InducedMeasurementSystem {R} [Ring R] {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq J] (f : I → R) (g : I → J) : J → R :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => g i = j), f i

lemma induced_measurement_system_is_measurement_system {R} [Ring R] [StarRing R]
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

def ObservableOfMeasurementSystem {R} [Ring R] (f : Fin 2 → R) : R :=
  f 0 - f 1

structure IsObservable (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (O : R) : Prop where
  involutive   : O * O = 1
  self_adjoint : star O = O

lemma is_observable_of_measurement_system {R} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (f : Fin 2 → R) (h : IsMeasurementSystem f) :
  IsObservable R (ObservableOfMeasurementSystem f) where
  involutive := by
    dsimp [ObservableOfMeasurementSystem]
    rw [sub_mul, mul_sub, mul_sub, h.idempotent 0, h.idempotent 1]
    rw [h.orthogonal 0 1 (by decide), h.orthogonal 1 0 (by decide)]
    rw [sub_zero, zero_sub, sub_neg_eq_add]
    exact (Fin.sum_univ_two f).symm.trans h.sum_one
  self_adjoint := by
    dsimp [ObservableOfMeasurementSystem]
    rw [star_sub, h.self_adjoint 0, h.self_adjoint 1]

-- ANCHOR: Alice_A
/-
noncomputable def Alice_A
  {G : LCSLayout}
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment G i) => x j = 0), strat.E i x) -
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment G i) => x j = 1), strat.E i x)
-/
noncomputable def Alice_A {G : LCSLayout} {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  ObservableOfMeasurementSystem (InducedMeasurementSystem (strat.E i) (fun x => x j))
-- ANCHOR_END: Alice_A

-- ANCHOR: Bob_B
/-
def Bob_B
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout}
  (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  strat.F j 0 - strat.F j 1
-/
def Bob_B {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] {G : LCSLayout}
  (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  ObservableOfMeasurementSystem (strat.F j)
-- ANCHOR_END: Bob_B

lemma bob_is_observable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G) (j : Fin G.s) :
  IsObservable R (Bob_B strat j) :=
  is_observable_of_measurement_system (strat.F j) (strat.bob_ms j)

lemma alice_is_observable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) :
  IsObservable R (Alice_A strat i j) :=
  is_observable_of_measurement_system _
    (induced_measurement_system_is_measurement_system _ (strat.alice_ms i) _)

private lemma measurement_commute {I R} [Ring R] [StarRing R] [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (x y : I) : Commute (f x) (f y) := by
  by_cases hxy : x = y
  · rw [hxy]
  · rw [Commute, SemiconjBy, h.orthogonal x y hxy, h.orthogonal y x (Ne.symm hxy)]

private lemma measurement_commute_sum {I R} [Ring R] [StarRing R] [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (A B : Finset I) : Commute (∑ x ∈ A, f x) (∑ y ∈ B, f y) :=
  Commute.sum_left _ _ _ (fun x _ =>
    Commute.sum_right _ _ _ (fun y _ => measurement_commute h x y))

lemma alice_observables_commute {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] {G : LCSLayout}
  (strat : LCSStrategy R G) (i : Fin G.r) (j j' : G.V i) :
  Commute (Alice_A strat i j) (Alice_A strat i j') := by
  let comm := measurement_commute_sum (strat.alice_ms i)
  exact Commute.sub_left (Commute.sub_right (comm _ _) (comm _ _))
    (Commute.sub_right (comm _ _) (comm _ _))
