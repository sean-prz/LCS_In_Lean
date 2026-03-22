import LCS.Basic

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



structure IsObservable
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (O : R) : Prop where
  involutive   : O * O = 1
  self_adjoint : star O = O


lemma measurement_commute {I R} [Ring R] [StarRing R] [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (x y : I) : Commute (f x) (f y) := by
  dsimp [Commute, SemiconjBy]
  by_cases hxy : x = y
  · rw [hxy]
  · rw [h.orthogonal x y hxy, h.orthogonal y x (Ne.symm hxy)]

lemma measurement_commute_sum {I R} [Ring R] [StarRing R] [Fintype I] {f : I → R}
  (h : IsMeasurementSystem f) (A B : Finset I) :
  Commute (∑ x ∈ A, f x) (∑ y ∈ B, f y) :=
  Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => measurement_commute h x y

lemma alice_observables_commute
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout}
  (strat : LCSStrategy R G) (i : Fin G.r) (j j' : G.V i) :
  Commute (Alice_A strat i j) (Alice_A strat i j') := by
  unfold Alice_A
  let comm := measurement_commute_sum (strat.alice_ms i)
  exact Commute.sub_left
    (Commute.sub_right (comm _ _) (comm _ _))
    (Commute.sub_right (comm _ _) (comm _ _))

def ObservableOfMeasurementSystem {R} [Ring R]
  (f : Fin 2 → R) : R :=
  f 0 - f 1

lemma is_observable_of_measurement_system {R} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (f : Fin 2 → R) (h : IsMeasurementSystem f) :
  IsObservable R (ObservableOfMeasurementSystem f) := by
  constructor
  · dsimp [ObservableOfMeasurementSystem]
    rw [sub_mul, mul_sub, mul_sub]
    rw [h.idempotent 0, h.idempotent 1]
    have h01 : f 0 * f 1 = 0 := h.orthogonal 0 1 (by decide)
    have h10 : f 1 * f 0 = 0 := h.orthogonal 1 0 (by decide)
    rw [h01, h10, sub_zero, zero_sub, sub_neg_eq_add]
    have hsum : ∑ x : Fin 2, f x = 1 := h.sum_one
    rw [Fin.sum_univ_two] at hsum
    exact hsum
  · dsimp [ObservableOfMeasurementSystem]
    rw [star_sub, h.self_adjoint 0, h.self_adjoint 1]

noncomputable def InducedMeasurementSystem {R} [Ring R] {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq J] (f : I → R) (g : I → J) : J → R :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => g i = j), f i

lemma induced_measurement_system_is_measurement_system {R} [Ring R] [StarRing R]
  {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  (f : I → R) (h : IsMeasurementSystem f) (g : I → J) :
  IsMeasurementSystem (InducedMeasurementSystem f g) := by
  constructor
  · dsimp [InducedMeasurementSystem]
    rw [Finset.sum_fiberwise Finset.univ g f]
    exact h.sum_one
  · intro j
    dsimp [InducedMeasurementSystem]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    have : ∑ i ∈ Finset.univ.filter (fun i => g i = j), f x * f i = f x * f x := by
      apply Finset.sum_eq_single x
      · intro y hy hxy
        exact h.orthogonal x y hxy.symm
      · intro hnx
        exact False.elim (hnx hx)
    rw [this, h.idempotent x]
  · intro j1 j2 hj
    dsimp [InducedMeasurementSystem]
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro y hy
    rw [Finset.mem_filter] at hx hy
    have hxy : x ≠ y := by
      rintro rfl
      rw [←hx.2, ←hy.2] at hj
      exact hj rfl
    exact h.orthogonal x y hxy
  · intro j
    dsimp [InducedMeasurementSystem]
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact h.self_adjoint x

lemma bob_is_observable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G) (j : Fin G.s) :
  IsObservable R (Bob_B strat j) := by
  exact is_observable_of_measurement_system (strat.F j) (strat.bob_ms j)

lemma alice_is_observable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) :
  IsObservable R (Alice_A strat i j) := by
  have hind := induced_measurement_system_is_measurement_system (strat.E i)
    (strat.alice_ms i) (fun x => x j)
  exact is_observable_of_measurement_system _ hind
