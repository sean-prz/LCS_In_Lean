import LCS.Basic

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

