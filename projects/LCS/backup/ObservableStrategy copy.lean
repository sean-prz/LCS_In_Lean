import LCS.Basic
import LCS.Observables
import Mathlib.Algebra.Star.Module

open scoped BigOperators

namespace ObservableStrategy

structure ObservableStrategyData
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (G : LCSLayout) where
  obs : Fin G.s → R
  observable : ∀ j, IsObservable (obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))

lemma half_smul_two
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] :
    (1 / 2 : ℂ) • (2 : R) = 1 := by
  rw [show (2 : R) = (2 : ℕ) • (1 : R) by simp]
  rw [two_nsmul, smul_add]
  rw [← add_smul]
  norm_num

lemma quarter_smul_two
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] :
    (1 / 4 : ℂ) • (2 : R) = (1 / 2 : ℂ) • (1 : R) := by
  rw [show (2 : R) = (2 : ℕ) • (1 : R) by simp]
  rw [two_nsmul, smul_add]
  rw [← add_smul]
  norm_num

lemma quarter_smul_two_mul
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (O : R) :
    (1 / 4 : ℂ) • ((2 : R) * O) = (1 / 2 : ℂ) • O := by
  rw [two_mul, smul_add]
  rw [← add_smul]
  norm_num

lemma two_invQuarter_smul
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (x : R) :
    (2 : ℕ) • (((2⁻¹ : ℂ) * 2⁻¹) • x) = (1 / 2 : ℂ) • x := by
  calc
    (2 : ℕ) • (((2⁻¹ : ℂ) * 2⁻¹) • x)
        = (((2⁻¹ : ℂ) * 2⁻¹) • x) + (((2⁻¹ : ℂ) * 2⁻¹) • x) := by rw [two_nsmul]
    _ = ((((2⁻¹ : ℂ) * 2⁻¹) + ((2⁻¹ : ℂ) * 2⁻¹)) : ℂ) • x := by rw [← add_smul]
    _ = (1 / 2 : ℂ) • x := by norm_num

lemma observableToProjector_sum
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (O : R) :
    ObservableToProjector O 0 + ObservableToProjector O 1 = 1 := by
  simp [ObservableToProjector, observableSign, smul_add]
  abel_nf
  simpa using (half_smul_two (R := R))

lemma observableToProjector_idempotent
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {O : R} (hO : IsObservable R O) (a : Fin 2) :
    ObservableToProjector O a * ObservableToProjector O a = ObservableToProjector O a := by
  fin_cases a
  · simp [ObservableToProjector, observableSign, add_mul, mul_add, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, hO.involutive]
    abel_nf
    simpa using congrArg₂ (fun x y => x + y)
      (two_invQuarter_smul (R := R) (1 : R))
      (two_invQuarter_smul (R := R) O)
  · simp [ObservableToProjector, observableSign, add_mul, mul_add, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, hO.involutive]
    abel_nf
    simpa using congrArg₂ (fun x y => x + y)
      (two_invQuarter_smul (R := R) (1 : R))
      (congrArg Neg.neg (two_invQuarter_smul (R := R) O))

lemma observableToProjector_orthogonal
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {O : R} (hO : IsObservable R O) (a b : Fin 2) (hab : a ≠ b) :
    ObservableToProjector O a * ObservableToProjector O b = 0 := by
  fin_cases a <;> fin_cases b
  · contradiction
  · simp [ObservableToProjector, observableSign, add_mul, mul_add, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, hO.involutive]
    abel_nf
  · simp [ObservableToProjector, observableSign, add_mul, mul_add, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, hO.involutive]
    abel_nf
  · contradiction

lemma observableToProjector_selfAdjoint
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {O : R} (hO : IsObservable R O) (a : Fin 2) :
    star (ObservableToProjector O a) = ObservableToProjector O a := by
  fin_cases a <;> simp [ObservableToProjector, observableSign, hO.self_adjoint]

lemma observableToProjector_commute
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {O P : R} (h : Commute O P) (a b : Fin 2) :
    ObservableToProjector O a * ObservableToProjector P b =
      ObservableToProjector P b * ObservableToProjector O a := by
  fin_cases a <;> fin_cases b <;>
    simp only [ObservableToProjector, observableSign, add_mul, mul_add, smul_add,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul]
  all_goals
    simp [h.eq]
    abel_nf

lemma observable_projector_measurementSystem
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {O : R} (hO : IsObservable R O) :
    IsMeasurementSystem (ObservableToProjector O) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using observableToProjector_sum O
  · intro a
    exact observableToProjector_idempotent hO a
  · intro a b hab
    exact observableToProjector_orthogonal hO a b hab
  · intro a
    exact observableToProjector_selfAdjoint hO a

noncomputable def BobMeasurementFromObservables
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (obs : Fin G.s → R) :
  Fin G.s → (Fin 2 → R) :=
  fun j outcome => ObservableToProjector (obs j) outcome

lemma bobMeasurementFromObservables_isMeasurementSystem
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (S : ObservableStrategyData R G) (j : Fin G.s) :
    IsMeasurementSystem (BobMeasurementFromObservables S.obs j) := by
  simpa [BobMeasurementFromObservables] using
    (observable_projector_measurementSystem (O := S.obs j) (S.observable j))

lemma projector_commute_in_equation
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (S : ObservableStrategyData R G)
  (i : Fin G.r) (j k : G.V i) (a b : Fin 2) :
    ObservableToProjector (S.obs j.1) a * ObservableToProjector (S.obs k.1) b =
      ObservableToProjector (S.obs k.1) b * ObservableToProjector (S.obs j.1) a := by
  by_cases hjk : j = k
  · subst hjk
    exact observableToProjector_commute (Commute.refl _) a b
  · exact observableToProjector_commute ((S.sameEquation_comm i) hjk) a b

noncomputable def AliceMeasurementFromObservables
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G) :
  ∀ i, Assignment G i → R :=
  fun i assignment =>
    (Finset.univ : Finset (G.V i)).noncommProd
      (fun j_idx => ObservableToProjector (S.obs j_idx.1) (assignment j_idx))
      (by
        intro j hj j' hj' hne
        exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))

noncomputable def JointOn
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : ↥s → Fin 2) : R :=
  s.noncommProd
    (fun j =>
      if hj : j ∈ s then
        ObservableToProjector (S.obs j.1) (assignment ⟨j, hj⟩)
      else 1)
    (by
      intro j hj j' hj' hne
      have hjs : j ∈ s := hj
      have hj's : j' ∈ s := hj'
      simpa [Function.onFun, Commute, SemiconjBy, hjs, hj's] using
        (projector_commute_in_equation S i j j' (assignment ⟨j, hj⟩) (assignment ⟨j', hj'⟩)))

lemma jointOn_sum_one
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G) :
  ∀ i, (∑ assignment : ↥((Finset.univ : Finset (G.V i))) → Fin 2,
      JointOn S i (Finset.univ : Finset (G.V i)) assignment) = 1 := by
  classical
  intro i
  let sumJointOn :
      ∀ s : Finset (G.V i), (∑ assignment : ↥s → Fin 2, JointOn S i s assignment) = 1 := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp [JointOn]
    | @insert a s ha ih =>
        let a0 : ↥(insert a s) := ⟨a, Finset.mem_insert_self a s⟩
        let assignEquiv : (↥(insert a s) → Fin 2) ≃ Fin 2 × (↥s → Fin 2) :=
          { toFun := fun assignment =>
              (assignment a0, fun j => assignment ⟨j.1, Finset.mem_insert_of_mem j.2⟩)
            invFun := fun p j =>
              if hja : j.1 = a then
                p.1
              else
                p.2 ⟨j.1, by
                  rcases Finset.mem_insert.mp j.2 with hj | hj
                  · exact (hja hj).elim
                  · exact hj⟩
            left_inv := by
              intro assignment
              funext j
              by_cases hja : j.1 = a
              · have hj : j = a0 := by
                  apply Subtype.ext
                  simpa [a0] using hja
                simpa [hj]
              · have hjs : j.1 ∈ s := by
                  rcases Finset.mem_insert.mp j.2 with hj | hj
                  · exact (hja hj).elim
                  · exact hj
                have hsub :
                    (⟨j.1, Finset.mem_insert_of_mem hjs⟩ : ↥(insert a s)) = j := by
                  exact Subtype.ext (by rfl)
                simp [hja, hsub]
            right_inv := by
              intro p
              rcases p with ⟨b, β⟩
              apply Prod.ext
              · simp [a0]
              · funext j
                have hne : (j : G.V i) ≠ a := by
                  intro h
                  apply ha
                  simpa [h] using j.2
                simp [hne] }
        calc
          (∑ assignment : ↥(insert a s) → Fin 2, JointOn S i (insert a s) assignment)
              = ∑ p : Fin 2 × (↥s → Fin 2),
                  JointOn S i (insert a s) (assignEquiv.symm p) := by
                    refine Fintype.sum_equiv assignEquiv _ _ ?_
                    intro x
                    simpa using congrArg (fun y => JointOn S i (insert a s) y)
                      (assignEquiv.left_inv x).symm
          _ = ∑ p : Fin 2 × (↥s → Fin 2),
                ObservableToProjector (S.obs a.1) p.1 * JointOn S i s p.2 := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                rcases p with ⟨b, β⟩
                unfold JointOn
                rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
                simp [assignEquiv, a0]
                apply congrArg (fun z => ObservableToProjector (S.obs a.1) b * z)
                refine Finset.noncommProd_congr rfl ?_ (by
                  intro x hx y hy hxy
                  have hxa : x ≠ a := by
                    intro h
                    apply ha
                    simpa [h] using hx
                  have hya : y ≠ a := by
                    intro h
                    apply ha
                    simpa [h] using hy
                  change
                    (if h : x = a ∨ x ∈ s then ObservableToProjector (S.obs x.1) (if h : x = a then b else β ⟨x, hx⟩) else 1) *
                      (if h : y = a ∨ y ∈ s then ObservableToProjector (S.obs y.1) (if h : y = a then b else β ⟨y, hy⟩) else 1) =
                    (if h : y = a ∨ y ∈ s then ObservableToProjector (S.obs y.1) (if h : y = a then b else β ⟨y, hy⟩) else 1) *
                      (if h : x = a ∨ x ∈ s then ObservableToProjector (S.obs x.1) (if h : x = a then b else β ⟨x, hx⟩) else 1)
                  have hxv :
                      (if h : x = a ∨ x ∈ s then
                        ObservableToProjector (S.obs x.1) (if h : x = a then b else β ⟨x, hx⟩)
                      else 1) =
                        ObservableToProjector (S.obs x.1) (β ⟨x, hx⟩) := by
                    have hx' : x ∈ s := hx
                    simp [hx', hxa]
                  have hyv :
                      (if h : y = a ∨ y ∈ s then
                        ObservableToProjector (S.obs y.1) (if h : y = a then b else β ⟨y, hy⟩)
                      else 1) =
                        ObservableToProjector (S.obs y.1) (β ⟨y, hy⟩) := by
                    have hy' : y ∈ s := hy
                    simp [hy', hya]
                  rw [hxv, hyv]
                  exact projector_commute_in_equation S i x y (β ⟨x, hx⟩) (β ⟨y, hy⟩))
                · intro x hx
                  have hxa : x ≠ a := by
                    intro h
                    apply ha
                    simpa [h] using hx
                  simp [assignEquiv, hx, hxa]
          _ = ∑ β : ↥s → Fin 2,
                (∑ b : Fin 2, ObservableToProjector (S.obs a.1) b) * JointOn S i s β := by
                rw [Fintype.sum_prod_type]
                simp [Fin.sum_univ_two, add_mul, Finset.sum_add_distrib]
          _ = ∑ β : ↥s → Fin 2, JointOn S i s β := by
                have hms := observable_projector_measurementSystem (O := S.obs a.1) (S.observable a.1)
                have hsum : (∑ b : Fin 2, ObservableToProjector (S.obs a.1) b) = 1 := hms.sum_one
                simp [hsum]
          _ = 1 := ih
  simpa using sumJointOn (Finset.univ : Finset (G.V i))

lemma aliceMeasurementFromObservables_sum_one
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G) (i : Fin G.r) :
  (∑ assignment : Assignment G i, AliceMeasurementFromObservables S i assignment) = 1 := by
  classical
  let e : Assignment G i ≃ (↥((Finset.univ : Finset (G.V i))) → Fin 2) := {
    toFun := fun assignment j => assignment j.1
    invFun := fun assignment j => assignment ⟨j, Finset.mem_univ j⟩
    left_inv := by
      intro assignment
      funext j
      rfl
    right_inv := by
      intro assignment
      funext j
      cases j
      rfl
  }
  calc
    (∑ assignment : Assignment G i, AliceMeasurementFromObservables S i assignment)
        = ∑ assignment : ↥((Finset.univ : Finset (G.V i))) → Fin 2,
            AliceMeasurementFromObservables S i (e.symm assignment) := by
              refine Fintype.sum_equiv e _ _ ?_
              intro assignment
              rfl
    _ = ∑ assignment : ↥((Finset.univ : Finset (G.V i))) → Fin 2,
          JointOn S i (Finset.univ : Finset (G.V i)) assignment := by
            refine Finset.sum_congr rfl ?_
            intro assignment h
            simp [AliceMeasurementFromObservables, JointOn, e]
    _ = 1 := jointOn_sum_one S i

private lemma alice_partial_idempotent
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : Assignment G i) :
  let f : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (assignment j)
  (s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))) *
  (s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))) =
  (s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))) := by
  classical
  dsimp
  let f : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (assignment j)
  let comm : (s : Set (G.V i)).Pairwise (fun x y => Commute (f x) (f y)) := by
    intro j hj j' hj' hne
    simpa [Commute, SemiconjBy, f] using
      projector_commute_in_equation S i j j' (assignment j) (assignment j')
  have hmul := Finset.noncommProd_mul_distrib (s := s) f f comm comm comm
  calc
    s.noncommProd f comm * s.noncommProd f comm
      = s.noncommProd (fun j => f j * f j) (Finset.noncommProd_mul_distrib_aux comm comm comm) := by
            symm
            exact hmul
    _ = s.noncommProd f comm := by
          refine Finset.noncommProd_congr rfl ?_ (Finset.noncommProd_mul_distrib_aux comm comm comm)
          · intro j hj
            simp [f, observableToProjector_idempotent (S.observable j.1)]

private lemma alice_partial_selfAdjoint
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : Assignment G i) :
  let f : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (assignment j)
  star (s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))) =
  s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j')) := by
  classical
  dsimp
  let f : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (assignment j)
  let comm : (s : Set (G.V i)).Pairwise (fun x y => Commute (f x) (f y)) := by
    intro j hj j' hj' hne
    simpa [Commute, SemiconjBy, f] using
      projector_commute_in_equation S i j j' (assignment j) (assignment j')
  induction s using Finset.induction with
  | empty =>
      simp [f]
  | @insert a s ha ih =>
      have hcomm_a_s :
          Commute (f a) (s.noncommProd f (comm.mono fun _ => Finset.mem_insert_of_mem)) := by
        refine Finset.noncommProd_commute s f (comm.mono fun _ => Finset.mem_insert_of_mem) (f a) ?_
        intro x hx
        exact comm (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hx) (by
          intro hxa
          exact ha (hxa.symm ▸ hx))
      rw [Finset.noncommProd_insert_of_notMem _ _ _ comm ha]
      rw [star_mul, ih]
      have hsa : star (f a) = f a := by
        simp [f, observableToProjector_selfAdjoint (S.observable a.1)]
      rw [hsa, hcomm_a_s.eq]

private lemma alice_partial_orthogonal
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (α β : Assignment G i) (j0 : G.V i) (hj0 : j0 ∈ s)
  (hneq : α j0 ≠ β j0) :
  let fα : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (α j)
  let fβ : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (β j)
  (s.noncommProd fα (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (α j) (α j'))) *
  (s.noncommProd fβ (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (β j) (β j'))) = 0 := by
  classical
  dsimp
  let fα : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (α j)
  let fβ : G.V i → R := fun j => ObservableToProjector (S.obs j.1) (β j)
  let commα : (s : Set (G.V i)).Pairwise (fun x y => Commute (fα x) (fα y)) := by
    intro j hj j' hj' hne
    simpa [Commute, SemiconjBy, fα] using projector_commute_in_equation S i j j' (α j) (α j')
  let commβ : (s : Set (G.V i)).Pairwise (fun x y => Commute (fβ x) (fβ y)) := by
    intro j hj j' hj' hne
    simpa [Commute, SemiconjBy, fβ] using projector_commute_in_equation S i j j' (β j) (β j')
  let commβα : (s : Set (G.V i)).Pairwise (fun x y => Commute (fβ x) (fα y)) := by
    intro j hj j' hj' hne
    simpa [Commute, SemiconjBy, fα, fβ] using
      (projector_commute_in_equation S i j' j (α j') (β j)).symm
  have hmul := Finset.noncommProd_mul_distrib (s := s) fα fβ commα commβ commβα
  have hcomm_prod : (s : Set (G.V i)).Pairwise (fun x y => Commute (fα x * fβ x) (fα y * fβ y)) :=
    Finset.noncommProd_mul_distrib_aux commα commβ commβα
  calc
    s.noncommProd fα commα * s.noncommProd fβ commβ
      = s.noncommProd (fun j => fα j * fβ j) hcomm_prod := by
          symm
          exact hmul
    _ = (s.erase j0).noncommProd (fun j => fα j * fβ j) (by
          intro j hj j' hj' hne
          exact hcomm_prod (s.mem_of_mem_erase hj) (s.mem_of_mem_erase hj') hne) * (fα j0 * fβ j0) := by
            symm
            exact Finset.noncommProd_erase_mul s hj0 (fun j => fα j * fβ j) hcomm_prod
    _ = 0 := by
          have hj0zero : fα j0 * fβ j0 = 0 := by
            simpa [fα, fβ] using observableToProjector_orthogonal (S.observable j0.1) (α j0) (β j0) hneq
          simp [hj0zero]

lemma aliceMeasurementFromObservables_isMeasurementSystem
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout} (S : ObservableStrategyData R G) (i : Fin G.r) :
  IsMeasurementSystem (AliceMeasurementFromObservables S i) := by
  classical
  refine ⟨aliceMeasurementFromObservables_sum_one S i, ?_, ?_, ?_⟩
  · intro assignment
    simpa [AliceMeasurementFromObservables] using
      (alice_partial_idempotent S i (Finset.univ : Finset (G.V i)) assignment)
  · intro α β hαβ
    have hex : ∃ j : G.V i, α j ≠ β j := by
      classical
      by_contra h
      apply hαβ
      funext j
      exact by_contra (fun hj => h ⟨j, hj⟩)
    rcases hex with ⟨j0, hj0neq⟩
    simpa [AliceMeasurementFromObservables] using
      (alice_partial_orthogonal S i (Finset.univ : Finset (G.V i)) α β j0 (by simp) hj0neq)
  · intro assignment
    simpa [AliceMeasurementFromObservables] using
      (alice_partial_selfAdjoint S i (Finset.univ : Finset (G.V i)) assignment)

noncomputable def build_LCS_strategy
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G)
  (h_cross :
    ∀ i j (α : Assignment G i) β,
      AliceMeasurementFromObservables S i α *
        BobMeasurementFromObservables S.obs j β =
      BobMeasurementFromObservables S.obs j β *
        AliceMeasurementFromObservables S i α) :
  LCSStrategy R G :=
  {
    E := AliceMeasurementFromObservables S
    F := BobMeasurementFromObservables S.obs
    alice_ms := aliceMeasurementFromObservables_isMeasurementSystem S
    bob_ms := bobMeasurementFromObservables_isMeasurementSystem S
    commute := h_cross
  }

end ObservableStrategy
