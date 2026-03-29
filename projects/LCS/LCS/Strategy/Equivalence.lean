import LCS.Strategy.ProjectorStrategy
import LCS.Strategy.ObservableStrategy

/-!
# Equivalence between Observable-based and Projector-based Strategies

This module establishes the equivalence between the two main formalisms for LCS strategies:
1. **Observable-based strategies**: Defined in terms of self-adjoint involutive operators
   $A_j, B_k$ satisfying local commutation constraints.
2. **Projector-based strategies**: Defined in terms of projector measurement systems
   $E_{i,x}, F_{j,y}$ satisfying similar commutation and consistency constraints.

The main construction in this file is `ObservableStrategy_To_ProjectorStrategy`,
which converts an `ObservableStrategyData` into an `LCSStrategy`. It proves that:
- The induced Alice measurements $E_{i,x}$ (defined as products of projectors) and Bob
  measurements $F_{j,y}$ (derived from Bob's observables) form valid measurement systems.
- Alice and Bob's measurements commute as required by the LCS game structure.
-/

open ObservableStrategy
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace ObservableStrategy

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {G : LCSLayout}

/-- Bob's two-outcome measurement obtained from his observable via
$P_y = (1/2)(1 + (-1)^y B_j)$. -/
noncomputable def BobMeasurementFromObservables
  (S : ObservableStrategyData R G) :
  Fin G.s → Fin 2 → R :=
  fun j y => ObservableToProjector (S.bob_obs j) y

/-- For each question $j$, Bob's observable-induced projectors form a measurement system. -/
lemma bobMeasurementFromObservables_isMeasurementSystem
  (S : ObservableStrategyData R G) (j : Fin G.s) :
  IsMeasurementSystem (BobMeasurementFromObservables S j) where
  sum_one := by
    rw [Fin.sum_univ_two]
    exact sum_one_observableToProjector (S.bob_obs j)
  idempotent y := idempotent_observableToProjector (S.bob_obs j) (S.bob_observable j) y
  orthogonal y y' hy := by
    fin_cases y <;> fin_cases y'
    · contradiction
    · simpa [BobMeasurementFromObservables] using
        orthogonal_observableToProjector (S.bob_obs j) (S.bob_observable j)
    · have h := orthogonal_observableToProjector (S.bob_obs j) (S.bob_observable j)
      have hcomm : Commute (ObservableToProjector (S.bob_obs j) 1)
          (ObservableToProjector (S.bob_obs j) 0) :=
        commute_observableToProjector (Commute.refl (S.bob_obs j)) 1 0
      exact hcomm.eq.trans (by simpa [BobMeasurementFromObservables] using h)
    · contradiction
  self_adjoint y := star_observableToProjector (S.bob_obs j) (S.bob_observable j) y

/-- Projectors built from Alice observables belonging to the same equation commute,
because the underlying observables commute. -/
lemma projector_commute_in_equation
  (S : ObservableStrategyData R G)
  (i : Fin G.r) (j k : G.V i) (a b : Fin 2) :
    Commute (ObservableToProjector (S.alice_obs j.1) a)
      (ObservableToProjector (S.alice_obs k.1) b) := by
  by_cases hjk : j = k
  · subst hjk
    exact commute_observableToProjector (Commute.refl _) a b
  · exact commute_observableToProjector ((S.sameEquation_comm i) hjk) a b

/-- Alice's projector for an assignment $x$ is the product
$E_{i,x} = \prod_{j \in V_i} (1/2)(1 + (-1)^{x_j} A_j)$. -/
noncomputable def AliceMeasurementFromObservables
  (S : ObservableStrategyData R G) :
  ∀ i, Assignment G i → R :=
  fun i assignment =>
    (Finset.univ : Finset (G.V i)).noncommProd
      (fun j_idx => ObservableToProjector (S.alice_obs j_idx.1) (assignment j_idx))
      (by
        intro j hj j' hj' hne
        exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))

/-- Partial joint measurement over a finite subset $s \subseteq V_i$.
This is used to prove the normalization of Alice's full measurement by induction on $s$. -/
noncomputable def JointOn
  (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : ∀ j ∈ s, Fin 2) : R :=
  s.noncommProd
    (fun j =>
      if hj : j ∈ s then
        ObservableToProjector (S.alice_obs j.1) (assignment j hj)
      else 1)
    (by
      intro j hj j' hj' hne
      have hjs : j ∈ s := hj
      have hj's : j' ∈ s := hj'
      simpa [Function.onFun, hjs, hj's] using
        (projector_commute_in_equation S i j j' (assignment j hjs) (assignment j' hj's)))

/-- Summing the partial joint projectors over all assignments on $s = V_i$ gives $1$. -/
lemma jointOn_sum_one
  (S : ObservableStrategyData R G) :
  ∀ i, (∑ assignment : ∀ j ∈ (Finset.univ : Finset (G.V i)), Fin 2,
      JointOn S i (Finset.univ : Finset (G.V i)) assignment) = 1 := by
  classical
  intro i
  let sumJointOn :
      ∀ s : Finset (G.V i), (∑ assignment : ∀ j ∈ s, Fin 2, JointOn S i s assignment) = 1 := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp [JointOn]
    | @insert a s ha ih =>
        let assignEquiv :=
          Finset.insertPiProdEquiv (fun _ : G.V i => Fin 2) (s := s) (a := a) ha
        calc
          (∑ assignment : ∀ j ∈ insert a s, Fin 2, JointOn S i (insert a s) assignment)
              = ∑ p : Fin 2 × (∀ j ∈ s, Fin 2),
                  JointOn S i (insert a s) (assignEquiv.symm p) := by
                    refine Fintype.sum_equiv assignEquiv _ _ ?_
                    intro assignment
                    simpa using congrArg (fun y => JointOn S i (insert a s) y)
                      (assignEquiv.left_inv assignment).symm
          _ = ∑ p : Fin 2 × (∀ j ∈ s, Fin 2),
                ObservableToProjector (S.alice_obs a.1) p.1 * JointOn S i s p.2 := by
                refine Finset.sum_congr rfl ?_
                intro p
                simp only [Finset.mem_univ, true_implies]
                rcases p with ⟨b, β⟩
                unfold JointOn
                rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
                have ha_eval : assignEquiv.symm (b, β) a (Finset.mem_insert_self a s) = b := by
                  change Finset.prodPiInsert (fun _ : G.V i => Fin 2) (b, β) a
                    (Finset.mem_insert_self a s) = b
                  simp [Finset.prodPiInsert]
                simp [ha_eval]
                apply congrArg (fun z => ObservableToProjector (S.alice_obs a.1) b * z)
                refine Finset.noncommProd_congr rfl ?_ ?_
                · intro x hx
                  have hxa : x ≠ a := by
                    intro h
                    apply ha
                    simpa [h] using hx
                  have hx_eval :
                      assignEquiv.symm (b, β) x (Finset.mem_insert_of_mem hx) = β x hx := by
                    change Finset.prodPiInsert (fun _ : G.V i => Fin 2) (b, β) x
                      (Finset.mem_insert_of_mem hx) = β x hx
                    simp [Finset.prodPiInsert, hxa]
                  simp [hx, hx_eval]
          _ = ∑ β : ∀ j ∈ s, Fin 2,
                (∑ b : Fin 2, ObservableToProjector (S.alice_obs a.1) b) * JointOn S i s β := by
                rw [Fintype.sum_prod_type]
                simp [Fin.sum_univ_two, add_mul, Finset.sum_add_distrib]
          _ = ∑ β : ∀ j ∈ s, Fin 2, JointOn S i s β := by
                have hsum : (∑ b : Fin 2, ObservableToProjector (S.alice_obs a.1) b) = 1 := by
                  rw [Fin.sum_univ_two]
                  exact sum_one_observableToProjector (S.alice_obs a.1)
                simp [hsum]
          _ = 1 := ih
  simpa using sumJointOn (Finset.univ : Finset (G.V i))

/-- Alice's full assignment-indexed projectors sum to $1$. -/
lemma aliceMeasurementFromObservables_sum_one
  (S : ObservableStrategyData R G) (i : Fin G.r) :
  (∑ assignment : Assignment G i, AliceMeasurementFromObservables S i assignment) = 1 := by
  classical
  let e : Assignment G i ≃ (∀ j ∈ (Finset.univ : Finset (G.V i)), Fin 2) := {
    toFun := fun assignment j _ => assignment j
    invFun := fun assignment j => assignment j (by simp)
    left_inv := by
      intro assignment
      funext j
      rfl
    right_inv := by
      intro assignment
      funext j hj
      simp
  }
  calc
    (∑ assignment : Assignment G i, AliceMeasurementFromObservables S i assignment)
        = ∑ assignment : ∀ j ∈ (Finset.univ : Finset (G.V i)), Fin 2,
            AliceMeasurementFromObservables S i (e.symm assignment) := by
              refine Fintype.sum_equiv e _ _ ?_
              intro assignment
              rfl
    _ = ∑ assignment : ∀ j ∈ (Finset.univ : Finset (G.V i)), Fin 2,
          JointOn S i (Finset.univ : Finset (G.V i)) assignment := by
            refine Finset.sum_congr rfl ?_
            intro assignment h
            simp [AliceMeasurementFromObservables, JointOn, e]
    _ = 1 := jointOn_sum_one S i

/-- Two distinct outcomes for the projector associated to a single observable are orthogonal. -/
private lemma projector_orthogonal_of_ne
  (O : R) (hO : IsObservable O) (a b : Fin 2) (hab : a ≠ b) :
  ObservableToProjector O a * ObservableToProjector O b = 0 := by
  fin_cases a <;> fin_cases b
  · contradiction
  · simpa using orthogonal_observableToProjector O hO
  · have h := orthogonal_observableToProjector O hO
    have hcomm : Commute (ObservableToProjector O 1) (ObservableToProjector O 0) :=
      commute_observableToProjector (Commute.refl O) 1 0
    exact hcomm.eq.trans (by simpa using h)
  · contradiction

/-- The partial Alice measurement over $s$ is idempotent. -/
private lemma alice_partial_idempotent
  (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : Assignment G i) :
  let f : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (assignment j)
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
  let f : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (assignment j)
  let comm : (s : Set (G.V i)).Pairwise (fun x y => Commute (f x) (f y)) := by
    intro j hj j' hj' hne
    simpa [f] using projector_commute_in_equation S i j j' (assignment j) (assignment j')
  have hmul := Finset.noncommProd_mul_distrib (s := s) f f comm comm comm
  calc
    s.noncommProd f comm * s.noncommProd f comm
      = s.noncommProd (fun j => f j * f j) (Finset.noncommProd_mul_distrib_aux comm comm comm) := by
          symm
          exact hmul
    _ = s.noncommProd f comm := by
          refine Finset.noncommProd_congr rfl ?_ (Finset.noncommProd_mul_distrib_aux comm comm comm)
          intro j hj
          simp [f, idempotent_observableToProjector, S.alice_observable]

/-- The partial Alice measurement over $s$ is self-adjoint. -/
private lemma alice_partial_selfAdjoint
  (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (assignment : Assignment G i) :
  let f : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (assignment j)
  star (s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j'))) =
  s.noncommProd f (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (assignment j) (assignment j')) := by
  classical
  dsimp
  let f : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (assignment j)
  let comm : (s : Set (G.V i)).Pairwise (fun x y => Commute (f x) (f y)) := by
    intro j hj j' hj' hne
    simpa [f] using projector_commute_in_equation S i j j' (assignment j) (assignment j')
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
        simp [f, star_observableToProjector, S.alice_observable]
      rw [hsa, hcomm_a_s.eq]

/-- If two assignments differ at some $j₀ \in s$, then the corresponding partial Alice
projectors are orthogonal. -/
private lemma alice_partial_orthogonal
  (S : ObservableStrategyData R G) (i : Fin G.r)
  (s : Finset (G.V i)) (α β : Assignment G i) (j0 : G.V i) (hj0 : j0 ∈ s)
  (hneq : α j0 ≠ β j0) :
  let fα : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (α j)
  let fβ : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (β j)
  (s.noncommProd fα (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (α j) (α j'))) *
  (s.noncommProd fβ (by
    intro j hj j' hj' hne
    exact projector_commute_in_equation S i j j' (β j) (β j'))) = 0 := by
  classical
  dsimp
  let fα : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (α j)
  let fβ : G.V i → R := fun j => ObservableToProjector (S.alice_obs j.1) (β j)
  let commα : (s : Set (G.V i)).Pairwise (fun x y => Commute (fα x) (fα y)) := by
    intro j hj j' hj' hne
    simpa [fα] using projector_commute_in_equation S i j j' (α j) (α j')
  let commβ : (s : Set (G.V i)).Pairwise (fun x y => Commute (fβ x) (fβ y)) := by
    intro j hj j' hj' hne
    simpa [fβ] using projector_commute_in_equation S i j j' (β j) (β j')
  let commβα : (s : Set (G.V i)).Pairwise (fun x y => Commute (fβ x) (fα y)) := by
    intro j hj j' hj' hne
    simpa [fα, fβ] using
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
            exact projector_orthogonal_of_ne (S.alice_obs j0.1) (S.alice_observable j0.1) (α j0)
              (β j0) hneq
          simp [hj0zero]

/-- For each equation $i$, the assignment-indexed family of Alice projectors is a measurement system. -/
lemma aliceMeasurementFromObservables_isMeasurementSystem
  (S : ObservableStrategyData R G) (i : Fin G.r) :
  IsMeasurementSystem (AliceMeasurementFromObservables S i) := by
  classical
  refine ⟨aliceMeasurementFromObservables_sum_one S i, ?_, ?_, ?_⟩
  · intro assignment
    simpa [AliceMeasurementFromObservables] using
      (alice_partial_idempotent S i (Finset.univ : Finset (G.V i)) assignment)
  · intro α β hαβ
    have hex : ∃ j : G.V i, α j ≠ β j := by
      by_contra h
      apply hαβ
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    rcases hex with ⟨j0, hj0neq⟩
    simpa [AliceMeasurementFromObservables] using
      (alice_partial_orthogonal S i (Finset.univ : Finset (G.V i)) α β j0 (by simp) hj0neq)
  · intro assignment
    simpa [AliceMeasurementFromObservables] using
      (alice_partial_selfAdjoint S i (Finset.univ : Finset (G.V i)) assignment)

/-- Every Alice projector commutes with every Bob projector, because each Alice observable
commutes with each Bob observable and commutation is preserved by the projector construction. -/
lemma aliceMeasurement_bobMeasurement_commute
  (S : ObservableStrategyData R G)
  (i : Fin G.r) (j : Fin G.s) (α : Assignment G i) (β : Fin 2) :
  AliceMeasurementFromObservables S i α * BobMeasurementFromObservables S j β =
    BobMeasurementFromObservables S j β * AliceMeasurementFromObservables S i α := by
  classical
  let f : G.V i → R := fun k => ObservableToProjector (S.alice_obs k.1) (α k)
  let comm : ((Finset.univ : Finset (G.V i)) : Set (G.V i)).Pairwise (fun x y => Commute (f x) (f y)) := by
    intro x hx y hy hxy
    simpa [f] using projector_commute_in_equation S i x y (α x) (α y)
  have hBob : ∀ x ∈ (Finset.univ : Finset (G.V i)),
      Commute (BobMeasurementFromObservables S j β) (f x) := by
    intro x hx
    simpa [BobMeasurementFromObservables, f] using
      commute_observableToProjector (S.alice_bob_commute x.1 j).symm β (α x)
  have hcomm_prod :
      Commute (BobMeasurementFromObservables S j β)
        ((Finset.univ : Finset (G.V i)).noncommProd f comm) :=
    Finset.noncommProd_commute (Finset.univ : Finset (G.V i)) f comm _ hBob
  simpa [AliceMeasurementFromObservables, BobMeasurementFromObservables] using hcomm_prod.eq.symm

end ObservableStrategy

open ObservableStrategy

/-- The observable strategy data induces a projector-valued LCS strategy by taking, for each
observable, its associated two-outcome spectral projectors. -/
noncomputable def ObservableStrategy_To_ProjectorStrategy
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G)
 :
  LCSStrategy R G :=
  {
    E := AliceMeasurementFromObservables S
    F := BobMeasurementFromObservables S
    alice_ms := aliceMeasurementFromObservables_isMeasurementSystem S
    bob_ms := bobMeasurementFromObservables_isMeasurementSystem S
    commute := aliceMeasurement_bobMeasurement_commute S
  }
