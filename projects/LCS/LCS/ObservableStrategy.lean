import LCS.Basic
import LCS.Observables
import Mathlib.Algebra.Star.Module

open scoped BigOperators

namespace ObservableStrategy

structure ObservableStrategyData
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (G : LCSLayout) where
  obs : Fin G.s → R
  observable : ∀ j, IsObservable R (obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))

def observableSign (a : Fin 2) : ℂ :=
  if a = 0 then 1 else -1

noncomputable def ObservableToProjector
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (O : R) (a : Fin 2) : R :=
  (1 / 2 : ℂ) • (1 + observableSign a • O)

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

noncomputable def build_LCS_strategy
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G)
  (h_alice_ms : ∀ i, IsMeasurementSystem (AliceMeasurementFromObservables S i))
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
    alice_ms := h_alice_ms
    bob_ms := bobMeasurementFromObservables_isMeasurementSystem S
    commute := h_cross
  }

end ObservableStrategy
