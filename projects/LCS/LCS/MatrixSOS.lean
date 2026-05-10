import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Matrix Sum-of-Squares Helpers

This module contains finite-dimensional complex matrix lemmas used by the EPR
extraction arguments.  It is intentionally concrete over complex matrices: the
proofs use `Matrix.dotProduct` positivity and conjugate transpose.
-/

open scoped BigOperators ComplexOrder

open Matrix

section VectorNormSOS

variable {m : Type*} [Fintype m]

local notation "Mat" => Matrix m m ℂ

private lemma three_nonneg_add_eq_zero
    {α : Type*} [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b c : α} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨hab, hc_zero⟩ :=
    (add_eq_zero_iff_of_nonneg (add_nonneg ha hb) hc).mp h
  obtain ⟨ha_zero, hb_zero⟩ := (add_eq_zero_iff_of_nonneg ha hb).mp hab
  exact ⟨ha_zero, hb_zero, hc_zero⟩

private lemma dotProduct_square_mulVec_eq_dotProduct_mulVec_self
    [DecidableEq m]
    (T : Mat) (v : m → ℂ)
    (hT : Tᴴ = T) :
    star v ⬝ᵥ Matrix.mulVec (T ^ 2) v =
      star (Matrix.mulVec T v) ⬝ᵥ Matrix.mulVec T v := by
  simp [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hT]

variable [DecidableEq m]
variable (T₁ T₂ T₃ : Matrix m m ℂ) (v : m → ℂ)

lemma three_selfAdjoint_squares_mulVec_eq_zero
    (hT₁ : T₁ᴴ = T₁) (hT₂ : T₂ᴴ = T₂) (hT₃ : T₃ᴴ = T₃)
    (h :
      Matrix.mulVec (T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2) v = 0) :
    Matrix.mulVec T₁ v = 0 ∧ Matrix.mulVec T₂ v = 0 ∧ Matrix.mulVec T₃ v = 0 := by
  have hdot :
      star v ⬝ᵥ Matrix.mulVec (T₁ ^ 2 + T₂ ^ 2 + T₃ ^ 2) v = 0 := by
    simp [h]
  have hsum_complex :
      star (Matrix.mulVec T₁ v) ⬝ᵥ Matrix.mulVec T₁ v +
          star (Matrix.mulVec T₂ v) ⬝ᵥ Matrix.mulVec T₂ v +
          star (Matrix.mulVec T₃ v) ⬝ᵥ Matrix.mulVec T₃ v = 0 := by
    simpa [Matrix.add_mulVec, dotProduct_add,
      dotProduct_square_mulVec_eq_dotProduct_mulVec_self T₁ v hT₁,
      dotProduct_square_mulVec_eq_dotProduct_mulVec_self T₂ v hT₂,
      dotProduct_square_mulVec_eq_dotProduct_mulVec_self T₃ v hT₃] using hdot
  have h₁_nonneg :
      0 ≤ star (Matrix.mulVec T₁ v) ⬝ᵥ Matrix.mulVec T₁ v :=
    dotProduct_star_self_nonneg _
  have h₂_nonneg :
      0 ≤ star (Matrix.mulVec T₂ v) ⬝ᵥ Matrix.mulVec T₂ v :=
    dotProduct_star_self_nonneg _
  have h₃_nonneg :
      0 ≤ star (Matrix.mulVec T₃ v) ⬝ᵥ Matrix.mulVec T₃ v :=
    dotProduct_star_self_nonneg _
  obtain ⟨h₁_zero, h₂_zero, h₃_zero⟩ :=
    three_nonneg_add_eq_zero h₁_nonneg h₂_nonneg h₃_nonneg hsum_complex
  exact ⟨dotProduct_star_self_eq_zero.mp h₁_zero,
    dotProduct_star_self_eq_zero.mp h₂_zero,
    dotProduct_star_self_eq_zero.mp h₃_zero⟩

end VectorNormSOS
