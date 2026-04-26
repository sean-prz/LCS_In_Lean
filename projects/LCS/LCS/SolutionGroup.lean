import LCS.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.PresentedGroup

open scoped BigOperators

/-- Generators for the solution group of a binary linear system. -/
inductive SolutionGen (S : LinearSystem) where
  | var : Fin S.layout.s → SolutionGen S
  | J : SolutionGen S
deriving DecidableEq

/-- The free-group generator attached to variable `j`. -/
def genVar {S : LinearSystem} (j : Fin S.layout.s) : FreeGroup (SolutionGen S) :=
  FreeGroup.of (SolutionGen.var j)

/-- The distinguished central free-group generator. -/
def genJ {S : LinearSystem} : FreeGroup (SolutionGen S) :=
  FreeGroup.of SolutionGen.J

/-- The relator forcing `x` to be an involution. -/
def involutionRel {α : Type*} (x : FreeGroup α) : FreeGroup α :=
  x ^ 2

/-- The commutator relator forcing `x` and `y` to commute. -/
def commuteRel {α : Type*} (x y : FreeGroup α) : FreeGroup α :=
  x * y * x⁻¹ * y⁻¹

/-- The support of equation `i`, extracted from the coefficient matrix. -/
def eqSupport (S : LinearSystem) (i : Fin S.layout.r) : Finset (Fin S.layout.s) :=
  Finset.univ.filter fun j => S.A i j = 1

/-- The left-hand-side word of equation `i`, ordered by the `Finset` order. -/
def equationWord (S : LinearSystem) (i : Fin S.layout.r) : FreeGroup (SolutionGen S) :=
  ((eqSupport S i).sort (· ≤ ·)).map (genVar (S := S)) |>.prod

/-- The relator encoding equation `i` as `equationWord = J^(b i)`. -/
def equationRelator (S : LinearSystem) (i : Fin S.layout.r) : FreeGroup (SolutionGen S) :=
  equationWord S i * (genJ (S := S) ^ (S.b i).val)⁻¹

/-- Two variables are related when they appear together in some equation. -/
def sameEquation (S : LinearSystem) (j k : Fin S.layout.s) : Prop :=
  ∃ i : Fin S.layout.r, S.A i j = 1 ∧ S.A i k = 1

/-- The defining relators of the solution group of `S`. -/
def solutionRelators (S : LinearSystem) : Set (FreeGroup (SolutionGen S)) :=
  fun w =>
    (∃ j, w = involutionRel (genVar (S := S) j)) ∨
    w = involutionRel (genJ (S := S)) ∨
    (∃ j, w = commuteRel (genVar (S := S) j) (genJ (S := S))) ∨
    (∃ j k, sameEquation S j k ∧ w = commuteRel (genVar (S := S) j) (genVar (S := S) k)) ∨
    (∃ i, w = equationRelator S i)

/-- The presented solution group attached to `S`. -/
abbrev SolutionGroup (S : LinearSystem) :=
  PresentedGroup (solutionRelators S)

namespace SolutionGroup

/-- The distinguished quotient element attached to variable `j`. -/
def var {S : LinearSystem} (j : Fin S.layout.s) : SolutionGroup S :=
  PresentedGroup.of (rels := solutionRelators S) (SolutionGen.var j)

/-- The distinguished quotient element `J`. -/
def J {S : LinearSystem} : SolutionGroup S :=
  PresentedGroup.of (rels := solutionRelators S) SolutionGen.J

@[simp] lemma var_sq {S : LinearSystem} (j : Fin S.layout.s) : var (S := S) j ^ 2 = 1 := by
  simpa [var, genVar, involutionRel] using
    (PresentedGroup.one_of_mem
      (rels := solutionRelators S)
      (x := involutionRel (genVar (S := S) j))
      (Or.inl ⟨j, rfl⟩))

@[simp] lemma J_sq {S : LinearSystem} : J (S := S) ^ 2 = 1 := by
  simpa [J, genJ, involutionRel] using
    (PresentedGroup.one_of_mem
      (rels := solutionRelators S)
      (x := involutionRel (genJ (S := S)))
      (Or.inr (Or.inl rfl)))

lemma var_comm_J {S : LinearSystem} (j : Fin S.layout.s) :
    var (S := S) j * J (S := S) = J (S := S) * var (S := S) j := by
  have h :
      var (S := S) j * J (S := S) * (var (S := S) j)⁻¹ * (J (S := S))⁻¹ = 1 := by
    simpa [var, J, genVar, genJ, commuteRel] using
      (PresentedGroup.one_of_mem
        (rels := solutionRelators S)
        (x := commuteRel (genVar (S := S) j) (genJ (S := S)))
        (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))))
  have h' := congrArg (fun z => z * J (S := S) * var (S := S) j) h
  simpa [mul_assoc] using h'

lemma var_comm_of_sameEquation {S : LinearSystem} {j k : Fin S.layout.s}
    (hjk : sameEquation S j k) :
    var (S := S) j * var (S := S) k = var (S := S) k * var (S := S) j := by
  have h :
      var (S := S) j * var (S := S) k * (var (S := S) j)⁻¹ * (var (S := S) k)⁻¹ = 1 := by
    simpa [var, genVar, commuteRel] using
      (PresentedGroup.one_of_mem
        (rels := solutionRelators S)
        (x := commuteRel (genVar (S := S) j) (genVar (S := S) k))
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, k, hjk, rfl⟩)))))
  have h' := congrArg (fun z => z * var (S := S) k * var (S := S) j) h
  simpa [mul_assoc] using h'

lemma equation_holds {S : LinearSystem} (i : Fin S.layout.r) :
    PresentedGroup.mk (solutionRelators S) (equationWord S i) = J (S := S) ^ (S.b i).val := by
  have h :
      PresentedGroup.mk (solutionRelators S) (equationWord S i * (genJ (S := S) ^ (S.b i).val)⁻¹) = 1 := by
    exact PresentedGroup.one_of_mem
      (rels := solutionRelators S)
      (x := equationRelator S i)
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))))
  have h' := congrArg (fun z => z * J (S := S) ^ (S.b i).val) h
  simpa [equationRelator, J, genJ, mul_assoc] using h'

end SolutionGroup
