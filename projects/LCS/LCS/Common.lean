import LCS.Basic
open scoped BigOperators

set_option linter.unusedSectionVars false



lemma fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 := by
  match a with | 0 => left; rfl | 1 => right; rfl



lemma sign_mul (a b : Fin 2) :
    (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val = (-1 : ℂ) ^ (a + b).val := by
  fin_cases a <;> fin_cases b <;> simp


/-- Arithmetic helper: the sign factor `$(1/2)(1 + (-1)^b * (-1)^s)$` equals the indicator `s = b`. -/
lemma sign_indicator (b s : Fin 2) :
    (1 / 2 : ℂ) + (1 / 2 : ℂ) * (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ s.val = if s = b then 1 else 0 := by
  match b, s with
  | 0, 0 => norm_num
  | 0, 1 => norm_num
  | 1, 0 => norm_num
  | 1, 1 => norm_num


def observableSign (a : Fin 2) : ℂ :=
  if a = 0 then 1 else -1
