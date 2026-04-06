import LCS.Basic
import LCS.Observable
import LCS.Strategy.ObservableStrategy
import LCS.Pauli

-- Single-party and bipartite matrix types for the Mermin-Peres strategy.
abbrev mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
abbrev mat16 := Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ
-- ANCHOR_END: import


def magic_square_layout : LCSLayout  := {
  r := 6
  s := 9
  V := fun i =>
  match i with
  | 0 => {0, 1, 2}
  | 1 => {3, 4, 5}
  | 2 => {6, 7, 8}
  | 3 => {0, 3, 6}
  | 4 => {1, 4, 7}
  | 5 => {2, 5, 8}
  }
#eval magic_square_layout.V (1: Fin 6)


open Matrix
open Kronecker
open scoped BigOperators


-- The Mermin-Peres Grid
def MP_observables : Fin 9 → mat4
  | 0 => X  ⊗ₖ I2
  | 1 => I2 ⊗ₖ X
  | 2 => X  ⊗ₖ X
  | 3 => I2 ⊗ₖ Y
  | 4 => Y  ⊗ₖ I2
  | 5 => Y  ⊗ₖ Y
  | 6 => X  ⊗ₖ Y
  | 7 => Y  ⊗ₖ X
  | 8 => Z  ⊗ₖ Z

lemma MP_observable (j : Fin 9) : IsObservable (MP_observables j) := by
  fin_cases j
  · simpa [MP_observables] using kronecker_observable X_observable I2_observable
  · simpa [MP_observables] using kronecker_observable I2_observable X_observable
  · simpa [MP_observables] using kronecker_observable X_observable X_observable
  · simpa [MP_observables] using kronecker_observable I2_observable Y_observable
  · simpa [MP_observables] using kronecker_observable Y_observable I2_observable
  · simpa [MP_observables] using kronecker_observable Y_observable Y_observable
  · simpa [MP_observables] using kronecker_observable X_observable Y_observable
  · simpa [MP_observables] using kronecker_observable Y_observable X_observable
  · simpa [MP_observables] using kronecker_observable Z_observable Z_observable


macro "crush_comm" : tactic => `(tactic| {
  dsimp [MP_observables]
  first
  | (apply kronecker_comm_of_comm; all_goals {
      first
      | exact Commute.refl _
      | { rw [I2_eq_one]; exact Commute.one_left _ }
      | { rw [I2_eq_one]; exact Commute.one_right _ }
    })
  | (apply kronecker_comm_of_anticomm; all_goals {
      first
      | exact XY_anticomm
      | exact XZ_anticomm
      | exact YZ_anticomm
      | { rw [XY_anticomm]; simp }
      | { rw [ZX_mul, XZ_mul]; simp }
      | { rw [ZY_mul, YZ_mul]; simp }
    })
})

macro "solve_line_comm" : tactic => `(tactic| {
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  <;> crush_comm
})

lemma row1_comm : Pairwise (fun j k : magic_square_layout.V (0 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  solve_line_comm

lemma row2_comm : Pairwise (fun j k : magic_square_layout.V (1 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  solve_line_comm

lemma row3_comm : Pairwise (fun j k : magic_square_layout.V (2 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  solve_line_comm

lemma col1_comm : Pairwise (fun j k : magic_square_layout.V (3 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  solve_line_comm

lemma col2_comm : Pairwise (fun j k : magic_square_layout.V (4 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  solve_line_comm

lemma col3_comm : Pairwise (fun j k : magic_square_layout.V (5 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  solve_line_comm

lemma MP_sameEquation_comm (i : Fin 6) :
    Pairwise (fun j k : magic_square_layout.V i => Commute (MP_observables j.1) (MP_observables k.1)) := by
  fin_cases i
  · exact row1_comm
  · exact row2_comm
  · exact row3_comm
  · exact col1_comm
  · exact col2_comm
  · exact col3_comm

noncomputable def Strat_merminPeres : ObservableStrategyData mat16 magic_square_layout :=
  BipartiteObservableStrategy MP_observables MP_observable MP_sameEquation_comm
