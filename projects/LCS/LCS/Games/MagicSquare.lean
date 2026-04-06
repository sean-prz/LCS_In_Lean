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

lemma row1_comm_0_1 : Commute (MP_observables 0) (MP_observables 1) := by
  dsimp [MP_observables]
  have h1 : Commute X I2 := by rw [I2_eq_one]; exact Commute.one_right X
  have h2 : Commute I2 X := by rw [I2_eq_one]; exact Commute.one_left X
  exact kronecker_comm_of_comm h1 h2

lemma row1_comm_1_2 : Commute (MP_observables 1) (MP_observables 2) := by
  dsimp [MP_observables]
  have h1 : Commute I2 X := by rw [I2_eq_one]; exact Commute.one_left X
  have h2 : Commute X X := Commute.refl X
  exact kronecker_comm_of_comm h1 h2

lemma row1_comm_0_2 : Commute (MP_observables 0) (MP_observables 2) := by
  dsimp [MP_observables]
  have h1 : Commute X X := Commute.refl X
  have h2 : Commute I2 X := by rw [I2_eq_one]; exact Commute.one_left X
  exact kronecker_comm_of_comm h1 h2

lemma row1_comm : Pairwise (fun j k : magic_square_layout.V (0 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  · exact row1_comm_0_1
  · exact row1_comm_0_2
  · exact row1_comm_0_1.symm
  · exact row1_comm_1_2
  · exact row1_comm_0_2.symm
  · exact row1_comm_1_2.symm

lemma row2_comm_3_4 : Commute (MP_observables 3) (MP_observables 4) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · rw [I2_eq_one]
    exact Commute.one_left Y
  · rw [I2_eq_one]
    exact Commute.one_right Y

lemma row2_comm_3_5 : Commute (MP_observables 3) (MP_observables 5) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · rw [I2_eq_one]
    exact Commute.one_left Y
  · exact Commute.refl Y

lemma row2_comm_4_5 : Commute (MP_observables 4) (MP_observables 5) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · exact Commute.refl Y
  · rw [I2_eq_one]
    exact Commute.one_left Y

lemma row2_comm : Pairwise (fun j k : magic_square_layout.V (1 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  · exact row2_comm_3_4
  · exact row2_comm_3_5
  · exact row2_comm_3_4.symm
  · exact row2_comm_4_5
  · exact row2_comm_3_5.symm
  · exact row2_comm_4_5.symm

lemma row3_comm_6_7 : Commute (MP_observables 6) (MP_observables 7) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_anticomm
  · exact XY_anticomm
  · rw [XY_anticomm]
    simp

lemma row3_comm_6_8 : Commute (MP_observables 6) (MP_observables 8) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_anticomm
  · exact XZ_anticomm
  · exact YZ_anticomm

lemma row3_comm_7_8 : Commute (MP_observables 7) (MP_observables 8) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_anticomm
  · exact YZ_anticomm
  · exact XZ_anticomm

lemma row3_comm : Pairwise (fun j k : magic_square_layout.V (2 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  · exact row3_comm_6_7
  · exact row3_comm_6_8
  · exact row3_comm_6_7.symm
  · exact row3_comm_7_8
  · exact row3_comm_6_8.symm
  · exact row3_comm_7_8.symm

lemma col1_comm_0_3 : Commute (MP_observables 0) (MP_observables 3) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · rw [I2_eq_one]
    exact Commute.one_right X
  · rw [I2_eq_one]
    exact Commute.one_left Y

lemma col1_comm_0_6 : Commute (MP_observables 0) (MP_observables 6) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · exact Commute.refl X
  · rw [I2_eq_one]
    exact Commute.one_left Y

lemma col1_comm_3_6 : Commute (MP_observables 3) (MP_observables 6) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · rw [I2_eq_one]
    exact Commute.one_left X
  · exact Commute.refl Y

lemma col1_comm : Pairwise (fun j k : magic_square_layout.V (3 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  · exact col1_comm_0_3
  · exact col1_comm_0_6
  · exact col1_comm_0_3.symm
  · exact col1_comm_3_6
  · exact col1_comm_0_6.symm
  · exact col1_comm_3_6.symm

lemma col2_comm_1_4 : Commute (MP_observables 1) (MP_observables 4) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · rw [I2_eq_one]
    exact Commute.one_left Y
  · rw [I2_eq_one]
    exact Commute.one_right X

lemma col2_comm_1_7 : Commute (MP_observables 1) (MP_observables 7) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · rw [I2_eq_one]
    exact Commute.one_left Y
  · exact Commute.refl X

lemma col2_comm_4_7 : Commute (MP_observables 4) (MP_observables 7) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_comm
  · exact Commute.refl Y
  · rw [I2_eq_one]
    exact Commute.one_left X

lemma col2_comm : Pairwise (fun j k : magic_square_layout.V (4 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  · exact col2_comm_1_4
  · exact col2_comm_1_7
  · exact col2_comm_1_4.symm
  · exact col2_comm_4_7
  · exact col2_comm_1_7.symm
  · exact col2_comm_4_7.symm

lemma col3_comm_2_5 : Commute (MP_observables 2) (MP_observables 5) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_anticomm
  · exact XY_anticomm
  · exact XY_anticomm

lemma col3_comm_2_8 : Commute (MP_observables 2) (MP_observables 8) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_anticomm
  · exact XZ_anticomm
  · exact XZ_anticomm

lemma col3_comm_5_8 : Commute (MP_observables 5) (MP_observables 8) := by
  dsimp [MP_observables]
  apply kronecker_comm_of_anticomm
  · exact YZ_anticomm
  · exact YZ_anticomm

lemma col3_comm : Pairwise (fun j k : magic_square_layout.V (5 : Fin 6) => Commute (MP_observables j.1) (MP_observables k.1)) := by
  intro j k hjk
  rcases j with ⟨j, hj⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;> simp [magic_square_layout] at hj hk hjk ⊢
  · exact col3_comm_2_5
  · exact col3_comm_2_8
  · exact col3_comm_2_5.symm
  · exact col3_comm_5_8
  · exact col3_comm_2_8.symm
  · exact col3_comm_5_8.symm

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
