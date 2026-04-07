import LCS.Basic
import LCS.Observable
import LCS.Strategy.ObservableStrategy
import LCS.Pauli
/-!
# Mermin-Peres Magic Square Game

This module defines the layout for the Mermin-Peres magic square Linear Constraint System (LCS) game
and provides a valid quantum strategy for it using observables.

It verifies the commutativity requirements (both local within equations and global bipartite commutativity)
necessary to define a valid `ObservableStrategyData`.
-/

abbrev mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
abbrev mat16 := Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ


/-- The layout of the Mermin-Peres magic square game.
It consists of 6 equations (3 rows and 3 columns) over 9 variables (the cells of the 3x3 grid). -/
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

open Matrix
open Kronecker
open scoped BigOperators


-- The Mermin-Peres Grid
/-- The 9 observables for the Mermin-Peres magic square, defined as Kronecker products of
Pauli matrices (X, Y, Z) and the identity (I2). -/
def magic_square_grid : Fin 9 → mat4
  | 0 => X  ⊗ₖ I2
  | 1 => I2 ⊗ₖ X
  | 2 => X  ⊗ₖ X
  | 3 => I2 ⊗ₖ Y
  | 4 => Y  ⊗ₖ I2
  | 5 => Y  ⊗ₖ Y
  | 6 => X  ⊗ₖ Y
  | 7 => Y  ⊗ₖ X
  | 8 => Z  ⊗ₖ Z

/-- A tactic to automatically prove that a matrix is an observable,
assuming it is a Kronecker product of Pauli matrices. -/
macro "crush_observable" : tactic => `(tactic| {
  dsimp [magic_square_grid]
  repeat (
    first
    | apply kronecker_observable
    | exact I2_observable
    | exact X_observable
    | exact Y_observable
    | exact Z_observable
  )
})

lemma magic_square_is_observable (j : Fin 9) : IsObservable (magic_square_grid j) := by
  fin_cases j <;> crush_observable


macro "crush_comm" : tactic => `(tactic| {
  dsimp [magic_square_grid]
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

lemma row1_comm : Pairwise (fun j k : magic_square_layout.V (0 : Fin 6) => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

lemma row2_comm : Pairwise (fun j k : magic_square_layout.V (1 : Fin 6) => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

lemma row3_comm : Pairwise (fun j k : magic_square_layout.V (2 : Fin 6) => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

lemma col1_comm : Pairwise (fun j k : magic_square_layout.V (3 : Fin 6) => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

lemma col2_comm : Pairwise (fun j k : magic_square_layout.V (4 : Fin 6) => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

lemma col3_comm : Pairwise (fun j k : magic_square_layout.V (5 : Fin 6) => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  solve_line_comm

lemma MP_sameEquation_comm (i : Fin 6) :
    Pairwise (fun j k : magic_square_layout.V i => Commute (magic_square_grid j.1) (magic_square_grid k.1)) := by
  fin_cases i
  · exact row1_comm
  · exact row2_comm
  · exact row3_comm
  · exact col1_comm
  · exact col2_comm
  · exact col3_comm

/-- The Mermin-Peres strategy for the magic square game.
This strategy uses `BipartiteObservableStrategy` to lift the 9 `MP_observables` to a
valid `ObservableStrategyData` on a 16x16 bipartite space. It relies on
`MP_sameEquation_comm` to satisfy the commutativity constraints for each equation. -/
noncomputable def Strat_merminPeres : ObservableStrategyData mat16 magic_square_layout :=
  BipartiteObservableStrategy magic_square_grid magic_square_is_observable MP_sameEquation_comm
