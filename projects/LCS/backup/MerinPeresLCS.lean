import LCS
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Algebra.Basic        -- For the [Algebra ℂ R] typeclass
import Mathlib.Algebra.Module.Basic         -- For the scalar action (•)
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Complex.Basic           -- For the Complex numbers (ℂ)
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

-- define type mat4 as 4x4 matrices over ℂ
abbrev mat4 := Matrix (Fin 4) (Fin 4) ℂ
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


-- Base Pauli Matrices
def I2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]


def toFin4 {R : Type*} (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv M

-- The Mermin-Peres Grid
def MP_observables : Fin 9 → mat4 
  | 0 => toFin4 (X  ⊗ₖ I2)
  | 1 => toFin4 (I2 ⊗ₖ X)
  | 2 => toFin4 (X  ⊗ₖ X)
  | 3 => toFin4 (Y  ⊗ₖ I2)
  | 4 => toFin4 (I2 ⊗ₖ Y)
  | 5 => toFin4 (Y  ⊗ₖ Y)
  | 6 => toFin4 (X  ⊗ₖ Y)
  | 7 => toFin4 (Y  ⊗ₖ X)
  | 8 => toFin4 (Z  ⊗ₖ Z)


noncomputable def ObservableToProjector {R : Type*} [Ring R] [Algebra ℂ R]
  (O : R) (a : Fin 2) : R := 
  let sign : ℂ := if a = 0 then 1 else -1
  (1/2 : ℂ) • (1 + sign • O)



noncomputable def Strat_merinPeres : LCSStrategy 
   mat4 magic_square_layout := 
  {
  F := fun j outcome => ObservableToProjector (MP_observables j) outcome
  E := fun i assignement => 
    Π j ∈ magic_square_layout.V i, ObservableToProjector (MP_observables j) (assignement j)
  alice_ms := sorry-- To be proven
  bob_ms   := sorry -- To be proven
  commute  := sorry -- To be proven
} 

/- #eval Strat_merinPeres.F (0: Fin 9) (0: Fin 2) -/


