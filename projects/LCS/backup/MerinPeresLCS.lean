-- ANCHOR: import
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Algebra.Basic        -- For the [Algebra ℂ R] typeclass
import Mathlib.Algebra.Module.Basic         -- For the scalar action (•)
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Complex.Basic           -- For the Complex numbers (ℂ)
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open scoped BigOperators

-- From the docs : A *-ring R is a non-unital, non-associative (semi)ring
-- with an involutive star operation
-- which is additive which makes R with its multiplicative structure into a *-multiplication.
variable {R : Type*} 


-- define type mat4 as 4x4 matrices over ℂ
def mat4 := Matrix (Fin 4) (Fin 4) ℂ
-- ANCHOR_END: import

-- ANCHOR: IsMeasurementSystem
structure IsMeasurementSystem {R : Type*} [Semiring R] [StarRing R] {I : Type*} [Fintype I] 
  (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
-- ANCHOR_END: IsMeasurementSystem


/-- Assignemnt is an abreviation/aliases for the type, (function type). the type of functions that represents all possible assignments of values to the variables in V i. A type that represents all possible assignments of values to the variables in V i. -/ 
abbrev Assignment {r s : ℕ}  (V : Fin r → Finset (Fin s)) (i : Fin r) : Type :=
  (V i) → Fin 2

/-- A strategy for an LCS game consists of:
    1. For each question i, and each possible assignment of values to the variables in V i, we have an element of R (this is the E function).
    2. For each variable j, and each possible outcome (0 or 1), we have an element of R (this is the F function).
    3. For each question i, the family of elements given by E i forms a measurement system.
    4. For each variable j, the family of elements given by F j forms a measurement system.
    5. For each i, j, and each possible assignment α and β, E_(i,α) commutes with F_(j,β).
-/
structure LCSStrategy (r s :  ℕ) (V : Fin r → Finset (Fin s)) (R : Type*) [Semiring R] [StarRing R] [Algebra ℂ R]
  where
  -- For each equation i in [r],
  -- and each possible combined, simultaneous assignment of values to ALL the variables in V i,
  -- we have an element of R.
  -- (i in [r], α : Assignment V i) ↦ E_(i,α) in R
  E : ∀ i, (Assignment V i → R)
  F : Fin s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α




def V_merinPeres : Fin 6 → Finset (Fin 9) := fun i =>
  match i with
  | 0 => {0, 1, 2}
  | 1 => {3, 4, 5}
  | 2 => {6, 7, 8}
  | 3 => {0, 3, 6}
  | 4 => {1, 4, 7}
  | 5 => {2, 5, 8}


open Matrix
open Kronecker



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
  (r:= 6) (s:= 9) V_merinPeres (Matrix (Fin 4) (Fin 4) ℂ)  := 
  {
  E := fun i assignment => 
    let V_i  : Finset (Fin 9)   := V_merinPeres i  -- i.e {0,1,2}
    let Obs_i  := V_i.map (fun j => MP_observables j) -- i.e {X⊗I, I⊗X, X⊗X}
    let α    : Finset (Fin 2)   := Finset.univ.filter (fun x => x ∈ V_i)

  F := fun j outcome => ObservableToProjector (MP_observables j) outcome
  alice_ms := sorry, -- To be proven
  bob_ms   := sorry, -- To be proven
  commute  := sorry, -- To be proven
} 




noncomputable def Alice_A {R : Type*} [Ring R] [StarRing R] {r s : ℕ} {V : Fin r → Finset (Fin s)}
  (strat : LCSStrategy R V) (i : Fin r) (j : V i) : R :=
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment V i) => x j = 0), strat.E i x) -
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment V i) => x j = 1), strat.E i x)



/- lemma alice_observables_commute {R : Type*} [Ring R] [StarRing R] {r s : ℕ} {V : Fin r → Finset (Fin s)} -/
/-   (strat : LCSStrategy R V) (i : Fin r) (j j' : V i) : -/
/-   (Alice_A strat i j) * (Alice_A strat i j') = (Alice_A strat i j') * (Alice_A strat i j) := by -/
/-   sorry -- To be proven -/
