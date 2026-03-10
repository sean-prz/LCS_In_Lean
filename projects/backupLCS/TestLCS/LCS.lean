import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

open scoped BigOperators

-- From the docs : A *-ring R is a non-unital, non-associative (semi)ring
-- with an involutive star operation
-- which is additive which makes R with its multiplicative structure into a *-multiplication.
variable {R : Type*} [Ring R] [StarRing R]


/-- A family of elements of R (indexed by I) that satisfy the following properties:
   1. The sum of all the elements is 1 (completeness)
   2. Each element is idempotent (applying it twice is the same as applying it once)
   3. Distinct elements are orthogonal (applying one after the other gives 0)
   4. Each element is self-adjoint (Hermitian condition)
-/
-- ANCHOR: IsMeasurementSystem
structure IsMeasurementSystem {I : Type*} [Fintype I] (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
-- ANCHOR_END: IsMeasurementSystem


/-- Assignemnt is an abreviation/aliases for the type, (function type). the type of functions that represents all possible assignments of values to the variables in V i. A type that represents all possible assignments of values to the variables in V i. -/ 
abbrev Assignment {r s : ℕ} (V : Fin r → Finset (Fin s)) (i : Fin r) : Type :=
  (V i) → Fin 2

/-- A strategy for an LCS game consists of:
    1. For each question i, and each possible assignment of values to the variables in V i, we have an element of R (this is the E function).
    2. For each variable j, and each possible outcome (0 or 1), we have an element of R (this is the F function).
    3. For each question i, the family of elements given by E i forms a measurement system.
    4. For each variable j, the family of elements given by F j forms a measurement system.
    5. For each i, j, and each possible assignment α and β, E_(i,α) commutes with F_(j,β).
-/
structure LCSStrategy (R : Type*) [Ring R] [StarRing R] {r s : ℕ} (V : Fin r → Finset (Fin s)) where
  -- For each equation i in [r],
  -- and each possible combined, simultaneous assignment of values to ALL the variables in V i,
  -- we have an element of R.
  -- (i in [r], α : Assignment V i) ↦ E_(i,α) in R
  E : ∀ i, (Assignment V i → R)
  F : Fin s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α























noncomputable def Alice_A {R : Type*} [Ring R] [StarRing R] {r s : ℕ} {V : Fin r → Finset (Fin s)}
  (strat : LCSStrategy R V) (i : Fin r) (j : V i) : R :=
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment V i) => x j = 0), strat.E i x) -
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment V i) => x j = 1), strat.E i x)



/- lemma alice_observables_commute {R : Type*} [Ring R] [StarRing R] {r s : ℕ} {V : Fin r → Finset (Fin s)} -/
/-   (strat : LCSStrategy R V) (i : Fin r) (j j' : V i) : -/
/-   (Alice_A strat i j) * (Alice_A strat i j') = (Alice_A strat i j') * (Alice_A strat i j) := by -/
/-   sorry -- To be proven -/
