import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

universe u v w

/--
An LCS game measurement system in a *-ring.
* `I` represents the set of equations.
* `J` represents the set of variables.
* `X` represents the type of possible assignments (e.g., maps from J to {1, -1}).
* `E i x` represents Alice's projector for equation `i` yielding assignment `x`.
* `F j y` represents Bob's projector for variable `j` yielding value `y`.
-/
structure IsLCSMeasurement {R I J X Y : Type*} [Ring R] [StarRing R]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (E : I → X → R) (F : J → Y → R) : Prop where
  
  -- Alice's operators are valid projective measurements
  E_sa    : ∀ i x, star (E i x) = E i x
  E_proj  : ∀ i x, E i x ^ 2 = E i x
  E_ortho : ∀ i x x', x ≠ x' → E i x * E i x' = 0
  E_sum_I : ∀ i, ∑ x, E i x = 1
  
  -- Bob's operators are valid projective measurements
  F_sa    : ∀ j y, star (F j y) = F j y
  F_proj  : ∀ j y, F j y ^ 2 = F j y
  F_ortho : ∀ j y y', y ≠ y' → F j y * F j y' = 0
  F_sum_I : ∀ j, ∑ y, F j y = 1

  -- Alice's and Bob's measurements commute (tensor product suppression)
  EF_comm : ∀ i j x y, E i x * F j y = F j y * E i x

variable {R I J X : Type*} [Ring R] [StarRing R] [Fintype X] [DecidableEq X]
variable (E : I → X → R)
variable (eval : X → J → Int) -- Function to evaluate assignment x at variable j

/-- Alice's observable A_j^(i) defined as the difference of projectors -/
noncomputable def Alice_A (i : I) (j : J) : R :=
  (∑ x ∈ Finset.univ.filter (fun x => eval x j = 1), E i x) - 
  (∑ x ∈ Finset.univ.filter (fun x => eval x j = -1), E i x)
