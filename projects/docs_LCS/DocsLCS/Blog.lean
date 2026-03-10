import VersoBlog

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "../LCS"
set_option verso.exampleModule "LCS"
#doc (Page) "Archive" => 



We will need the definition of a measurement system, which is a family of elements in R that sum to 1, are idempotent, orthogonal, and self-adjoint. This is the mathematical structure that captures the idea of a quantum measurement in the context of our LCS game.

To define this, we need to import some basic algebraic structures from mathlib, and then we can define the IsMeasurementSystem structure.


# The import

```anchor import
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi

open scoped BigOperators

-- From the docs : A *-ring R is a non-unital, non-associative (semi)ring
-- with an involutive star operation
-- which is additive which makes R with its multiplicative structure into a *-multiplication.
variable {R : Type*} [Ring R] [StarRing R]
```



## IsMeasurementSystem



```anchor IsMeasurementSystem
structure IsMeasurementSystem {I : Type*} [Fintype I] 
  (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
```
