import VersoManual
import DocsLCS.Section1
import DocsLCS.Section2
-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso. Here, they're used to have the text refer to Verso code used in the text's
-- own source.
open Verso.Genre.Manual.InlineLean

-- This gets access to tools for showing Lean code that's loaded from external modules. need new
open Verso.Code.External


set_option pp.rawOnError true

set_option verso.exampleProject "../LCS"
set_option verso.exampleModule "LCS"


set_option verso.exampleModule "LCS.Basic"
#doc (Manual) "Formalisation of Linear Constraints Systems games in Lean4" =>
%%%
authors := ["Sean Perazzolo, Spring 2026"]
shortTitle := "LCS in Lean4"
%%%

*New W07* :
  - Verified Magic Square grid is a valid strategy for the Magic Squre game available [here](./doc4/LCS/games/MagicSquare.html) 
  - SOS Decomposition of the local loss operator of a LCS game available [here](./doc4/LCS/WinningCondition.html)


Week by week status of the project available [here](./status.pdf)



{include 1 DocsLCS.Section1}

{include 1 DocsLCS.Section2}


# Formalising Linear Constraint System Games
_To even start proving anything about LCS games, we first need to formalise what an LCS game is and what is a valid strategy for a game. This involves defining the geometry of the game, the requirements for a strategy to be valid, and the specific values of the constraints that define the game._

All of the content below is defined in the module [LCS.Basic](./).



## Defining the Layout of an LCS Game
A LCS Game is defined by his sets of variables and constraints.

We choose to represent the geometry of the game using a structure called LCSLayout, which contains the following data:
- $`r` : the number of constraints (or questions for Alice)
- $`s` : the number of variables (or questions for Bob)
- $`V` : a function that takes an index i and returns the set of variables that are involved in the i-th constraint.


```anchor LCSLayout
structure LCSLayout where
  r : ℕ
  s : ℕ
  V : Fin r → Finset (Fin s)
```

Note that this layout does not contain any information about the specific values of the constraints, it only captures the geometry of the game, i.e. which variables are involved in which constraints. The specific values of the constraints will be captured in the definition of the LCS Game itself. This follows from the fact that a strategy for the game does not depend on the specific values of theconstraints, but only on the geometry of the game.


## Assignments

Assignment is an abbreviation for the function type representing all possible assignments of values to the variables within a specific constraint i.

For a given LCSLayout and a constraint i, an assignment is a function that maps each variable in Vi to a value in Fin 2 (0 or 1). This captures the requirement that Alice must provide a binary value for every variable involved in the i-th equation.

Because the domain Vi is finite, Lean can automatically infer that the type Assignment G i is also a Fintype. This is crucial for the formalization, as it allows us to sum over the entire space of possible assignments when defining Alice's observables.

```anchor Assignment
abbrev Assignment (G : LCSLayout) (i : Fin G.r) : Type :=
  (G.V i) → Fin 2
```

## A LCS Game
So far we have defined the geometry of the game, and the requirement for a strategy to be valid without ever specifying the specific values of the constraints. However as we will need to talk about winning assignements or winning strategies, we need to define
the values of the contraints.

A LCS game is defined for a layout G. It is represent as a function that takes an index i to a value in $`ZMod 2` (i.e. 0 or 1). This captures the idea that the i-th constraint requires that the sum of the variables involved in that constraint must be equal to 0 or 1

```anchor LCSGame
structure LCSGame (G : LCSLayout) where
  b : Fin G.r → Fin 2
```


## A Valid Strategy for an LCS Game
A strategy for an LCS game is modeled by two families of projectors. For each constraint i, Alice has a measurement system Ei over satisfying assignments. For each variable j, Bob has a measurement system Fj over binary outcomes. To ensure the strategy is physically realizable in the commuting operator framework, we require that all of Alice's projectors commute with all of Bob's projectors.

```anchor LCSStrategy (module := LCS.Strategy.ProjectorStrategy)
structure LCSStrategy
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
  (G : LCSLayout) where
  E : ∀ i, (Assignment G i → R)
  F : Fin G.s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α
```

### Measurement Systems (Projective Measurements)
The mathematical structure that captures the idea of a quantum measurement in the context of our LCS game.

```anchor IsMeasurementSystem (module := LCS.Measurement)
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
```


## Alice and Bob's Observables

Given a strategy for an LCS game, we can define the observables for Alice and Bob.

Alice’s observable for a given equation i and variable j (where j is in equation i) is defined as the difference between two sums: the sum of projectors for all assignments x of equation i that assign 0 to j, and the sum of projectors for all assignments x that assign 1 to j.

For Bob, the observable for a given variable j is defined as the difference between the projector that assigns 0 to j and the projector that assigns 1 to j.


### Alice's observable

```anchor Alice_A (module := LCS.Strategy.ProjectorStrategy)
noncomputable def Alice_A
  (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  ObservableOfMeasurementSystem (InducedMeasurementSystem (strat.E i) (fun x => x j))
```
### Bob's observable

```anchor Bob_B (module := LCS.Strategy.ProjectorStrategy)
def Bob_B (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  ObservableOfMeasurementSystem (strat.F j)
```
