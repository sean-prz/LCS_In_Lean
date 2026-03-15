import VersoManual


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
authors := ["Sean Perazzolo"]
shortTitle := "LCS in Lean4"
%%%


# Introduction to Linear Constraint System Games

A Linear Constraint System (LCS) game is a type of nonlocal game that can be used to demonstrate quantum advantage. In an LCS game, two players, Alice and Bob, are given inputs and must produce outputs that satisfy certain linear constraints. The players are not allowed to communicate with each other during the game, but they can share entangled quantum states beforehand.

Alice generally receives an input that corresponds to a linear constraint, and she must produce an output that satisfies that constraint. Bob receives an input that corresponds to a variable in the constraints, and he must produce an output that is consistent with the constraints given Alice's outpt.


## Mermin Peres Magic Square Game

The most famous example of an LCS game is the Mermin Peres Magic Square game. In this game, Alice and Bob are given a 3x3 grid of variables, and they must fill in the grid with 0s and 1s such that each row and column sums to an even number. Classically, it is impossible for Alice and Bob to win this game with probability 1, but if they share a specific entangled quantum state, they can win with probability 1.

# Formalising Linear Constraint System Games

Insipiring from the formalisation of an CHSH tuple in Lean4, we can formalise LCS games in a similar way. We will need to define the following concepts:

## The \*-algebra

## A LCS Strategy

### Measurement Systems

The following structure represents a set of projectors for a given question for Alice / variable for Bob. ect... 




```anchor IsMeasurementSystem (module := LCS.Basic) 
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
```

### Assignements.
Assignemnt is an abreviation/aliases for the type, (function type). the type of functions that represents all possible assignments of values to the variables in V i. A type that represents all possible assignments of values to the variables in V i.
```anchor Assignment
abbrev Assignment (G : LCSLayout) (i : Fin G.r) : Type :=
  (G.V i) → Fin 2
```
## A LCS Game

# Proving Properties of LCS Games 
