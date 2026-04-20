
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
#doc (Manual) "Formalising Linear Constraint System Games" =>

This chapter introduces the basic Lean objects used to represent an LCS game. All of the core definitions discussed here live in `LCS.Basic`.


# Defining the Layout of an LCS Game
A linear constraint system starts with a finite family of equations in binary variables. The first task of the formalisation is therefore to record only the incidence data: how many equations there are, how many variables there are, and which variables occur in each equation.

This information is packaged in the structure `LCSLayout`, with the following fields:
- $`r` : the number of constraints (or questions for Alice)
- $`s` : the number of variables (or questions for Bob)
- $`V` : a function that takes an index i and returns the set of variables that are involved in the i-th constraint.


```anchor LCSLayout
structure LCSLayout where
  r : ℕ
  s : ℕ
  V : Fin r → Finset (Fin s)
```

The important design choice is that `LCSLayout` stores only the geometry of the game. It does not yet record the right-hand side of any equation. This separation is useful because many constructions depend only on which variables belong to which equation, not on the parity values that define the actual winning constraints.


# Assignments

Once an equation `i` is fixed, Alice's local answers are assignments of bits to the variables appearing in that equation. In Lean this is represented by the abbreviation `Assignment G i`.

For a given layout `G`, an assignment is simply a function from the finite set `G.V i` to `Fin 2`. This captures the fact that Alice answers locally, equation by equation, and only on the variables that appear in the equation she was asked.

Because the domain is finite, Lean can automatically treat `Assignment G i` as a finite type. This becomes important later, when the theory sums over all possible local answers in order to define measurement operators and winning operators.

```anchor Assignment
abbrev Assignment (G : LCSLayout) (i : Fin G.r) : Type :=
  (G.V i) → Fin 2
```

# A LCS Game

After the layout is fixed, an actual game is obtained by choosing the parity target of each equation. In the library this is done by the structure `LCSGame`, whose field `b` assigns to every equation a value in `Fin 2`.

This means that the formal game data is deliberately small: the layout tells us which variables belong to each constraint, and `b` tells us whether the corresponding sum should equal `0` or `1`. Together these two pieces determine the classical winning conditions that later get translated into operator statements.

```anchor LCSGame
structure LCSGame (G : LCSLayout) where
  b : Fin G.r → Fin 2
```

# Summary

The next chapter adds the quantum side of the story: measurement systems, projector strategies, observable strategies, and the equivalence results connecting the two viewpoints.
