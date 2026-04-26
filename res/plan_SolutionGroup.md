# Plan: Generic Solution Group for Linear Systems

## Goal

Define in Lean:

1. a full linear-system object carrying layout, coefficient matrix, and right-hand side
2. a generic solution-group construction from that object
3. a canonical way to recover the current support-only LCS games as linear systems
4. the Mermin-Peres solution group as an instance of the generic construction

## High-Level Design

The current codebase has:

- `LCSLayout`, storing the incidence geometry through `V : Fin r → Finset (Fin s)`
- `LCSGame`, storing the parity bits `b : Fin r → Fin 2`

To match the usual solution-group presentation from the literature, introduce a new object that also stores the coefficient matrix:

```lean
structure LinearSystem where
  layout : LCSLayout
  A : Fin layout.r → Fin layout.s → Fin 2
  b : Fin layout.r → Fin 2
```

The generic solution-group construction should depend on `LinearSystem`, not directly on `LCSLayout` alone.

## Step 1: Introduce `LinearSystem`

Add a new structure:

```lean
structure LinearSystem where
  layout : LCSLayout
  A : Fin layout.r → Fin layout.s → Fin 2
  b : Fin layout.r → Fin 2
```

This should live either in `LCS/Basic.lean` or in the new `LCS/SolutionGroup.lean` file. If it will be reused beyond solution groups, prefer `Basic.lean`.

## Step 2: Add a Canonical Conversion from the Current Support-Only Data

The current project treats each equation as the parity condition on the variables in `G.V i`. This corresponds to the coefficient matrix:

```lean
A i j = if j ∈ G.V i then 1 else 0
```

Define a constructor from the existing data:

```lean
def LCSGame.toLinearSystem (G : LCSLayout) (game : LCSGame G) : LinearSystem :=
  ...
```

with:

- `layout := G`
- `A i j := if j ∈ G.V i then 1 else 0`
- `b := game.b`

This preserves compatibility with the existing code while making the matrix `A` explicit.

## Step 3: Create `LCS/SolutionGroup.lean`

This file should contain the generic presented-group construction for an arbitrary `S : LinearSystem`.

Suggested imports:

- `LCS.Basic`
- `Mathlib.GroupTheory.PresentedGroup`
- any small supporting imports needed for `Finset` products and filtered supports

## Step 4: Define the Generator Type

For a linear system `S`, define one abstract generator for each variable plus a distinguished central generator `J`.

Suggested definition:

```lean
inductive SolutionGen (S : LinearSystem) where
  | var : Fin S.layout.s → SolutionGen S
  | J : SolutionGen S
deriving DecidableEq
```

This is the generator type for `FreeGroup (SolutionGen S)`.

## Step 5: Define Helper Words in the Free Group

Define the standard helper words:

- `genVar (j : Fin S.layout.s) : FreeGroup (SolutionGen S)`
- `genJ : FreeGroup (SolutionGen S)`
- `involutionRel x := x ^ 2`
- `commuteRel x y := x * y * x⁻¹ * y⁻¹`

These will make the relator set readable.

## Step 6: Define Equation Supports from `A`

For each equation `i`, define its support using the coefficient matrix:

```lean
def eqSupport (S : LinearSystem) (i : Fin S.layout.r) : Finset (Fin S.layout.s) :=
  Finset.univ.filter (fun j => S.A i j = 1)
```

This is the chosen design: equation words should be built only over the support extracted from `A`, not over all variables with trivial factors inserted.

## Step 7: Define the Equation Word

For each equation `i`, define the left-hand-side word as the product of the variable generators appearing in `eqSupport i`:

```lean
def equationWord (S : LinearSystem) (i : Fin S.layout.r) : FreeGroup (SolutionGen S) :=
  (eqSupport S i).prod fun j => genVar j
```

The order is the `Finset` order. This is acceptable because the intended quotient will impose commutativity among variables appearing in the same equation.

## Step 8: Define the Equation Relator

For each equation `i`, encode the relation

```text
∏ g_j^(A i j) = J^(b i)
```

as the relator:

```lean
def equationRelator (S : LinearSystem) (i : Fin S.layout.r) : FreeGroup (SolutionGen S) :=
  equationWord S i * (genJ ^ (S.b i).val)⁻¹
```

Since `S.b i : Fin 2`, this is either:

- `equationWord S i` when `b i = 0`
- `equationWord S i * genJ` when `b i = 1`, using `J^2 = 1`

## Step 9: Define the Same-Equation Commutation Condition

Two variable generators should commute when they appear together in some equation.

Define the condition:

```lean
def sameEquation (S : LinearSystem) (j k : Fin S.layout.s) : Prop :=
  ∃ i : Fin S.layout.r, S.A i j = 1 ∧ S.A i k = 1
```

This drives the commutator relators.

## Step 10: Define the Full Relator Set

Define `solutionRelators (S : LinearSystem) : Set (FreeGroup (SolutionGen S))` to include:

1. `g_j^2 = 1` for every variable
2. `J^2 = 1`
3. `g_j J = J g_j` for every variable
4. `g_j g_k = g_k g_j` whenever `j` and `k` appear together in some equation
5. one equation relator `equationRelator S i` for each equation `i`

This is the core presented-group definition.

## Step 11: Define the Presented Group

Define:

```lean
abbrev SolutionGroup (S : LinearSystem) :=
  PresentedGroup (solutionRelators S)
```

This is the generic solution group associated to the linear system `S`.

## Step 12: Add Convenience Generator Elements in the Quotient

Define the distinguished elements of the quotient:

- `SolutionGroup.var (j : Fin S.layout.s)`
- `SolutionGroup.J`

Each should be defined using `PresentedGroup.of`.

These are the abstract generators that concrete representations will later interpret.

## Step 13: Add Basic Quotient-Level API Lemmas

Prove lemmas exposing the defining relations in `SolutionGroup S`, such as:

1. `var_sq`
2. `J_sq`
3. `var_comm_J`
4. `var_comm_of_sameEquation`
5. `equation_holds`

These do not need to be the strongest possible statements. The goal is to have a small practical API for later representations.

## Step 14: Instantiate the Magic Square as a `LinearSystem`

For Mermin-Peres, define or reuse:

- `magic_square_layout : LCSLayout`
- `magic_square_game : LCSGame magic_square_layout`

Then define:

```lean
def magic_square_system : LinearSystem :=
  LCSGame.toLinearSystem magic_square_layout magic_square_game
```

and:

```lean
abbrev MPSolutionGroup := SolutionGroup magic_square_system
```

This gives the magic-square solution group without any special-purpose group definition.

## Step 15: Later Concrete Representation to Pauli Matrices

Once the generic abstract group is in place, the next phase is to define a concrete homomorphism for Mermin-Peres:

1. choose a target group of invertible matrices or unitary observables
2. map each abstract variable generator to the corresponding Pauli observable
3. map `J` to `-I`
4. prove all relators are respected
5. use `PresentedGroup.toGroup` to obtain the homomorphism

This representation work should come after the generic solution-group file is complete.

## Minimal Implementation Order

Recommended implementation order:

1. define `LinearSystem`
2. define `LCSGame.toLinearSystem`
3. create `SolutionGen`
4. define free-group helper words
5. define `eqSupport`
6. define `equationWord`
7. define `equationRelator`
8. define `sameEquation`
9. define `solutionRelators`
10. define `SolutionGroup`
11. add convenience generators
12. prove a minimal quotient API
13. instantiate Mermin-Peres

## Naming Suggestions

Suggested names:

- `LinearSystem`
- `LCSGame.toLinearSystem`
- `SolutionGen`
- `eqSupport`
- `equationWord`
- `equationRelator`
- `sameEquation`
- `solutionRelators`
- `SolutionGroup`

These names keep the API centered on the generic linear-system construction rather than on any single game.
