
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
#doc (Manual) "About This Project" =>

This project formalises part of the theory of Linear Constraint System (LCS) games in Lean 4. The emphasis is on two linked themes: representing LCS games and their quantum strategies in a clean Lean interface, and proving structural results about perfect strategies using operator identities. The formal development is based on the framework used in Section 4.7 of Arthur Mehta's thesis [Entanglement and Non-locality in Games and Graphs](https://utoronto.scholaris.ca/server/api/core/bitstreams/3a3c8f11-3c06-4808-a685-deeda43f8fd3/content).

# Scope

The library is not intended to be a full survey of nonlocal games. It focuses on a specific slice of the theory that is mathematically coherent and already substantial enough to support both a general theorem and a concrete worked example.

On the abstract side, the project defines LCS layouts, LCS games, projector-valued strategies, observable-valued strategies, and the operators used to express local winning conditions. On the concrete side, it formalises the Mermin-Peres Magic Square game as the main case study.

# Verified Milestones

*Milestone 1.* The project formalises the Mermin-Peres Magic Square observables and proves that they determine a valid strategy in the observable formalism. This provides a concrete example showing that the abstract interfaces are strong enough to express a standard perfect quantum strategy.

*Milestone 2.* The project formalises the local winning and local loss operators for a general LCS game and projector strategy, and proves the sum-of-squares decomposition of the local loss operator. This is the main general structural result currently verified in the library.

# The Codebase

## Where to look

- The generated source and declaration browser for the library is available in [the API docs](./doc4/LCS.html).
- The Lean sources live in the `LCS` library under `projects/LCS/LCS`.

## Modules

*Core modules*
- **`LCS.Basic`**: core combinatorial data, including `LCSLayout`, `Assignment`, and `LCSGame`.
- **`LCS.Measurement`**: projector-valued measurement systems and the algebraic lemmas attached to them.
- **`LCS.Observable`**: observables and their basic interface.

*Core modules*

- **`LCS.Strategy.ProjectorStrategy`**: projector-based strategies for LCS games and the derived observables attached to Alice and Bob.
- **`LCS.Strategy.ObservableStrategy`**: observable-based strategy data.
- **`LCS.Strategy.ObservableToProjector`**: the construction turning observable strategy data into projector data.
- **`LCS.Strategy.Equivalence`**: results comparing the observable and projector viewpoints.

*Main results and examples*

- **`LCS.WinningCondition`**: winning assignments, local winning operators, local loss operators, and the sum-of-squares theorem.
- **`LCS.Games.MagicSquare`**: the Magic Square layout, observables, and strategy construction.

*Support modules*

- **`LCS.Common`**: shared arithmetic and sign conventions.
- **`LCS.Pauli`**: Pauli-matrix calculations used by the Magic Square example.

# Manual Overview

The rest of the manual is organised as a guided tour of the formalisation:

- *Introduction to Linear Constraint System Games* introduces the core game data and the role of strategies.
- *Formalising Linear Constraint System Games* presents the main Lean interfaces used throughout the library.
- *Strategy Formalisms and Equivalence* compares projector strategies and observable strategies, and explains the observable-to-projector construction.
- *Winning Condition and SOS Decomposition* presents the local loss operator and its sum-of-squares theorem.
- *Magic Square Case Study* shows how the abstract framework is instantiated on the Mermin-Peres game.
