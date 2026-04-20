
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
#doc (Manual) "Introduction to Linear Constraint System Games" =>

# Why LCS Games?
_LLM Generated Introduction_
Linear Constraint System games are a structured family of nonlocal games built from linear equations over `Fin 2`. They are important because they sit at a useful middle ground: rich enough to capture genuinely quantum behaviour, but rigid enough that one can prove general theorems about strategies rather than only isolated examples.

Historically, the Mermin-Peres Magic Square game gave one of the standard concrete demonstrations of perfect quantum performance in a game with no perfect classical strategy. Later work on nonlocal games and perfect strategies, including the LCS framework developed in the literature around solution groups and operator methods, used this class of games as a convenient setting in which algebraic and operator-theoretic arguments can be made explicit. This manual follows that perspective, while keeping the historical background brief.

# The Underlying Data

The starting point is the geometry of a system of binary linear constraints. An LCS layout records how many equations there are, how many variables there are, and which variables appear in each equation. In the library, this is the structure `LCSLayout` from `LCS.Basic`.

Once the layout is fixed, an LCS game chooses the right-hand side of each equation. The game data itself is therefore very small: for every equation, one bit saying whether the corresponding parity constraint should evaluate to `0` or `1`. This is the structure `LCSGame`.

The point of separating `LCSLayout` from `LCSGame` is mathematical as well as practical. Many constructions depend only on the incidence pattern between equations and variables, while the actual parity values matter only when one formulates the winning condition.

# Alice and Bob's Roles

As a nonlocal game, an LCS game is played by two cooperating but non-communicating players.

- Alice is asked an equation. She must answer with an assignment of bits to all variables appearing in that equation.
- Bob is asked a single variable. He must answer with one bit.

To win, Alice's assignment must satisfy the requested equation, and Bob's bit must agree with Alice's value on the shared variable whenever their questions overlap. The entire formalism is designed to make those two requirements precise in operator language.

In Lean, Alice's answer space for a fixed equation `i` is represented by `Assignment G i`, namely the type of functions from the variables occurring in equation `i` to `Fin 2`.

# Why Projector Strategies?

The main target formalism of the library is the projector-based one. A strategy is encoded by a family of projective measurements for Alice, indexed by equations and local assignments, together with a family of projective measurements for Bob, indexed by variables and binary outcomes. This is the structure `LCSStrategy` in `LCS.Strategy.ProjectorStrategy`.

This formalism is the natural home for the winning condition. It makes it possible to sum directly over answer sets, define local winning and local loss operators, and state the sum-of-squares decomposition theorem in the form used later in the manual. For that reason, the deepest general theorem in the project is phrased for projector strategies.

# Why Observables Also Appear

Although projector strategies are the main formal target, observables remain essential. In concrete quantum examples, one often starts from self-adjoint involutions with prescribed commutation relations rather than from a full list of projectors. The observable formalism captures exactly that viewpoint.

The library therefore also defines `ObservableStrategyData` in `LCS.Strategy.ObservableStrategy`, and then proves that observable data can be turned into projector data through the construction in `LCS.Strategy.ObservableToProjector`. This is what lets the development move back and forth between a compact operator description and the measurement-based language needed for the winning operators.

# The Main Case Study: Magic Square

The Mermin-Peres Magic Square game is the running example for the manual and the main concrete case study of the project. It is small enough to be explicit, but already rich enough to exhibit the phenomena that motivate the general theory: local parity constraints, compatibility conditions between Alice and Bob, and a perfect quantum strategy naturally described in terms of observables.

Later in the manual, the Magic Square chapter will instantiate the abstract framework on this example. For now, its role is conceptual: it is the guiding model showing why the two strategy formalisms are both useful, and why LCS games are a natural testing ground for formalising nonlocal-game arguments in Lean.


