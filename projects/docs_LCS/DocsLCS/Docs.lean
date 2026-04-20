import VersoManual
import DocsLCS.Section1
import DocsLCS.Section2
import DocsLCS.Section3
import DocsLCS.Section4
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



This manual acts as a research companion to the Lean 4 formalisation of Linear Constraint System (LCS) games. Its purpose is to explain the mathematical objects formalised in the library. Exhaustive declarations and theorem statements are left to the generated API documentation.
 
*Main Verified Results*

- The Mermin-Peres Magic Square observables are formalised and assembled into a valid strategy in the library. See the [Magic Square API page](./doc4/LCS/Games/MagicSquare.html).
- The local winning and local loss operators are formalised for a general LCS game, together with the sum-of-squares decomposition theorem for the local loss operator. See the [Winning condition API page](./doc4/LCS/WinningCondition.html).
- The bridge from observable strategies to projector strategies is implemented explicitly, so the two strategy formalisms can be compared inside one framework. See the [Strategy equivalence API page](./doc4/LCS/Strategy/Equivalence.html).

*Reference Links*

- A snapshot of the project's current written status is available in the [status report PDF](./status.pdf).
- The generated API documentation for the Lean library is available in [the API docs](./doc4/LCS.html).

{include 1 DocsLCS.Section1}

{include 1 DocsLCS.Section2}

{include 1 DocsLCS.Section3}

{include 1 DocsLCS.Section4}
