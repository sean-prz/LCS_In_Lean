
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


This semester research project is about formalising Linear Constraint System (LCS) games in Lean4.
Specifically the current end goal as of \[W06\] is to formalise the sum of square argument in LCS that gives a condition for the existence of a perfect quantum strategy for an LCS Game.

The exact statements this project is verifying are taken from section 4.7 of Arthur Mehta Thesis  [entanglement and non-locality in games and graphs](https://utoronto.scholaris.ca/server/api/core/bitstreams/3a3c8f11-3c06-4808-a685-deeda43f8fd3/content)

# The CodeBase

- The Interactive source view for this project is available [here](./source/LCS/)

- The raw source files are available on the public github repository for this project [here](https://github.com/sean-prz/LCS_In_Lean/tree/main/projects/LCS/LCS)

*Structure*

The codebase is structured in the following way:

    - *LCS.Basic* : contains the basic definitions of LCS games, including the definition of a measurement system, and the definition of a LCS game.
    - *LCS.MagicSquare* : contains the formalisation of the Mermin Peres Magic Square game, and the proof that it has a perfect quantum strategy.
    - *LCS.MeasurementLemmas* : contains some lemmas about measurement systems that are used in the proofs of the other modules.
    - *LCS.WinningCondition* : contains the formalisation of the sum of squares argument that gives a condition for the existence of a perfect quantum strategy for an LCS Game.


Section 3 of this manual documents the content of the module *LCS.Basic*.
