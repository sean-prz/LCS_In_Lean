---
trigger: always_on
---

# LCS Project Summary: Current Structure

Formalization of Linear Constraint System (LCS) games in Lean 4.

Main goals:
1. Show equivalence between the observable strategy formalism and the projector strategy formalism.
2. Develop the local-loss sum-of-squares framework used to analyze perfect strategies.
3. Construct the solution group for binary 

## Project Roots

- Main Lean library: `projects/LCS`.
- Manual docs project (Verso): `projects/docs_LCS`.
- API docs project (`doc-gen4` wrapper): `projects/LCS/docbuild`.
- Toolchain is pinned to `leanprover/lean4:v4.28.0` in all three projects.

## Verified Commands

- Run all `lake` commands from `projects/LCS`, not from repo root.
- Full library build: `lake build`.
- Focused module check: `lake build LCS.WinningCondition`.
- Umbrella target: `LCS` via `projects/LCS/LCS.lean`.

## Lean Library Layout (`projects/LCS/LCS`)

1. **Core definitions and algebraic utilities**
   - `Basic.lean`: `LCSLayout`, `Assignment`, `LCSGame`, `LinearSystem`.
   - `Common.lean`: sign lemmas and finite-field arithmetic helpers.
   - `Measurement.lean`: projector measurement systems (`IsMeasurementSystem`) and induced measurements.
   - `Observable.lean`: observables (`IsObservable`) and observable/measurement conversions.
   - `Pauli.lean`: Pauli matrices and Kronecker-product lemmas used by concrete strategies.

2. **Strategy formalisms and bridges**
   - `Strategy/ObservableStrategy.lean`: observable strategy data (`ObservableStrategyData`) and bipartite lift.
   - `Strategy/ObservableToProjector.lean`: map `ObservableToProjector` and measurement proofs.
   - `Strategy/ProjectorStrategy.lean`: projector strategy data (`LCSStrategy`) and derived observables.
   - `Strategy/Equivalence.lean`: conversion from observable strategies to projector strategies.

3. **Group-theoretic layer**
   - `SolutionGroup.lean`: presented-group construction for LCS solution groups.

4. **Winning-condition results**
   - `WinningCondition.lean`: local winning/loss operators and SOS decomposition lemmas.

5. **Concrete example: Mermin-Peres Magic Square**
   - `Games/MagicSquare/Strategy.lean`: magic-square layout/game plus explicit observable strategy.
   - `Games/MagicSquare/SolutionGroup.lean`: solution-group instantiation and inspectable relators.
   - `Games/MagicSquare.lean`: re-export module for the game-specific files.

## Docs Flow

- Manual entrypoint: `projects/docs_LCS/MainManual.lean` (pulls `DocsLCS/*.lean`).
- Build manual docs from `projects/docs_LCS` with `lake exe generate-docs`.
- Docs examples target `../LCS` via `set_option verso.exampleProject "../LCS"`.
- Root `update-docs.sh` is a larger interactive pipeline for manual docs, optional literate/API docs, post-processing, and publishing artifacts into `docs/`.

## Gotchas

- Prefer focused `lake build <Module>` checks while iterating on Lean files.
- `projects/LCS/lakefile.toml` enables `weak.linter.mathlibStandardSet = true`; existing warnings can be non-blocking.
- Treat generated `docs/` output as build artifacts unless the task is explicitly about docs publication.
