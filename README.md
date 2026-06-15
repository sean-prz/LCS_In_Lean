# LCS in Lean 4

This repository provides a Lean 4 framework for reasoning about binary Linear Constraint System (LCS) games and their quantum strategies.

The development includes:

- core combinatorial definitions of LCS layouts and games
- observable and projector strategy formalisms
- the bridge from observable data to projector strategies
- local winning and local loss operators with a sum-of-squares decomposition
- EPR-style consequences of vanishing local loss
- solution groups and their complex-matrix representations

The main concrete example is the Mermin-Peres Magic Square game.

Further information and documentation available at <https://sean.perazzolo.ch/LCS>

## Build

The main Lean package is `src/`.

```bash
cd src
lake build
```

For a focused module check:

```bash
cd src
lake build LCS.WinningCondition
```

The toolchain is pinned to `leanprover/lean4:v4.28.0`.

## Using The Library

The umbrella module is `src/LCS.lean`, so downstream code can import the whole
library with:

```lean
import LCS
```

## Project Layout

- `src/`: main Lean package
- `src/LCS.lean`: umbrella entry point
- `src/LCS/Basic.lean`: `LCSLayout`, `Assignment`, `LCSGame`, `LinearSystem`
- `src/LCS/Common.lean`: finite-field and sign lemmas
- `src/LCS/Measurement.lean`, `src/LCS/Observable.lean`, `src/LCS/Pauli.lean`: operator and matrix infrastructure
- `src/LCS/Strategy/`: observable strategies, projector strategies, and conversion machinery
- `src/LCS/WinningCondition.lean`: local win/loss operators and SOS results
- `src/LCS/MatrixSOS.lean`, `src/LCS/EPR.lean`: positivity lemmas and EPR extraction
- `src/LCS/SolutionGroup.lean`, `src/LCS/SolutionGroup/Representation.lean`: solution groups and representations
- `src/LCS/Games/MagicSquare/`: the main worked example
- `src/docbuild/`: `doc-gen4` wrapper for API docs
- `update-docs.sh`: repository docs pipeline helper

## Documentation

To build API docs:

```bash
cd src/docbuild
lake build LCS:docs
```

The repository also includes `update-docs.sh`, which can:

- build API docs
- run the post-processing step in `postprocess_docs/`
- compile the Typst status report
- optionally serve `docs/` locally

## Main Example

The Mermin-Peres Magic Square development includes:

- the game data
- a Pauli-based observable strategy
- the associated solution-group construction
