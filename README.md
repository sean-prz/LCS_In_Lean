# LCS in Lean 4

This repository formalizes binary Linear Constraint System (LCS) games in Lean 4. It defines the core game structures, observable and projector strategy formalisms, winning and loss operators, the local-loss sum-of-squares decomposition, an EPR extraction pipeline, and solution groups together with their matrix representations.

The main concrete example is the Mermin-Peres Magic Square game.

Further information: <https://lcs.perazzolo.ch>

## Build

The main Lean project is `projects/LCS`.

```bash
cd projects/LCS
lake build
```


The toolchain is pinned to `leanprover/lean4:v4.28.0`.

## What Is Formalized

- Basic LCS data: `LCSLayout`, `Assignment`, `LCSGame`, `LinearSystem`
- Two strategy languages: observable strategies and projector strategies
- The bridge from observables to projectors in `LCS.Strategy.Equivalence`
- Local winning and loss operators, including the theorem `local_loss_sos`
- EPR extraction from local-loss annihilation to local matrix identities
- Solution groups and their representations by complex matrices

## Main Example

The main case study is the Mermin-Peres Magic Square game, including:

- its LCS layout and game data
- a Pauli-based observable strategy
- the associated solution-group construction

## Project Structure

Inside `projects/LCS/LCS/`:

- `Basic.lean`: core LCS definitions
- `Measurement.lean`, `Observable.lean`, `Pauli.lean`: operator and matrix tools
- `Strategy/`: observable strategies, projector strategies, and their bridge
- `WinningCondition.lean`: winning/loss operators and the SOS theorem
- `MatrixSOS.lean`, `EPR.lean`: positivity lemmas and EPR extraction
- `SolutionGroup.lean`, `SolutionGroup/Representation.lean`: solution groups and representations
- `Games/MagicSquare/`: the main worked example
