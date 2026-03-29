# Plan: Prove Equivalence between Observable and Projector Strategies

The goal is to implement the proof described in `res/EquivalenceProof.md` in the file `projects/LCS/LCS/Strategy/Equivalence.lean`. We will bridge the gap between the updated `ObservableStrategyData` (with separate Alice/Bob observables and commutation) and `LCSStrategy`.

## Proposed Changes

### [NEW] [ObservableToProjector.lean](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Strategy/ObservableToProjector.lean)

We will move the construction and fundamental lemmas of `ObservableToProjector` to a dedicated file for cleaner organization.

- **Definition**: Move `ObservableToProjector (O : R) (a : Fin 2)` here.
- **Lemmas**:
  - `star_observableToProjector`: $P(O, a)^\dagger = P(O, a)$ if $O$ is observable.
  - `idempotent_observableToProjector`: $P(O, a)^2 = P(O, a)$ if $O$ is observable.
  - `orthogonal_observableToProjector`: $P(O, 0) P(O, 1) = 0$.
  - `sum_one_observableToProjector`: $P(O, 0) + P(O, 1) = I$.
  - `commute_observableToProjector`: $\text{Commute } P(O_1, a) P(O_2, b)$ if $\text{Commute } O_1 O_2$.

### [MODIFY] [ProjectorStrategy.lean](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Strategy/ProjectorStrategy.lean)

- Remove the definition of `ObservableToProjector`.
- Import `LCS.Strategy.ObservableToProjector`.

### [MODIFY] [Equivalence.lean](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Strategy/Equivalence.lean)

Implement `ObservableStrategy_To_ProjectorStrategy` using the updated `ObservableStrategyData`.

#### 1. Define Alice and Bob Projectors
- Define $F_{j}(y) = \text{ObservableToProjector}(S.bob\_obs\ j,\ y)$.
- Define $E_{i,x} = \prod_{j \in V_i} \text{ObservableToProjector}(S.alice\_obs\ j.1,\ x\ j)$.
  - Use `Finset.univ.prod` (or similar) combined with `S.sameEquation_comm`.

#### 2. Prove Measurement Systems
- **`bob_ms`**: Directly uses lemmas from `ObservableToProjector.lean` and `S.bob_observable`.
- **`alice_ms`**: Implements the proof from `res/EquivalenceProof.md`:
  - **Self-Adjoint**: Product of commuting self-adjoint elements.
  - **Idempotent**: Product of commuting idempotents.
  - **Orthogonal**: Finds the differing index $m \in V_i$ and uses `orthogonal_observableToProjector`.
  - **Sum to One**: Uses $P(O, 0) + P(O, 1) = I$ and the distributive property of products over sums.

#### 3. Prove Alice-Bob Commutativity (`commute`)
- Uses `S.alice_bob_commute` to show that every factor in $E_i$ commutes with every factor in $F_j$.

## Open Questions

- None at the moment, as the updated `ObservableStrategyData` resolves the commutativity issue.

## Verification Plan

### Automated Tests
- Compile the project ensuring all files (`ObservableToProjector.lean`, `ProjectorStrategy.lean`, `Equivalence.lean`) build without errors or `sorry`.
- Verify the main theorem `ObservableStrategy_To_ProjectorStrategy` is fully proven.
