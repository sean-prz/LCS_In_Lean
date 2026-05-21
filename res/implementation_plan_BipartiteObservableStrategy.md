# Refactor to `BipartiteObservableStrategy` Structure

## Problem Description
Currently, `BipartiteObservableStrategy` is a function that takes `obs`, `obs_is_observable`, and `sameEquation_comm` and returns an `ObservableStrategyData`. Because `ObservableStrategyData` abstracts away the bipartite structure (it just has `alice_obs` and `bob_obs`), we lose the explicit information that `alice_obs = obs ⊗ 1` and `bob_obs = 1 ⊗ obs`. This lost information forces downstream files (like `Representation.lean` and EPR loss proofs) to pass around the raw `obs` arrays and constantly invoke bridging lemmas to unpack the strategy.

## Proposed Changes

We will introduce a new structure to explicitly represent a bipartite observable strategy over matrices, and use it to simplify the EPR/game-specific pipeline while leaving the generic group representation layers appropriately abstract.

### 1. `LCS/Strategy/ObservableStrategy.lean`
- **Replace existing API**: We will completely replace the current `def BipartiteObservableStrategy` with a `structure` of the same name. This is a breaking API change for any downstream users of the current constructor.
- [NEW] Define the structure:
  ```lean
  structure BipartiteObservableStrategy
      (n : Type*) [Fintype n] [DecidableEq n]
      (G : LCSLayout) where
    obs : Fin G.s → Matrix n n ℂ
    is_observable : ∀ j, IsObservable (obs j)
    sameEquation_comm : ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))
  ```
- [NEW] Provide the conversion to `ObservableStrategyData`:
  ```lean
  noncomputable def BipartiteObservableStrategy.toObservableStrategy
      {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
      (strat : BipartiteObservableStrategy n G) :
      ObservableStrategyData (Matrix (n × n) (n × n) ℂ) G := ...
  ```
- [NEW] Add `@[simp]` lemmas for the projections of `toObservableStrategy` so that proofs don't require manual unfolding:
  ```lean
  @[simp] lemma BipartiteObservableStrategy.alice_obs_eq (strat : BipartiteObservableStrategy n G) (j) :
    strat.toObservableStrategy.alice_obs j = bipartiteAliceLift (strat.obs j)
  ```

### 2. `LCS/Strategy/Equivalence.lean`
- [NEW] Add a convenience conversion to `LCSStrategy` and extraction lemmas to avoid boilerplate at use sites:
  ```lean
  noncomputable def BipartiteObservableStrategy.toProjectorStrategy
      {n : Type*} [Fintype n] [DecidableEq n] {G : LCSLayout}
      (strat : BipartiteObservableStrategy n G) :
      LCSStrategy (Matrix (n × n) (n × n) ℂ) G :=
    ObservableStrategy_To_ProjectorStrategy strat.toObservableStrategy

  @[simp] lemma alice_A_bipartite (strat : BipartiteObservableStrategy n G) (i : Fin G.r) (j : G.V i) :
      Alice_A strat.toProjectorStrategy i j = bipartiteAliceLift (strat.obs j.1)

  @[simp] lemma bob_B_bipartite (strat : BipartiteObservableStrategy n G) (j : Fin G.s) :
      Bob_B strat.toProjectorStrategy j = bipartiteBobLift (strat.obs j)
  ```

### 3. `LCS/SolutionGroup/Representation.lean` (and EPR pipeline)
- **Maintain Abstraction Boundary**: 
  - `section PresentedGroupConstruction` will **remain** in terms of raw `obs`. It builds a representation of an arbitrary `LinearSystem`, not a game, so bipartite structure is irrelevant there.
  - `section RepresentationData` (the game/EPR layer) will adopt `BipartiteObservableStrategy`.
- [NEW] Add the row product bridge lemma here (near the EPR lemmas that use `rowObservableProduct`), to avoid a cyclic or awkward dependency with `Equivalence.lean`:
  ```lean
  @[simp] lemma aliceRowProd_bipartite (strat : BipartiteObservableStrategy n G) (i : Fin G.r) :
      Alice_Row_Prod strat.toProjectorStrategy i = bipartiteAliceLift (rowObservableProduct strat.obs i)
  ```
- [MODIFY] In `section RepresentationData`, for **EPR-facing lemmas only**, replace `obs`, `obs_is_observable`, and `sameEquation_comm` with `(strat : BipartiteObservableStrategy n G)`. Helper lemmas about bare row products or `game.toLinearSystem` should continue using bare `obs`.
- [MODIFY] The `hLoss` hypothesis in the EPR constructors will simplify:
  ```lean
  (hLoss : ∀ i (j : G.V i),
    Matrix.mulVec (local_loss_operator game strat.toProjectorStrategy i j) (eprVec n) = 0)
  ```
- This bridges perfectly: The EPR layer unpacks `strat.obs` from `hLoss` and passes the resulting matrix identities to the generic group construction layer.

### 4. `LCS/Games/MagicSquare/Strategy.lean`
- [MODIFY] Update the instantiation of the Magic Square strategy to build the new `BipartiteObservableStrategy` structure instead of calling the old function.

## Verification Plan
1. `lake build LCS.Strategy.ObservableStrategy`
2. `lake build LCS.Strategy.Equivalence`
3. `lake build LCS.SolutionGroup.Representation`
4. `lake build LCS` to ensure `MagicSquare` and the umbrella library successfully adopt the new structure.
