# Refactor Proposal for `SolutionGroup/Representation.lean`

This plan updates the earlier representation refactor to account for the new
`BipartiteObservableStrategy` structure.

That structure already removed one layer of noise from the EPR pipeline:

- the game/EPR-facing API now carries
  `strat : BipartiteObservableStrategy n G`,
- `strat.toObservableStrategy` and `strat.toProjectorStrategy` are available,
- the bridge lemmas `alice_A_bipartite`, `bob_B_bipartite`, and
  `aliceRowProd_bipartite` already expose the concrete bipartite matrices.

So the next cleanup should not reintroduce raw `obs`, `obs_is_observable`, and
`sameEquation_comm` on the EPR side. The correct abstraction boundary is now:

- generic presented-group construction: raw `obs`,
- game/EPR construction: `BipartiteObservableStrategy`.

## Main Refactor

Collapse the public constructor stack to two main layers:

1. `solutionGroupRepresentation`
   - Generic over `S : LinearSystem`.
   - Inputs:
     - `obs`
     - `obs_is_observable`
     - `hsame : ∀ {j k}, sameEquation S j k → Commute (obs j) (obs k)`
     - `hequation : ∀ i, FreeGroup.lift ... (equationRelator S i) = 1`
   - Output:
     - `SolutionGroup S →* (Matrix n n ℂ)ˣ`
   - Implementation:
     - build the relator proof directly,
     - then call `PresentedGroup.toGroup`.

2. `solutionGroupRepresentationOfEPRLoss`
   - Game-specialized end-to-end constructor.
   - Inputs:
     - `strat : BipartiteObservableStrategy n G`
     - `hNonempty`
     - `hLoss : ∀ i (j : G.V i),
         Matrix.mulVec (local_loss_operator game strat.toProjectorStrategy i j) (eprVec n) = 0`
   - Responsibilities:
     - derive row identities from local loss,
     - convert row identities into equation-relator proofs,
     - call `solutionGroupRepresentation`.

This keeps the mathematical structure but removes the current wrapper chain.

## Constructors and Layers To Remove or Collapse

These are the main compression targets:

- `solutionGroupRepresentationOfRelatorProof`
- `solutionGroupRelatorProofOfEquationProof`
- `solutionGroupRepresentationOfGameEquationProof`

Target state:

- replace them with one public generic constructor,
- inline or privatize the relator-building proof,
- keep only the game/EPR entrypoint as the public specialization.

## Helpers To Privatize or Trim

These do useful local work, but they should not survive as broad public API
unless they are genuinely reused outside the file:

- `rowObservableProduct_eq_noncommProd`
- `sameEquation_toLinearSystem_iff`
- `eqSupport_toLinearSystem`
- `lift_genVar_list_prod_val`
- `lift_equationWord_toLinearSystem_val`

Suggested treatment:

- make them `private` if they are only used in one proof path,
- keep them public only if another file actually needs them.

By contrast, the following lemmas now have clear downstream value and should be
kept public:

- `solutionGroupGeneratorImage_var`
- `solutionGroupGeneratorImage_J`
- `BipartiteObservableStrategy.alice_A_bipartite`
- `BipartiteObservableStrategy.bob_B_bipartite`
- `aliceRowProd_bipartite`

## Most Valuable Generic Simplification

The biggest generic compression target is still:

- `lift_equationRelator_toLinearSystem_of_row`

Right now it goes through:

1. `lift_equationWord_toLinearSystem_val`
2. a local `hwordUnit`
3. a case split on `fin2_eq_zero_or_one`

That should be shortened by adding a dedicated simp lemma for the `J` image:

```lean
@[simp] lemma negOneMatrixUnit_pow_fin2_val (b : Fin 2) :
  ((negOneMatrixUnit (n := n) ^ b.val : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
    = (-1 : ℂ) ^ b.val • (1 : Matrix n n ℂ)
```

Then prove the relator by `Units.ext` using only:

- `lift_equationWord_toLinearSystem_val`
- the row identity hypothesis
- the new simp lemma

This removes the local proof detour and makes the row-to-relator bridge much
more direct.

## EPR-Side Cleanup with the New Structure

Because the EPR layer now takes `strat : BipartiteObservableStrategy n G`, it
should no longer carry local abbreviations rebuilding the projector strategy
from raw fields.

Use the existing structure-level API directly:

```lean
strat.toProjectorStrategy
```

and the bridge lemmas:

```lean
alice_A_bipartite
bob_B_bipartite
aliceRowProd_bipartite
```

So `rowObservableProduct_eq_sign_of_local_loss` should stay conceptually as:

1. choose `j` from row nonemptiness,
2. identify `Alice_A`, `Bob_B`, and `Alice_Row_Prod` via the bipartite lemmas,
3. apply `local_matrix_identities_of_local_loss_annihilate_epr`,
4. extract the row identity.

The main simplification here is not a new abbreviation, but deleting any
remaining wrapper constructors between:

- `strat : BipartiteObservableStrategy n G`,
- row identities,
- equation relator proofs,
- the final group representation.

## Recommended Intermediate Constructor

If an intermediate public constructor remains useful, it should be row-based and
game-facing:

```lean
noncomputable def solutionGroupRepresentationOfRows
    (game : LCSGame G)
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hrow :
      ∀ i, rowObservableProduct obs i =
        (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ)) :
    SolutionGroup game.toLinearSystem →* (Matrix n n ℂ)ˣ
```

This would sit naturally between:

- the generic linear-system constructor, and
- the EPR constructor.

It is a better intermediate API than the current equation-proof wrapper because
row identities are the actual mathematical output of the EPR/SOS argument.

## Proposed Final File Shape

Aim for a file organized around this narrative:

1. `solutionGroupGeneratorImage`
2. `solutionGroupRepresentation`
3. `rowObservableProduct`
4. `lift_equationRelator_of_rowIdentity`
5. `solutionGroupRepresentationOfRows`
6. `solutionGroupRepresentationOfEPRLoss`

Everything else should be:

- a private helper,
- a public simp lemma with clear downstream value,
- or deleted if it only forwards another result.

## Expected Outcome

After the new bipartite structure, the right simplification is:

1. keep the generic presented-group layer generic,
2. keep the game/EPR layer structured around `BipartiteObservableStrategy`,
3. remove wrappers that merely shuttle data between those layers,
4. expose row identities, not equation-proof bureaucracy, as the main bridge.

The end result is the same representation

```text
SolutionGroup(game.toLinearSystem) → (Matrix n n ℂ)ˣ
```

but with a shorter proof pipeline and a cleaner abstraction boundary.
