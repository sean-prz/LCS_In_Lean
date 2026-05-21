# Refactor Proposal for `SolutionGroup/Representation.lean`

The main issue in `projects/LCS/LCS/SolutionGroup/Representation.lean` is that the representation construction is split across too many forwarding lemmas and wrappers. The mathematical content is fine, but the proof pipeline is longer than needed.

## Main Refactor

Collapse the public constructor stack to two layers:

1. `solutionGroupRepresentation`
   - Generic over `S : LinearSystem`.
   - Inputs:
     - `obs`
     - `obs_is_observable`
     - `hsame : forall {j k}, sameEquation S j k -> Commute (obs j) (obs k)`
     - `hequation : forall i, FreeGroup.lift ... (equationRelator S i) = 1`
   - Output:
     - `SolutionGroup S ->* (Matrix n n C)^x`
   - Implementation:
     - build the relator proof directly,
     - then call `PresentedGroup.toGroup`.

2. `solutionGroupRepresentationOfEPRLoss`
   - Game-specialized end-to-end constructor.
   - Responsibilities:
     - derive row identities from local loss,
     - convert row identities into equation-relator proofs,
     - call `solutionGroupRepresentation`.

This keeps the same mathematics but removes most of the boilerplate glue.

## Lemmas To Remove or Privatize

These appear to be mostly transport wrappers rather than stable API:

- `solutionGroupRepresentationOfRelatorProof`
- `solutionGroupRelatorProofOfEquationProof`
- `solutionGroupRepresentationOfGameEquationProof`
- `rowObservableProduct_eq_noncommProd`
- `solutionGroupGeneratorImage_var`
- `solutionGroupGeneratorImage_J`
- `sameEquation_toLinearSystem_iff`
- `eqSupport_toLinearSystem`
- `lift_genVar_list_prod_val`

Suggested treatment:

- delete wrappers that are one-line forwards,
- make one-off helper lemmas `private`,
- keep only the constructors and simp lemmas that are genuinely useful downstream.

## Most Valuable Proof Simplification

The biggest compression target is:

- `lift_equationRelator_toLinearSystem_of_row`

Right now it goes through:

1. `lift_equationWord_toLinearSystem_val`
2. a local `hwordUnit`
3. a case split on `fin2_eq_zero_or_one`

That can be shortened by adding a single lemma for the `J` image:

```lean
@[simp] lemma negOneMatrixUnit_pow_fin2_val (b : Fin 2) :
  ((negOneMatrixUnit (n := n) ^ b.val : (Matrix n n C)^x) : Matrix n n C)
    = (-1 : C) ^ b.val • (1 : Matrix n n C)
```

Then prove the relator by `Units.ext` using only:

- `lift_equationWord_toLinearSystem_val`
- the row identity hypothesis
- the new simp lemma above

This removes the local proof pipeline entirely.

## EPR-Side Cleanup

`rowObservableProduct_eq_sign_of_local_loss` also carries too much constructor plumbing.

Introduce local abbreviations such as:

```lean
noncomputable abbrev bipartiteStrategy :=
  ObservableStrategy_To_ProjectorStrategy
    (BipartiteObservableStrategy obs obs_is_observable sameEquation_comm)
```

and a bridge lemma like:

```lean
private lemma aliceRowProd_bipartiteStrategy :
  Alice_Row_Prod bipartiteStrategy i =
    bipartiteAliceLift (rowObservableProduct obs i)
```

After that, `rowObservableProduct_eq_sign_of_local_loss` reads much closer to the actual mathematical argument and avoids repeatedly expanding the same strategy constructors.

## Proposed Final File Shape

Aim for a file organized around these definitions and lemmas:

- `solutionGroupGeneratorImage`
- `solutionGroupRepresentation`
- `rowObservableProduct`
- `lift_equationRelator_of_rowIdentity`
- `solutionGroupRepresentationOfRows`
- `solutionGroupRepresentationOfEPRLoss`

Everything else should be either:

- a private helper,
- a simp lemma with clear downstream value,
- or deleted if it only forwards another result.

## Expected Outcome

This changes the file from a long wrapper pipeline into a shorter narrative:

1. define the generator image,
2. prove the relators,
3. descend to the presented group,
4. specialize row identities to equation relators,
5. specialize EPR loss to row identities.

The result is the same matrix representation of the LCS solution group, but with less indirection and less file bloat.
