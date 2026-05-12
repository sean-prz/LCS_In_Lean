import LCS.EPR
import LCS.SolutionGroup

/-!
# Representations of Solution Groups

This module constructs matrix representations of an LCS solution group from the
local identities extracted by the EPR/local-loss pipeline.

The intended representation sends the solution-group generators to matrix units:

* `var j` is sent to the observable matrix `obs j`;
* `J` is sent to the scalar matrix `-I`.

The main work is proving that this assignment respects the relators in the
presentation of the solution group.  The definitions are layered as follows.

```text
solutionGroupRepresentationOfEPRLoss
└─ solutionGroupRepresentationOfGameEquationProof
   └─ solutionGroupRepresentationOfEquationProof
      ├─ solutionGroupRelatorProofOfEquationProof
      │  ├─ observable/involutive facts for var^2 and J^2
      │  ├─ commutation of -I with every unit
      │  ├─ same-equation commutation of observable units
      │  └─ equation relator proofs
      └─ solutionGroupRepresentationOfRelatorProof
         └─ PresentedGroup.toGroup
```

The EPR-specific constructor builds the missing equation-relator proofs by:

```text
local loss annihilates the EPR vector
  ↓ local_matrix_identities_of_local_loss_annihilate_epr
row observable product = (-I) ^ b_i
  ↓ lift_equationRelator_toLinearSystem_of_row
equationRelator i maps to 1
```

Thus the top-level theorem is mostly plumbing: analytic local identities imply
the row equations, row equations imply all equation relators, and the generic
presented-group universal property then produces the representation.
-/

open scoped BigOperators

namespace SolutionGroup

/-!
## Matrix units

The target group of a representation is `(Matrix n n ℂ)ˣ`, so observable
matrices must first be packaged as units.  Since an observable is involutive,
its inverse is itself.  The distinguished solution-group generator `J` is
represented by the unit `-I`.
-/

section MatrixUnits

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix whose square is `1` as a unit. -/
noncomputable def involutiveMatrixUnit
    (M : Matrix n n ℂ) (hM : M * M = 1) : (Matrix n n ℂ)ˣ where
  val := M
  inv := M
  val_inv := hM
  inv_val := hM

/-- An observable matrix as a unit, using its involutivity. -/
noncomputable def observableMatrixUnit
    (M : Matrix n n ℂ) (hM : IsObservable M) : (Matrix n n ℂ)ˣ :=
  involutiveMatrixUnit M hM.involutive

/-- The scalar matrix `-I` as a unit. -/
noncomputable def negOneMatrixUnit : (Matrix n n ℂ)ˣ :=
  involutiveMatrixUnit ((-1 : ℂ) • (1 : Matrix n n ℂ)) (by
    rw [smul_mul_smul]
    simp)

@[simp] lemma involutiveMatrixUnit_val
    (M : Matrix n n ℂ) (hM : M * M = 1) :
    (involutiveMatrixUnit M hM : Matrix n n ℂ) = M :=
  rfl

@[simp] lemma observableMatrixUnit_val
    (M : Matrix n n ℂ) (hM : IsObservable M) :
    (observableMatrixUnit M hM : Matrix n n ℂ) = M :=
  rfl

@[simp] lemma negOneMatrixUnit_val :
    (negOneMatrixUnit (n := n) : Matrix n n ℂ) =
      (-1 : ℂ) • (1 : Matrix n n ℂ) :=
  rfl

@[simp] lemma involutiveMatrixUnit_sq
    (M : Matrix n n ℂ) (hM : M * M = 1) :
    involutiveMatrixUnit M hM ^ 2 = 1 := by
  apply Units.ext
  simpa [pow_two, involutiveMatrixUnit] using hM

@[simp] lemma observableMatrixUnit_sq
    (M : Matrix n n ℂ) (hM : IsObservable M) :
    observableMatrixUnit M hM ^ 2 = 1 := by
  simp [observableMatrixUnit]

@[simp] lemma negOneMatrixUnit_sq :
    negOneMatrixUnit (n := n) ^ 2 = 1 := by
  simp [negOneMatrixUnit]

lemma bipartiteAliceLift_noncommProd
    {α : Type*} (s : Finset α) (f : α → Matrix n n ℂ)
    (comm : (s : Set α).Pairwise (fun x y => Commute (f x) (f y))) :
    bipartiteAliceLift (s.noncommProd f comm) =
      s.noncommProd (fun x => bipartiteAliceLift (f x))
        (fun _ hx _ hy hxy => bipartiteAliceLift_commute (comm hx hy hxy)) := by
  classical
  induction s using Finset.cons_induction_on with
  | empty =>
      simp [bipartiteAliceLift]
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Finset.noncommProd_cons]
      rw [← bipartiteAliceLift_mul, ih]

end MatrixUnits

/-!
## Generic presented-group construction

This section is independent of a concrete `LCSGame`.  It starts with a
`LinearSystem S` and a proposed image of the solution-group generators.

There are three levels:

* `solutionGroupRepresentationOfRelatorProof` is the raw universal-property
  constructor: if every relator maps to `1`, the generator map descends to a
  homomorphism out of `SolutionGroup S`.
* `solutionGroupRelatorProofOfEquationProof` proves the all-relators hypothesis
  from structured assumptions: generator involutions, centrality of `J`,
  same-equation commutation, and the equation relators.
* `solutionGroupRepresentationOfEquationProof` packages those two steps.  It
  automatically handles the `J`-commutation and unit-lifting details, leaving
  only matrix commutation and equation-relator proofs to the caller.
-/

section PresentedGroupConstruction

variable {S : LinearSystem}
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The intended image of the solution-group generators in matrix units.

This is the generator-level assignment that all later constructors try to
descend through the quotient defining `SolutionGroup S`:

```text
var j ↦ obs j
J     ↦ -I
```
-/
noncomputable def solutionGroupGeneratorImage
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j)) :
    SolutionGen S → (Matrix n n ℂ)ˣ
  | .var j => observableMatrixUnit (obs j) (obs_is_observable j)
  | .J => negOneMatrixUnit

lemma solutionGroupGeneratorImage_var
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (j : Fin S.layout.s) :
    solutionGroupGeneratorImage obs obs_is_observable (.var j) =
      observableMatrixUnit (obs j) (obs_is_observable j) :=
  rfl

lemma solutionGroupGeneratorImage_J
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j)) :
    solutionGroupGeneratorImage obs obs_is_observable .J =
      negOneMatrixUnit :=
  rfl

/-- The raw universal-property constructor for solution-group representations.

The input `hrel` says that every defining relator of `SolutionGroup S` maps to
`1` under the free-group lift of `solutionGroupGeneratorImage`.  With that
proof in hand, `PresentedGroup.toGroup` descends the generator assignment to a
group homomorphism

```lean
SolutionGroup S →* (Matrix n n ℂ)ˣ
```

This definition does not prove any relators itself; it only consumes the full
relator proof.
-/
noncomputable def solutionGroupRepresentationOfRelatorProof
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hrel :
      ∀ r ∈ solutionRelators S,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable) r = 1) :
    SolutionGroup S →* (Matrix n n ℂ)ˣ :=
  PresentedGroup.toGroup hrel

/-- Build the full relator proof from the natural structured assumptions.

The solution-group presentation has five families of relators:

* variable involutions, `var j ^ 2 = 1`;
* the involution relation for `J`;
* centrality of `J`;
* commutation of variables that appear in a common equation;
* the equation relators themselves.

The first two are discharged from `obs_is_observable` and the fact that `J`
maps to `-I`.  The next two are supplied by `hJcomm` and `hsame`.  The final
family is exactly `hequation`.
-/
lemma solutionGroupRelatorProofOfEquationProof
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hJcomm :
      ∀ j,
        Commute
          (solutionGroupGeneratorImage obs obs_is_observable (.var j))
          (solutionGroupGeneratorImage obs obs_is_observable .J))
    (hsame :
      ∀ {j k}, sameEquation S j k →
        Commute
          (solutionGroupGeneratorImage obs obs_is_observable (.var j))
          (solutionGroupGeneratorImage obs obs_is_observable (.var k)))
    (hequation :
      ∀ i,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable)
          (equationRelator S i) = 1) :
    ∀ r ∈ solutionRelators S,
      FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable) r = 1 := by
  intro r hr
  rcases hr with hvar | hJ | hcentral | hcomm | heq
  · rcases hvar with ⟨j, rfl⟩
    simp [involutionRel, genVar, solutionGroupGeneratorImage]
  · subst r
    simp [involutionRel, genJ, solutionGroupGeneratorImage]
  · rcases hcentral with ⟨j, rfl⟩
    have h := (hJcomm j).eq
    simpa [commuteRel, genVar, genJ, solutionGroupGeneratorImage, mul_assoc] using
      mul_inv_eq_one.mpr h
  · rcases hcomm with ⟨j, k, _hjk, hsameEq, rfl⟩
    have h := (hsame hsameEq).eq
    simpa [commuteRel, genVar, solutionGroupGeneratorImage, mul_assoc] using
      mul_inv_eq_one.mpr h
  · rcases heq with ⟨i, rfl⟩
    exact hequation i

/-- Commuting matrices give commuting observable matrix units. -/
lemma observableMatrixUnit_commute_of_commute
    {M N : Matrix n n ℂ} {hM : IsObservable M} {hN : IsObservable N}
    (h : Commute M N) :
    Commute (observableMatrixUnit M hM) (observableMatrixUnit N hN) := by
  apply Units.ext
  exact h.eq

/-- The distinguished image of `J`, namely `-I`, commutes with every matrix unit. -/
lemma commute_negOneMatrixUnit
    (U : (Matrix n n ℂ)ˣ) :
    Commute U negOneMatrixUnit := by
  apply Units.ext
  simp [negOneMatrixUnit, involutiveMatrixUnit]

/-- Construct a representation once the equation relators are known.

This is the main generic constructor used by later sections.  It packages the
two lower-level steps:

```text
hsame + hequation
  ↓ solutionGroupRelatorProofOfEquationProof
all relators map to 1
  ↓ solutionGroupRepresentationOfRelatorProof
SolutionGroup S →* (Matrix n n ℂ)ˣ
```

The call to `solutionGroupRelatorProofOfEquationProof` also inserts two routine
facts: `-I` commutes with every matrix unit, and matrix-level commutation of
observables lifts to commutation of the corresponding units.
-/
noncomputable def solutionGroupRepresentationOfEquationProof
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hsame :
      ∀ {j k}, sameEquation S j k → Commute (obs j) (obs k))
    (hequation :
      ∀ i,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable)
          (equationRelator S i) = 1) :
    SolutionGroup S →* (Matrix n n ℂ)ˣ :=
  solutionGroupRepresentationOfRelatorProof obs obs_is_observable <|
    solutionGroupRelatorProofOfEquationProof obs obs_is_observable
      (fun _ => commute_negOneMatrixUnit _)
      (fun {j k} h =>
        observableMatrixUnit_commute_of_commute
          (hM := obs_is_observable j) (hN := obs_is_observable k) (hsame h))
      hequation

@[simp] lemma solutionGroupRepresentationOfRelatorProof_var
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hrel :
      ∀ r ∈ solutionRelators S,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable) r = 1)
    (j : Fin S.layout.s) :
    solutionGroupRepresentationOfRelatorProof obs obs_is_observable hrel
        (SolutionGroup.var (S := S) j) =
      observableMatrixUnit (obs j) (obs_is_observable j) := by
  simp [solutionGroupRepresentationOfRelatorProof, SolutionGroup.var,
    solutionGroupGeneratorImage]

@[simp] lemma solutionGroupRepresentationOfRelatorProof_J
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hrel :
      ∀ r ∈ solutionRelators S,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable) r = 1) :
    solutionGroupRepresentationOfRelatorProof obs obs_is_observable hrel
        (SolutionGroup.J (S := S)) =
      negOneMatrixUnit := by
  simp [solutionGroupRepresentationOfRelatorProof, SolutionGroup.J,
    solutionGroupGeneratorImage]

end PresentedGroupConstruction

/-!
## Game-level and EPR-level constructors

The previous section works for an arbitrary `LinearSystem`.  This section
specializes it to `game.toLinearSystem` and supplies equation-relator proofs
from the local identities produced by the EPR/local-loss pipeline.

The key bridge is:

```text
rowObservableProduct obs i = (-1) ^ (game.b i).val • I
  ↓ lift_equationRelator_toLinearSystem_of_row
equationRelator game.toLinearSystem i maps to 1
```

The top-level constructor `solutionGroupRepresentationOfEPRLoss` obtains that
row identity from `local_matrix_identities_of_local_loss_annihilate_epr`.
-/

section RepresentationData

variable {G : LCSLayout}
variable (game : LCSGame G)
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (obs : Fin G.s → Matrix n n ℂ)

/-- The canonical ordered product over the support of row `i`.

The product is taken over the sorted support list.  This fixes an order that
matches `equationWord`, which is useful when translating between free-group
words and matrix products.
-/
noncomputable def orderedSupportProduct
    {M : Type*} [Monoid M]
    (f : Fin G.s → M) (i : Fin G.r) : M :=
  (((G.V i).sort (· ≤ ·)).map f).prod

/-- The local product of observables in equation `i`.

This is the matrix-side version of the equation word for row `i`, using the
same sorted support order as `equationWord`.
-/
noncomputable def rowObservableProduct
    (i : Fin G.r) :
    Matrix n n ℂ :=
  orderedSupportProduct (G := G) obs i

/-- Relate the sorted row product to `Finset.noncommProd`.

This is the monoid-level support-product lemma.  The sorted list fixes the same
canonical order used by `equationWord`, while `noncommProd` is convenient for
strategy row products.  Pairwise commutation makes the two presentations agree.
-/
lemma orderedSupportProduct_eq_noncommProd
    {M : Type*} [Monoid M]
    (f : Fin G.s → M)
    (i : Fin G.r)
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (f j.1) (f k.1))) :
    orderedSupportProduct (G := G) f i =
      (G.V i).attach.noncommProd (fun j => f j.1)
        (fun _ _ _ _ hjk => sameEquation_comm i hjk) := by
  let support : List (G.V i) :=
    ((G.V i).sort (· ≤ ·)).pmap
      (fun j hj =>
        ⟨j, by
          simpa using (Finset.mem_sort (s := G.V i) (r := (· ≤ ·))).mp hj⟩)
      (by intro _ hj; exact hj)
  have hsupport_toFinset : support.toFinset = (G.V i).attach := by
    ext j
    simp [support]
  have hsupport_prod :
      (support.map (fun j => f j.1)).prod =
        orderedSupportProduct (G := G) f i := by
    simp [support, orderedSupportProduct]
  have hsupport_nodup : support.Nodup := by
    dsimp [support]
    apply List.Nodup.pmap
    · intro _ _ _ _ h
      exact Subtype.ext_iff.mp h
    · exact Finset.sort_nodup (G.V i) (· ≤ ·)
  symm
  rw [← hsupport_toFinset]
  rw [Finset.noncommProd_toFinset]
  · exact hsupport_prod
  · exact hsupport_nodup

/-- Relate the sorted row product to the `noncommProd` used by `Alice_Row_Prod`.

`rowObservableProduct` uses a sorted list to match `equationWord`, while
`Alice_Row_Prod` uses `Finset.noncommProd` over the attached row support.  When
the observables in the row commute pairwise, these products agree.
-/
lemma rowObservableProduct_eq_noncommProd
    (i : Fin G.r)
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))) :
    rowObservableProduct obs i =
      (G.V i).attach.noncommProd (fun j => obs j.1)
        (fun _ _ _ _ hjk => sameEquation_comm i hjk) := by
  exact orderedSupportProduct_eq_noncommProd obs i sameEquation_comm

/-- In `game.toLinearSystem`, `sameEquation` means membership in a common row. -/
lemma sameEquation_toLinearSystem_iff
    (j k : Fin G.s) :
    sameEquation game.toLinearSystem j k ↔
      ∃ i : Fin G.r, j ∈ G.V i ∧ k ∈ G.V i := by
  simp [sameEquation, LCSGame.toLinearSystem]

/-- The linear-system support of equation `i` is the game row support `G.V i`. -/
lemma eqSupport_toLinearSystem
    (i : Fin G.r) :
    eqSupport game.toLinearSystem i = G.V i := by
  ext j
  simp [eqSupport, LCSGame.toLinearSystem]

/-- Evaluate the free-group lift of a list of variable generators as matrices. -/
lemma lift_genVar_list_prod_val
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (l : List (Fin G.s)) :
    ((FreeGroup.lift
        (solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable)
        (l.map (genVar (S := game.toLinearSystem))).prod :
      (Matrix n n ℂ)ˣ) : Matrix n n ℂ) =
        (l.map obs).prod := by
  induction l with
  | nil =>
      simp
  | cons j l ih =>
      simp [genVar, solutionGroupGeneratorImage, ih]

/-- Evaluating an equation word gives the corresponding row observable product. -/
lemma lift_equationWord_toLinearSystem_val
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (i : Fin G.r) :
    ((FreeGroup.lift
        (solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable)
      (equationWord game.toLinearSystem i) : (Matrix n n ℂ)ˣ) :
      Matrix n n ℂ) =
        rowObservableProduct obs i := by
  classical
  simpa [equationWord, eqSupport_toLinearSystem, rowObservableProduct,
    orderedSupportProduct] using
      (lift_genVar_list_prod_val game obs obs_is_observable
        ((G.V i).sort (· ≤ ·)))

/-- Turn a row matrix identity into the corresponding equation-relator proof.

If the observable product in row `i` is `(-I) ^ b_i`, then the equation relator
for row `i` maps to `1` under `solutionGroupGeneratorImage`.
-/
lemma lift_equationRelator_toLinearSystem_of_row
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (i : Fin G.r)
    (hrow :
      rowObservableProduct obs i =
        (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ)) :
    FreeGroup.lift
        (solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable)
        (equationRelator game.toLinearSystem i) = 1 := by
  have hword :=
    lift_equationWord_toLinearSystem_val game
      obs obs_is_observable i
  have hwordUnit :
      FreeGroup.lift
          (solutionGroupGeneratorImage (S := game.toLinearSystem)
            obs obs_is_observable)
          (equationWord game.toLinearSystem i) =
        solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable .J ^ (game.b i).val := by
    apply Units.ext
    change
      ((FreeGroup.lift
          (solutionGroupGeneratorImage (S := game.toLinearSystem)
            obs obs_is_observable)
          (equationWord game.toLinearSystem i) : (Matrix n n ℂ)ˣ) :
        Matrix n n ℂ) =
      ((solutionGroupGeneratorImage (S := game.toLinearSystem)
          obs obs_is_observable .J ^ (game.b i).val :
        (Matrix n n ℂ)ˣ) : Matrix n n ℂ)
    rcases fin2_eq_zero_or_one (game.b i) with hb | hb
    · rw [hb] at hrow
      simp [hword, hrow, solutionGroupGeneratorImage,
        hb]
    · rw [hb] at hrow
      simp [hword, hrow, solutionGroupGeneratorImage,
        negOneMatrixUnit, involutiveMatrixUnit, hb]
  have hbLinear : game.toLinearSystem.b i = game.b i := rfl
  simp [equationRelator, genJ, hwordUnit, hbLinear]

omit [DecidableEq n] in
/-- Convert row-wise commutation into `sameEquation` commutation for
`game.toLinearSystem`. -/
lemma sameEquation_comm_of_row_comm
    (obs : Fin G.s → Matrix n n ℂ)
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    {j k : Fin G.s}
    (hjk : sameEquation game.toLinearSystem j k) :
    Commute (obs j) (obs k) := by
  rcases (sameEquation_toLinearSystem_iff game j k).mp hjk with
    ⟨i, hj, hk⟩
  by_cases h : (⟨j, hj⟩ : G.V i) = ⟨k, hk⟩
  · have hjk_eq : j = k := Subtype.ext_iff.mp h
    subst k
    exact Commute.refl _
  · exact sameEquation_comm i h

/-- Game-specialized representation constructor.

This is `solutionGroupRepresentationOfEquationProof` with
`S = game.toLinearSystem`.  The only extra work is translating the row-wise
commutation hypothesis into the `sameEquation` form expected by the generic
constructor.
-/
noncomputable def solutionGroupRepresentationOfGameEquationProof
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hequation :
      ∀ i,
        FreeGroup.lift
            (solutionGroupGeneratorImage (S := game.toLinearSystem)
              obs obs_is_observable)
          (equationRelator game.toLinearSystem i) = 1) :
    SolutionGroup game.toLinearSystem →* (Matrix n n ℂ)ˣ :=
  solutionGroupRepresentationOfEquationProof
    (S := game.toLinearSystem) obs obs_is_observable
    (sameEquation_comm_of_row_comm game obs sameEquation_comm)
    hequation

/-- Extract the row equation from the EPR/local-loss hypothesis.

For each row `i`, the local loss for any support element contains the row SOS
term.  Since the row is assumed nonempty, one such support element is enough to
recover

```lean
rowObservableProduct obs i = (-1) ^ (game.b i).val • I
```

This isolates the analytic EPR/SOS step from the presented-group construction.
-/
lemma rowObservableProduct_eq_sign_of_local_loss
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hNonempty : ∀ i, Nonempty (G.V i))
    (hLoss :
      ∀ i (j : G.V i),
        Matrix.mulVec
          (local_loss_operator game
            (ObservableStrategy_To_ProjectorStrategy
              (BipartiteObservableStrategy
                obs obs_is_observable sameEquation_comm))
            i j)
          (eprVec n) = 0)
    (i : Fin G.r) :
    rowObservableProduct obs i =
      (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ) := by
  classical
  let Sobs : ObservableStrategyData (Matrix (n × n) (n × n) ℂ) G :=
    BipartiteObservableStrategy obs obs_is_observable sameEquation_comm
  let strat : LCSStrategy (Matrix (n × n) (n × n) ℂ) G :=
    ObservableStrategy_To_ProjectorStrategy Sobs
  let row := rowObservableProduct obs i
  change row = (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ)
  rcases hNonempty i with ⟨j⟩
  have hAlice :
      Alice_A strat i j = bipartiteAliceLift (obs j.1) := by
    simpa [strat, Sobs, BipartiteObservableStrategy] using
      (alice_A_observableStrategy
        (BipartiteObservableStrategy obs obs_is_observable sameEquation_comm)
        i j)
  have hBob :
      Bob_B strat j.1 = bipartiteBobLift (obs j.1) := by
    simpa [strat, Sobs, BipartiteObservableStrategy] using
      (bob_B_observableStrategy
        (BipartiteObservableStrategy obs obs_is_observable sameEquation_comm)
        j.1)
  have hRowLift :
      Alice_Row_Prod strat i = bipartiteAliceLift row := by
    change Alice_Row_Prod strat i =
      bipartiteAliceLift (rowObservableProduct obs i)
    rw [rowObservableProduct_eq_noncommProd
      (sameEquation_comm := sameEquation_comm)]
    unfold Alice_Row_Prod
    rw [bipartiteAliceLift_noncommProd]
    refine Finset.noncommProd_congr rfl ?_ ?_
    intro k _
    simpa [strat, Sobs, BipartiteObservableStrategy] using
      (alice_A_observableStrategy
        (BipartiteObservableStrategy obs obs_is_observable sameEquation_comm)
        i k)
  exact
    (local_matrix_identities_of_local_loss_annihilate_epr
      game n strat i j (obs j.1) (obs j.1) row
      (hLoss i j) hAlice hBob hRowLift (obs_is_observable j.1)).2.1

/-- End-to-end representation constructor from the EPR/local-loss hypothesis.

This is the main constructor in the file.  It builds the representation

```lean
SolutionGroup game.toLinearSystem →* (Matrix n n ℂ)ˣ
```

with generator images `var j ↦ obs j` and `J ↦ -I`.

The proof supplies `solutionGroupRepresentationOfGameEquationProof` with an
equation-relator proof for every row.  For a fixed row `i`, it:

1. builds the bipartite observable strategy from `obs`;
2. uses the local-loss hypothesis on an arbitrary support element
   `j : G.V i`;
3. extracts the row identity
   `rowObservableProduct obs i = (-1) ^ (game.b i).val • I` via
   `local_matrix_identities_of_local_loss_annihilate_epr`;
4. turns that row identity into the equation-relator proof using
   `lift_equationRelator_toLinearSystem_of_row`.
-/
noncomputable def solutionGroupRepresentationOfEPRLoss
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hNonempty : ∀ i, Nonempty (G.V i))
    (hLoss :
      ∀ i (j : G.V i),
        Matrix.mulVec
          (local_loss_operator game
            (ObservableStrategy_To_ProjectorStrategy
              (BipartiteObservableStrategy
                obs obs_is_observable sameEquation_comm))
            i j)
          (eprVec n) = 0) :
    SolutionGroup game.toLinearSystem →* (Matrix n n ℂ)ˣ :=
  solutionGroupRepresentationOfGameEquationProof game
    obs obs_is_observable sameEquation_comm
    (by
      intro i
      exact
        lift_equationRelator_toLinearSystem_of_row game
          obs obs_is_observable i
          (rowObservableProduct_eq_sign_of_local_loss game
            obs obs_is_observable sameEquation_comm hNonempty hLoss i))

@[simp] lemma solutionGroupRepresentationOfEPRLoss_var
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hNonempty : ∀ i, Nonempty (G.V i))
    (hLoss :
      ∀ i (j : G.V i),
        Matrix.mulVec
          (local_loss_operator game
            (ObservableStrategy_To_ProjectorStrategy
              (BipartiteObservableStrategy
                obs obs_is_observable sameEquation_comm))
            i j)
          (eprVec n) = 0)
    (j : Fin G.s) :
    solutionGroupRepresentationOfEPRLoss game
        obs obs_is_observable sameEquation_comm hNonempty hLoss
        (SolutionGroup.var (S := game.toLinearSystem) j) =
      observableMatrixUnit (obs j) (obs_is_observable j) := by
  simp [solutionGroupRepresentationOfEPRLoss,
    solutionGroupRepresentationOfGameEquationProof,
    solutionGroupRepresentationOfEquationProof]

@[simp] lemma solutionGroupRepresentationOfEPRLoss_J
    (obs : Fin G.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1)))
    (hNonempty : ∀ i, Nonempty (G.V i))
    (hLoss :
      ∀ i (j : G.V i),
        Matrix.mulVec
          (local_loss_operator game
            (ObservableStrategy_To_ProjectorStrategy
              (BipartiteObservableStrategy
                obs obs_is_observable sameEquation_comm))
            i j)
          (eprVec n) = 0) :
    solutionGroupRepresentationOfEPRLoss game
        obs obs_is_observable sameEquation_comm hNonempty hLoss
        (SolutionGroup.J (S := game.toLinearSystem)) =
      negOneMatrixUnit := by
  simp [solutionGroupRepresentationOfEPRLoss,
    solutionGroupRepresentationOfGameEquationProof,
    solutionGroupRepresentationOfEquationProof]

end RepresentationData

end SolutionGroup
