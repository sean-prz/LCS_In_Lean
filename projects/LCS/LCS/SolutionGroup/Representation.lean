import LCS.EPR
import LCS.SolutionGroup

/-!
# Representations of Solution Groups

This module constructs matrix representations of an LCS solution group from the
local identities extracted by the EPR/local-loss pipeline.
-/

open scoped BigOperators

namespace SolutionGroup

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

section PresentedGroupConstruction

variable {S : LinearSystem}
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The intended image of the solution-group generators in matrix units. -/
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

/-- A representation of a solution group from a proof that the proposed generator
images satisfy all defining relators. -/
noncomputable def solutionGroupRepresentationOfRelatorProof
    (obs : Fin S.layout.s → Matrix n n ℂ)
    (obs_is_observable : ∀ j, IsObservable (obs j))
    (hrel :
      ∀ r ∈ solutionRelators S,
        FreeGroup.lift (solutionGroupGeneratorImage obs obs_is_observable) r = 1) :
    SolutionGroup S →* (Matrix n n ℂ)ˣ :=
  PresentedGroup.toGroup hrel

/-- Discharge the non-equation relators from the observable/unit structure, leaving
only the equation-word relators as explicit obligations. -/
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
    have hv :
        solutionGroupGeneratorImage obs obs_is_observable (.var j) ^ 2 = 1 := by
      ext a b
      change ((obs j) ^ 2) a b = (1 : Matrix n n ℂ) a b
      have hm : (obs j) ^ 2 = (1 : Matrix n n ℂ) := by
        simpa [pow_two] using (obs_is_observable j).involutive
      exact congrFun (congrFun hm a) b
    simpa [involutionRel, genVar] using hv
  · subst r
    have hJ :
        solutionGroupGeneratorImage obs obs_is_observable .J ^ 2 = 1 := by
      ext
      simp [solutionGroupGeneratorImage, negOneMatrixUnit, involutiveMatrixUnit]
    simpa [involutionRel, genJ] using hJ
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

/-- Construct a solution-group representation once the equation relators have
been proved for the proposed observable images. -/
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

section RepresentationData

variable {G : LCSLayout}
variable (game : LCSGame G)
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (obs : Fin G.s → Matrix n n ℂ)

/-- The local product of observables in equation `i`, in the same order as
`Alice_Row_Prod`. -/
noncomputable def rowObservableProduct
    (i : Fin G.r)
  (sameEquation_comm :
      ∀ i, Pairwise (fun j k : G.V i => Commute (obs j.1) (obs k.1))) :
    Matrix n n ℂ :=
  (G.V i).attach.noncommProd (fun j => obs j.1)
    (fun _ _ _ _ hjk => sameEquation_comm i hjk)

lemma sameEquation_toLinearSystem_iff
    (j k : Fin G.s) :
    sameEquation game.toLinearSystem j k ↔
      ∃ i : Fin G.r, j ∈ G.V i ∧ k ∈ G.V i := by
  simp [sameEquation, LCSGame.toLinearSystem]

lemma eqSupport_toLinearSystem
    (i : Fin G.r) :
    eqSupport game.toLinearSystem i = G.V i := by
  ext j
  simp [eqSupport, LCSGame.toLinearSystem]

omit [DecidableEq n] in
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

/-- A representation for `game.toLinearSystem` once the equation-word relators
are proved for the observable images. -/
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

lemma bob_B_observableStrategy
    (S : ObservableStrategyData (Matrix n n ℂ) G)
    (j : Fin G.s) :
    Bob_B (ObservableStrategy_To_ProjectorStrategy S) j = S.bob_obs j := by
  change ObservableOfMeasurementSystem (BobMeasurementFromObservables S j) =
    S.bob_obs j
  ext a b
  simp [ObservableOfMeasurementSystem, BobMeasurementFromObservables,
    ObservableToProjector, observableSign]
  ring

/-- End-to-end representation constructor from the EPR/local-loss hypothesis.

The proof currently uses `sorry` for the remaining bridge from the extracted
local matrix identities to the equation-word relators.  The surrounding shape is
the intended final proof: build the generator images, prove the relators, and
invoke the universal property `PresentedGroup.toGroup`.
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
      let Sobs : ObservableStrategyData (Matrix (n × n) (n × n) ℂ) G :=
        BipartiteObservableStrategy obs obs_is_observable sameEquation_comm
      let strat : LCSStrategy (Matrix (n × n) (n × n) ℂ) G :=
        ObservableStrategy_To_ProjectorStrategy Sobs
      let row :=
        rowObservableProduct obs i sameEquation_comm
      have hrow :
          row = (-1 : ℂ) ^ (game.b i).val • (1 : Matrix n n ℂ) := by
        classical
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
            bipartiteAliceLift (rowObservableProduct obs i sameEquation_comm)
          unfold Alice_Row_Prod rowObservableProduct
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
      -- Intended proof:
      -- rewrite `equationRelator game.toLinearSystem i`, evaluate
      -- `FreeGroup.lift solutionGroupGeneratorImage`, identify the sorted
      -- support product with `row`, and use `hrow` to match `J ^ b_i`.
      sorry)

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
