import LCS.Basic
import LCS.Common
import LCS.Measurement
import LCS.Observable
open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {G : LCSLayout}
set_option linter.unusedSectionVars false

-- ANCHOR: LCSStrategy
structure LCSStrategy
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
  (G : LCSLayout) where
  E : ∀ i, (Assignment G i → R)
  F : Fin G.s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α
-- ANCHOR_END: LCSStrategy

-- ANCHOR: Alice_A
/-
noncomputable def Alice_A (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment G i) => x j = 0), strat.E i x) -
  (∑ x ∈ Finset.univ.filter (fun (x : Assignment G i) => x j = 1), strat.E i x)
-/
noncomputable def Alice_A
  (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  ObservableOfMeasurementSystem (InducedMeasurementSystem (strat.E i) (fun x => x j))
-- ANCHOR_END: Alice_A

-- ANCHOR: Bob_B
/-
def Bob_B (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  strat.F j 0 - strat.F j 1
-/
def Bob_B (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  ObservableOfMeasurementSystem (strat.F j)
-- ANCHOR_END: Bob_B



noncomputable def ObservableToProjector
  (O : R) (a : Fin 2) : R :=
  (1 / 2 : ℂ) • (1 + observableSign a • O)

lemma bob_is_observable (strat : LCSStrategy R G) (j : Fin G.s) :
  IsObservable (Bob_B strat j) :=
  is_observable_of_measurement_system (strat.F j) (strat.bob_ms j)

lemma alice_is_observable (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) :
  IsObservable (Alice_A strat i j) :=
  is_observable_of_measurement_system _
    (induced_measurement_system_is_measurement_system _ (strat.alice_ms i) _)


lemma alice_observables_commute (strat : LCSStrategy R G) (i : Fin G.r) (j j' : G.V i) :
  Commute (Alice_A strat i j) (Alice_A strat i j') := by
  let comm := measurement_commute_sum (strat.alice_ms i)
  exact Commute.sub_left (Commute.sub_right (comm _ _) (comm _ _))
    (Commute.sub_right (comm _ _) (comm _ _))

lemma alice_bob_commute (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) :
  Commute (Alice_A strat i j) (Bob_B strat j) := by
  unfold Alice_A Bob_B ObservableOfMeasurementSystem InducedMeasurementSystem
  apply Commute.sub_left <;> apply Commute.sub_right
  all_goals {
    apply Commute.sum_left
    intro x _
    apply strat.commute
  }

lemma bob_measurement_eq_projector (strat : LCSStrategy R G) (j : Fin G.s) (y : Fin 2) :
  strat.F j y = ObservableToProjector (Bob_B strat j) y := by
  classical
  unfold Bob_B ObservableOfMeasurementSystem ObservableToProjector observableSign
  have hsum := (strat.bob_ms j).sum_one
  rw [Fin.sum_univ_two] at hsum
  fin_cases y
  · simp only [← hsum]
    symm
    calc
      (1 / 2 : ℂ) • (strat.F j 0 + strat.F j 1 + (1 : ℂ) • (strat.F j 0 - strat.F j 1))
      _ = (1 / 2 : ℂ) • (strat.F j 0 + strat.F j 0) := by
        congr 1; simp only [one_smul]; abel
      _ = (1 / 2 : ℂ) • strat.F j 0 + (1 / 2 : ℂ) • strat.F j 0 := by
        rw [smul_add]
      _ = (1 / 2 + 1 / 2 : ℂ) • strat.F j 0 := by
        rw [add_smul]
      _ = strat.F j 0 := by
        norm_num
  · simp only [← hsum]
    symm
    calc
      (1 / 2 : ℂ) • (strat.F j 0 + strat.F j 1 + (-1 : ℂ) • (strat.F j 0 - strat.F j 1))
      _ = (1 / 2 : ℂ) • (strat.F j 1 + strat.F j 1) := by
        congr 1; simp only [neg_smul, one_smul]; abel
      _ = (1 / 2 : ℂ) • strat.F j 1 + (1 / 2 : ℂ) • strat.F j 1 := by
        rw [smul_add]
      _ = (1 / 2 + 1 / 2 : ℂ) • strat.F j 1 := by
        rw [add_smul]
      _ = strat.F j 1 := by
        norm_num
