import LCS.Basic
import LCS.Common
import LCS.Observable

open scoped BigOperators

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

/-- Converts an observable $O$ and an outcome $a \in \{0, 1\}$ to a projector $P = (1/2)(I + (-1)^a O)$. -/
noncomputable def ObservableToProjector
  (O : R) (a : Fin 2) : R :=
  (1 / 2 : ℂ) • (1 + observableSign a • O)

lemma star_observableToProjector (O : R) (hO : IsObservable O) (a : Fin 2) :
    star (ObservableToProjector O a) = ObservableToProjector O a := by
  sorry

lemma idempotent_observableToProjector (O : R) (hO : IsObservable O) (a : Fin 2) :
    ObservableToProjector O a * ObservableToProjector O a = ObservableToProjector O a := by
  sorry

lemma orthogonal_observableToProjector (O : R) (hO : IsObservable O) :
    ObservableToProjector O 0 * ObservableToProjector O 1 = 0 := by
  sorry

lemma sum_one_observableToProjector (O : R) :
    ObservableToProjector O 0 + ObservableToProjector O 1 = 1 := by
  sorry

lemma commute_observableToProjector {O1 O2 : R} (h : Commute O1 O2) (a b : Fin 2) :
    Commute (ObservableToProjector O1 a) (ObservableToProjector O2 b) := by
  sorry
