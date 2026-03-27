import LCS.Strategy.ProjectorStrategy
import LCS.Strategy.ObservableStrategy

open ObservableStrategy

noncomputable def ObservableStrategy_To_ProjectorStrategy
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G)
 :
  LCSStrategy R G :=
  {
    E := sorry
    F := sorry
    alice_ms := sorry
    bob_ms := sorry
    commute := sorry
  }
