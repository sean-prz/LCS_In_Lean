import LCS.Basic
import LCS.MeasurementLemmas

-- ANCHOR: winning_assignments
def winning_assignments
  {G : LCSLayout}
  (game : LCSGame G) (i : Fin G.r) : 
  Finset (Assignment G i) :=
  Finset.univ.filter (fun α => (∑ j : G.V i , (α j : ZMod 2)) = game.b i)
-- ANCHOR_END: winning_assignments


/-- The Winning Operator `v` for a given Strategy and Game. -/
noncomputable def winning_operator
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G) : R :=
  ∑ i : Fin G.r, ∑ j : G.V i,
  let normalization : ℂ := (G.r * (G.V i).card : ℕ)
  (1 / normalization) • (∑ x ∈ winning_assignments game i, strat.E i x * strat.F j (x j))

lemma lemma_4_7_1
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  {G : LCSLayout} (game : LCSGame G) (strat : LCSStrategy R G)
  (i : Fin G.r) :
  (∑ x ∈ winning_assignments game i, strat.E i x) = 
  (1/2 : ℂ) • (1 + (-1 : ℂ)^(game.b i).val • 
  ((G.V i).attach.noncommProd 
    (fun j => Alice_A strat i j) 
    (fun j hj j' hj' _ => alice_observables_commute strat i j j'))) :=
  by sorry
