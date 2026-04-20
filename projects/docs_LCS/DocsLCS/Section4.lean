
import VersoManual


-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso. Here, they're used to have the text refer to Verso code used in the text's
-- own source.
open Verso.Genre.Manual.InlineLean

-- This gets access to tools for showing Lean code that's loaded from external modules. need new
open Verso.Code.External


set_option pp.rawOnError true

set_option verso.exampleProject "../LCS"
set_option verso.exampleModule "LCS"


set_option verso.exampleModule "LCS.Strategy.ProjectorStrategy"
#doc (Manual) "Strategy Formalisms and Equivalence" =>

This chapter introduces the two strategy languages used in the project. The projector formalism is the one used to state the main winning-condition theorem, while the observable formalism is often the most natural one for concrete constructions such as Magic Square.

# Measurement Systems

The projector-based formalism starts from measurement systems. A measurement system is a finite family of pairwise orthogonal self-adjoint idempotents summing to `1`. This is the abstract interface used to represent a projective quantum measurement in the library.

```anchor IsMeasurementSystem (module := LCS.Measurement)
structure IsMeasurementSystem
  {I : Type*} [Fintype I]
  (f : I → R) : Prop where
  sum_one      : ∑ x, f x = 1
  idempotent   : ∀ x, f x * f x = f x
  orthogonal   : ∀ x y, x ≠ y → f x * f y = 0
  self_adjoint : ∀ x, star (f x) = f x
```

This definition is used twice in an LCS strategy: once for Alice's measurement attached to an equation, and once for Bob's binary measurement attached to a variable.

# Projector Strategies

The main strategy structure in the library is `LCSStrategy`. It packages Alice's projector-valued measurements, Bob's projector-valued measurements, and the commutation relation between the two players.

```anchor LCSStrategy (module := LCS.Strategy.ProjectorStrategy)
structure LCSStrategy
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R]
  (G : LCSLayout) where
  E : ∀ i, (Assignment G i → R)
  F : Fin G.s → (Fin 2 → R)
  alice_ms : ∀ i, IsMeasurementSystem (E i)
  bob_ms   : ∀ j, IsMeasurementSystem (F j)
  commute  : ∀ i j α β, E i α * F j β = F j β * E i α
```

The type of `E i` reflects the fact that Alice answers an entire local assignment when she is asked equation `i`. By contrast, `F j` is binary because Bob only answers one bit when asked variable `j`. The commutation field expresses the usual no-signalling style separation used in the commuting-operator framework.

# Derived Observables

Once a projector strategy is fixed, the library extracts observables from the measurement data. For Alice, the observable attached to a variable inside equation `i` is obtained by collapsing the assignment measurement according to the value of that variable. For Bob, the observable is the usual difference of the two binary projectors.

## Alice's observable

```anchor Alice_A (module := LCS.Strategy.ProjectorStrategy)
noncomputable def Alice_A
  (strat : LCSStrategy R G) (i : Fin G.r) (j : G.V i) : R :=
  ObservableOfMeasurementSystem (InducedMeasurementSystem (strat.E i) (fun x => x j))
```

## Bob's observable

```anchor Bob_B (module := LCS.Strategy.ProjectorStrategy)
def Bob_B (strat : LCSStrategy R G) (j : Fin G.s) : R :=
  ObservableOfMeasurementSystem (strat.F j)
```

These derived observables are what make the projector formalism compatible with the operator identities used later in the winning-condition chapter.

# Observable Strategies

For explicit constructions, it is often more natural to start directly from observables. The corresponding data structure in the library is `ObservableStrategyData`.

```anchor ObservableStrategyData (module := LCS.Strategy.ObservableStrategy)
structure ObservableStrategyData
  (R : Type*) [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  (G : LCSLayout) where
  alice_obs : Fin G.s → R
  bob_obs : Fin G.s -> R
  alice_observable : ∀ j, IsObservable (alice_obs j)
  bob_observable : ∀ j, IsObservable (bob_obs j)
  sameEquation_comm :
    ∀ i, Pairwise (fun j k : G.V i => Commute (alice_obs j.1) (alice_obs k.1))
  alice_bob_commute :
    ∀ j k, Commute (alice_obs j) (bob_obs k)
```

Instead of listing every projector in a measurement, this structure records one observable for each variable on Alice's side and one observable for each variable on Bob's side, together with the commutation hypotheses needed to talk about products of compatible observables.

In practice this is the convenient entry point for examples such as the Mermin-Peres Magic Square, where the strategy is first described in terms of Pauli-type observables and only later converted into projector measurements.

# From Observables to Projectors

The two strategy languages are not unrelated presentations of different mathematics. The library includes a construction in `LCS.Strategy.ObservableToProjector` that turns observable strategy data into projector-valued measurements, and `LCS.Strategy.Equivalence` develops the relation between the two viewpoints.

At the level of a single observable, the basic projector construction is:

```anchor ObservableToProjector (module := LCS.Strategy.ObservableToProjector)
noncomputable def ObservableToProjector
  (O : R) (a : Fin 2) : R :=
  (1 / 2 : ℂ) • (1 + observableSign a • O)
```

At the level of full strategies, the main bridge is the construction:

```anchor ObservableStrategy_To_ProjectorStrategy (module := LCS.Strategy.Equivalence)
noncomputable def ObservableStrategy_To_ProjectorStrategy
  {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  {G : LCSLayout}
  (S : ObservableStrategyData R G)
 :
  LCSStrategy R G :=
  {
    E := AliceMeasurementFromObservables S
    F := BobMeasurementFromObservables S
    alice_ms := aliceMeasurementFromObservables_isMeasurementSystem S
    bob_ms := bobMeasurementFromObservables_isMeasurementSystem S
    commute := aliceMeasurement_bobMeasurement_commute S
  }
```

This bridge is important for the overall architecture of the project:

- concrete examples are often easiest to state with observables,
- general winning operators are easiest to define with projectors,
- and the observable-to-projector construction lets the same example feed into the general theory.

# Summary

The project therefore uses two complementary formalisms rather than choosing only one. Projector strategies provide the right interface for summing over outcomes and defining winning operators, while observable strategies provide a compact and usable language for concrete operator constructions. The equivalence machinery is what allows the manual to move between them without changing mathematical meaning.
