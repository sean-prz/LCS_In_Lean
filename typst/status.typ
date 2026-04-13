#import "@preview/cheq:0.3.0": checklist
#set page("a4", margin: 1.75cm, numbering: "1.")
#show: checklist

#align(right)[Perazzolo Sean]

#align(center)[
  = Formalising the SOS Decomposition of LCS Games in Lean
]

#align(center)[
  *_Project Status Report_*
]



== Week By Week Recap.
#line()

#let week1_1 = [
  #set text(8pt)
  #set align(left + top)
  - Got familar with Proof assistant (cs-428 in rocq)
  - Setup Lean
  - Basic Proof in Lean
]
#let week1_2 = [
  #set text(8pt)
  #set align(left + top)
  - Read : "Characterization of Binary Constraint System Games" \ Got familiar with the Mermin-Peres game, and the notion of LCS games.
  - Read : "entanglement and non-locality in games and graphs", section 1. \ Understand the historical context of non-local games.
  - Review CHSH decomposition in SOS to prove tsirelson bound.
]


#let week3_1 = [
  #set text(8pt)
  #set align(left + top)
  - Working in \*-ring  [StarRing] instead of a Hilbert space.
  - Adapting from the CHSH.lean file.
  - Setup a formal definition of a commuting measurement systems ${E_(i,x)}$.
  - Formally defined the LCSStrategy
]
#let week3_2 = [
  #set text(8pt)
  #set align(left + top)
  - Assimilate the construction of the observable for a LCS strategy.
]


#let week4_1 = [
  #set text(8pt)
  #set align(left + top)
  - Made&Published documentation
  - Reworked the LCS framework (geometry of the game)
  - Defined an LCS game
]
#let week4_2 = [
  #set text(8pt)
  #set align(left + top)
  - Proved some measurement Lemmas
  - Tried Mermin-Peres square strategy.
]


#let week5_1 = [
  #set text(8pt)
  #set align(left + top)
  - Defined A strategy given in terms of Observable.
  - Attempt to prove that given a strategy defined in terms of observable, we can construct a strategy defined in terms of projectors.
  - Proved that $A^i_j$ $B_j$ are valid observables (Introduce InducedMeasurementSystem)
  - Reformulated the proof that Alice observable commute for different variables of the same equation.
]
#let week5_2 = [
  #set text(8pt)
  #set align(left + top)
  - Prove 4.7.1 & 4.7.2 of the paper (fully automated by Lean).
]

#let week6_1 = [
  #set text(8pt)
  #set align(left + top)
  - Proove equivalence of Strategy given in terms of Observable and Strategy given in terms of Projectors.
  - Add MathLib style documentation
]

#let week6_2 = [
  #set text(8pt)
  #set align(left + top)
  - Define Local Winning/Loss Operator for main proof
  - Introduce ObservableToProjector Lemmas
  - Reorganize codebase
]

#let week7_1 = [
  #set text(8pt)
  #set align(left + top)
  - Setup pauli matrices algebra
  - Define the game layout and the grid of obserables
  - Define a Bipartite Observable Strategy
  - Prove commutation to show that the Mermin-Peres square strategy is valid.
]

#let week7_2 = [
  #set text(8pt)
  #set align(left + top)
  - Add auxilary lemmas of commutation over Alice and Bob observables
  - Define Alice product of obserables for a given equation.
  - Decomposed the proof in 5 steps.
  - Add custom notation for readability.
  - Sectionned codebase for docs.
]


#table(
  columns: (0.5fr, 1fr, 1fr),
  stroke: none,
  gutter: 0em,
  align: (left + horizon, center + horizon, center + horizon),
  inset: 2.5pt,

  [#v(1em)], [  ], [  ],
  [*Week 1 & 2 *], [Introduction to Lean], [LCS & The Mermin-Peres game],
  [ ], [#week1_1], [#week1_2],
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt + gray.transparentize(80%)))],
  [*Week 3*], [Formalising a LCS Strategy], [4.7 SOS approach to solution group],
  // WEEK 03
  [ ], [#week3_1], [#week3_2],
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt + gray.transparentize(80%)))],
  [*Week 4*], table.cell(colspan: 2)[Starting Proofs, Meremin-Peres & Documentation],
  [ ], [#week4_1], [#week4_2],
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt + gray.transparentize(80%)))],
  [*Week 5*], [Observable to Strategy], [Prove 4.7.1 & 4.7.2],
  [ ], [#week5_1], [#week5_2],
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt + gray.transparentize(80%)))],
  [*Week 6*], [Observable to Strategy], [Prep work for SOS decomposition  ],
  [ ], [#week6_1], [#week6_2],
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt + gray.transparentize(80%)))],

  [*Week 7 + Easter Break*  \ _(Milestone 1&2)_],
  [*Show that the Magic Square Grid is \ a valid strategy*], [*Formalize The SOS Decomposition of an LCS game*],
  [ ], [#week7_1], [#week7_2],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt + gray.transparentize(80%)))],

  [], [.], [],
  [], [.], [],
  [], [.], [],
  [*Week ?*  _(Milestone 3)_ ], table.cell(colspan: 2)[--- *???*---],
)

//   [W. ?], [#align(right)[-----------------------------------]], [#align(left)[-----------------------------------]],






#pagebreak()
= Meetings
#line()
*Monday 11.15am in BC110* to debrief previous week and plan the next one.

== Week 6


1. *Add Condition to the ObservableStrategy Game*

- Missing in the description of the strategy was that each of Alice observable must commute with each of Bob observable.

2. *Define `ObservableToProjector` with Lemmas to prove the construction is a valid PVM*

3. *In `Equivalence.lean` prove that the strategy defined in terms of observable is equivalent to the strategy defined in terms of projector.*

- Easy for Bob, Long for Alice requires one or more lemmas per projector

4. *Introduce Local Winning/Loss Operator for main proof*

5. *Restructure the codebase*

Introduce `Game/` `Strategy/` and moved everything specific to a Projector based strategy in its own file, while keeping general lemmas about measurement and observable in their own files.

Goal :

- Read & Understand Proofs in Observable and WinningCondiiton.
- Try to finalize the Observable->Strategy file to show that the Mermin-Peres square strategy is valid.
- Start Main proof if tims allows.
- Catch up with the documentation.


== Week 5

1. *Showing that $A^i_j$ and $B_j$ are valid observables*.

_Observable.lean_

- Defining IsObservable as element that are self-adjoint and square to identity.
- Proving that $A^i_j$ and $B_j$ are valid observables so that we can use these properties in the main proof.
- To do this we introduce inducesMeasurementSystem
  + If we have a valid Projector family we can construct another family by mapping outcomes to 0 and 1.
  + Prove that for a binary projector family, P(0) - P(1) is an observable.
  + So we prove that $A^i_j$ is valid by showing that it is an induced measurement system where the parition function is given by the value of the variable in the equation, thus the observable that is the difference of the two projectors is exactly $A^i_j$.

2. *Proving 4.7.1 & 4.7.2* of the paper.

_WinningCondition.lean_

- Both Lemmas are needed in the main proof.
- Proofs were written fully by LLMs and then simplified with another pass of LLMs.

3. *Generalize last week attempt to show that the Mermin-Peres square strategy is valid*.

_ObservableStrategy.lean_

- Define a strategy given in terms of observable and try to prove that we can construct a strategy given in terms of projectors, which is the form of strategy we need for the proof.
- Endgoal is to use this to show that the Mermin-Peres square strategy is valid.
- LLMs switched to Module instead of Algebra.
- File is not worth looking at right now.

4. *General remarks*.
- Tried Codex and Antigravity, ran out of budget in one hour.

== Week 4 :


1. *Made&Published documentation*

Available for consultation, to use while debriefing and throughout the weeks to check on the progress.
The source raw files are also available at src/

_Use docs for the rest of the debrief._

2. *Reworked the LCS framework*
added geometry of the game to remove long signature.

3. *Defined an LCS game*
as just a function from index of contraints to the value of the constriants

4. *Tried Mermin-Peres square strategy*
Multiple challenges:
- Noncomputable because of complex numbers.
- Working with matrices
- Proving commutation.
- Gave up for now.


5. *Proved some measurement Lemmas to get to Alice observable commutes.*
- Proved that Alice measurement commute for the same question but different answer.
- Starting to define the 4.7.1 & 4.7.2

6. *Noticed Typo in the Original Paper*


== Week 3 :
1. *Defined a strategy for a LCS game in Lean*.

2. *Getting familiar with the notation of the paper and the construction of the observable*.

== *Week 1 & 2*

1. *Clarify Project Goal and Scope*

Clarify that the goal is to formalize a proof that is general to LCS game and not just the Mermin-Peres square.
The proof gives a condition on the existence of a perfect strategy for an LCS game.

2. *Learn about the Context of the Mermin-Peres square and LCS games*


#pagebreak()
#bibliography("references.bib", style: "apa")
