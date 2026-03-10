#import "@preview/cheq:0.3.0": checklist
#set page("a4", margin: 1.75cm, numbering: "1.")
#show: checklist

= Formalization of the Mermin-Peres game in Lean
#v(2em)



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







#table(
  columns : (0.5fr, 1fr, 1fr), 
  stroke: none, 
  gutter: 0em,
  align: (left + horizon, center + horizon, center + horizon),
  inset: 2.5pt,

  [Week number], [*Formalization in Lean*], [*Quantum Information Theory*],
  [#v(1em)], [  ], [  ], 
  [*Week 1 & 2 *], [Introduction to Lean], [LCS & The Mermin-Peres game],
  [ ], [#week1_1], [#week1_2],
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt +  gray.transparentize(80%)))],
  [*Week 3*], [Formalising a LCS Strategy], [4.7 SOS approach to solution group], // WEEK 03
  [ ], [#week3_1], [#week3_2],
  // [], [ *|* ], [ *|* ], 
  [], [], [],
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt +  gray.transparentize(80%)))],
  // [], [ *|* ], [ *|* ], 
  [*W.?*  _(Milestone 1)_], table.cell(colspan: 2)[--- *CHSH SOS Decomposition in Lean*---],
  // [], [ *|* ], [ *|* ], 
  [], [], [],
  // [], [ *|* ], [ *|* ], 
  [*W.?*  _(Milestone 2)_ ], table.cell(colspan: 2)[--- *MerPer SOS Decomposition in Lean*---],
)

//   [W. ?], [#align(right)[-----------------------------------]], [#align(left)[-----------------------------------]],






#pagebreak()
= Meetings 
#line()
 *Monday 11.15am in BC110* to debrief previous week and plan the next one. 

== Week 4 : 
- Prouver 4.71 & 4.72 du papier.
- Commencer la SOS decomposition d'un LCS game.

== Week 3 : 
- Formaliser la construction d'une stratégie pour un LCS game. 
- Assimiler la construction de l'observable pour une stratégie LCS.
== *Week 1 & 2*
_Debrief Week 1&2  and plan Week 3_

- [ ] Voir le Recap ci-dessus pour les details de ce qui a été fait.
- [ ] Discuter de la différence entre CHSH SOS et Mermin-Peres SOS, et de ce que nous voulons prouver exactement.
- [ ] Clarifier l'objectif de la formalisation.
- [ ] Adapter le Milestone 1 
- [ ] Clarifier si des notions de "solution group" ou de "robust self-testing" sont nécessaires pour la formalisation.
- [ ] Clarifier si des notions *d'algèbre d'opérateurs* sont nécessaires pour la formalisation.
- [ ] *Agender la réunion de la semaine prochaine*

//
// #pagebreak()
// = To Do
// #line()
//
// == Week 1 & 2.
// -[] aha
//
// == Week 3 
//



#pagebreak()
= Notes



== Week 3
We assume the minimum framework to make the proof work. 

The CHSH proof defines a valid tuple, so that we can do proof on it: assume you have a valid tuple then ect...

For us we need to define a valid strategy, so that we can do: assume you have a valid strategy for a LCS game, then ....

To do that we're not working in hilbert space , but in an higher abstraction, 
we need to assume the minium to make the proof as elegant and general, so we work with ring\*-ring.

Furthermore, for the CHSH we only need to look at observable while for the proof we'll do later, we need to look at the projector that defines the observable.
This requires to define the structure of these projectors family.

We're trying to build a more general proof so we're defining sets, 
as function from index to element (projector)

The challenge here wasn't Bob but Alice wo needs one projector per assignement, to the equation
while bob only has one projector for 0, and for 1 (since 1 variable)

Also adjusting the milestone, are we staying general.
Will see if needs adapting




== Week 1 & 2
Is the goal acheivable without understanding 
group solution / group theory ?

Is the notion of robust self-testing relevant for now ?

Probably Will I need more operator theory algebra ? 


What are we trying to prove ?
1. that there is a solution ?
2. Do we want to plug in the Game operator for the mermin peres square and then what ? 

In class we saw that CHSH uses a decomposition to show a bound on the winning probability.
We started up by setting lambda I - G, and tried to
prove that this quantity is posisitive semidefinite, meaning that the winning probability is upper bounded by lambda.

In mermin peres sqaure, 

#pagebreak()
#bibliography("references.bib", style:"apa")
