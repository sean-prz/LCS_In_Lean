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
  - TBD
]
#let week3_2 = [
   #set text(8pt)
   #set align(left + top)
  - TDB
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
  // [], [ *|* ], [ *|* ], 
  table.cell(colspan: 3)[#line(length: 100%, stroke: (1pt +  gray.transparentize(80%)))],
  [*Week 3*], [Advanced Proof in Lean], [Focus on the CHSH game],
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

== *Week 1 & 2*
_Debrief Week 1&2  and plan Week 3_

- [ ] Voir le Recap ci-dessus pour les details de ce qui a été fait.
- [ ] Discuter de la différence entre CHSH SOS et Mermin-Peres SOS, et de ce que nous voulons prouver exactement.
- [ ] Clarifier l'objectif de la formalisation.
- [ ] Adapter le Milestone 1 
- [ ] Clarifier si des notions de "solution group" ou de "robust self-testing" sont nécessaires pour la formalisation.
- [ ] Clarifier si des notions *d'algèbre d'opérateurs* sont nécessaires pour la formalisation.
- [ ] *Agender la réunion de la semaine prochaine*

== Week 3 : 
- Continuer de lire la thèse de Meta.
- (EPR papers / Bell / CHSH papers)
- Quelque preuves simple en Lean en rapport avec la \*-algèbre, ou les opérateurs de projection (theory des opérateurs)


#pagebreak()
= To Do
#line()

== Week 1 & 2.
-[] aha

== Week 3 




#pagebreak()
= Notes
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
