#import "./charged-ieee.typ": ieee
#import "@preview/codelst:2.0.2": sourcecode
#import "@preview/wordometer:0.1.5": word-count, total-words
#set page(numbering:"1")

#show link: it => text(
  fill: blue,// Light sky blue
  style: "italic",
  underline(it)
)
#show raw: set text(size: 7pt)

// Do not modify, this starts the word-counter here  
// Exclude all raw block from the count.
#show: word-count.with(exclude: (raw,))

#show:ieee.with(
  title: [Formalising Binary Linear Constraint System Games in Lean 4],
  abstract: [
  This project presents a Lean 4 formalization of binary Linear Constraint System (LCS) games and their quantum strategies. 
  It provides the core definitions for LCS games over $F_2$, together with two complementary quantum strategy formalisms: a projector-based formalism, where strategies are described by projective measurement systems for the players, and an observable-based formalism, where strategies are described by self-adjoint involutive operators satisfying the relevant commutation relations. 
  The development also includes a bridge between these two formalisms, allowing strategies to be translated from one description to the other.

  On the analytic side, the formalization develops local winning and local loss operators for binary LCS games and proves a sum-of-squares decomposition of the local loss operator. This is then combined with an EPR-state argument to extract row identities for observables arising from bipartite strategies.
  On the algebraic side, the project defines the solution group of a binary linear system and shows how these row identities induce a matrix representation of the corresponding solution group. 

  The Mermin-Peres Magic Square game serves as the main case study, illustrating how the abstract framework can be instantiated by an explicit quantum strategy.

  Overall, the project provides a machine-checked Lean 4 development
  connecting binary LCS games, quantum strategies, and solution group representations. 
  ],
  authors: (
    (
      name: "Perazzolo Sean",
      organization: [EPFL],
      email: "sean.perazzolo@epfl.ch"
    ),
  ),
  index-terms: ("Lean 4", "Formal verification", "Linear Constraint System Games", "Quantum strategies", "Solution groups", "Mermin-Peres magic square game") ,
  figure-supplement: [Fig.],
)



= Introduction

== Quantum Nonlocal games
In the world of quantum information theory, non-local games serve as a powerfl framework for understanding the profound phenomenon of quantum entanglement and non-locality. 
Non-locality refers to the ability of quantum systems to exhibit correclations that defy classical phyiscal laws, specifically the principle of local realism, which dictactes that distant objects cannot influence one another instantaneously.
In a standard non-local game, two or more cooperatings players, are phyisically seperated and forbidden from communicating. 
They receive inputs from a referee and must produce outputs that satisfy certain conditions to win the game.
While Classical strategies for non-local games are limited by local realism, quantum strategies can leverage entanglement to achieve higher winning probabilities, often surpassing classical limits. This setting makes it possible to compare the correlations achievable by classical and quantum resources, providing insights into the fundamental differences between classical and quantum physics.

== Historical Context and Significance
The study of such games is rooted in the foundations of quantum mechanics. The Einstein-Podolsky-Rosen (EPR) paradox, proposed in 1935, challenged the completeness of quantum theory by arguing that its predictions suggested an unacceptable form of long-range influence, "spooky action at a distance." 
In 1964, Bell's theorem later showed that no local hidden variable theory could reproduce all the predictions of quantum, establishing non-locality as a central featrure of quantum theory rather than a philophical curiosity.
Since then, non-local games have become a standard for expressing and analyzing this phenomenon:
They form the theoritical backbone for device-independent quantum cryptography, where security guarantees are derived directly from
the violation of classical bounds in non-local games, without relying on assumptions about the internal workings of the devices used.

== Linear Constraint System Games
Within this borad class, Linear Constraint Systems games form a particulary simple and structured family. 
Instead of arbitrary input-output rules, the winning conditions in an LCS game are determined by a system of linear equations over a finite field (typically modulo 2), where the players' objective is to convince a referee that they possess a valid assignment of variables satisfying these constraints. 
Typically the first player, conventionally called Alice, is responsible for providing an assignement to the variables of a given equation, while the second player, Bob, is responsible for providing an assignement to a single variable of the same equation.
Because their underlying structure is firmly rooted in group theory and linear algebra, LCS games offer a highly systematic and mathematically elegant way to map out the exact boundaries of quantum advantage

=== Mermin-Peres Magic Square Game

Canonical examples, such as the Mermin-Peres magic square game, perfectly illustrate the strenth of this framework; they exhibit quantum pseudotelepathy, a scenario where players sharing entanglement can satisfy the constraints to win with 100% certainty, even tough no classical strategy can win perfectly. 

/*
== Linear Constraint System Games

=== What is a Linear Constraint System Game?

=== Why are Linear Constraint System Games interesting?


== Quantum Strategies for Linear Constraint System Games

== Mermin Peres Magic Square Game
*/

== Contributions and Scope
This project makes the following contributions to the formalization of binary Linear Constraint System games in Lean 4:

- It formalises the core definitions of binary Linear Constraint System games, including layouts, assignments, games, and explicit binary linear systems over $F_2$.
- It develops two quantum strategy formalisms:
  a projector-based formalism using projective measurement systems, and an observable-based formalism using self-adjoint involutive operators.
- It implements a bridge between these two formalisms, allowing observable strategies to be translated into projector strategies.
- It defines local and global winning/loss operators for binary LCS games and proves a sum-of-squares decomposition of the local loss operator, which is then used in the EPR-state argument.
- It formalises an EPR-state argument that extracts row identities from local-loss annihilation in the bipartite setting.
- It defines the solution group of a binary linear system and constructs matrix representations of this group from the previously derived row identities.
- It instantiates the general framework on the Mermin-Peres Magic Square game as the main case study.
The scope of the project is intentionally limited to the binary setting. In particular:
- the formalisation is restricted to LCS games over $F_2$,
- the solution-group construction is the binary one associated with this setting,
- and the final representation theorem is proved in the bipartite EPR framework.

= Approach

== Structure of the Lean Development

The formalization is organized into a small collection of modules following the main stages of the development. 

The foundational definitions are introduced in `LCS/Basic.lean`, which defines layouts, games, and explicit binary linear systems. 

The strategy layer is developed in `LCS/Strategy`, with separate modules for projector-based strategies, observable-based strategies, and the bridge between them. 

The main proof-oriented part of the project is then divided between `LCS/WinningCondition.lean`, which defines the winning and loss operators and proves the sum-of-squares decomposition of the local loss operator, `LCS/EPR.lean`, which extracts matrix identities from local-loss annihilation on the EPR state, and `LCS/SolutionGroup.lean` together with `LCS/SolutionGroup/Representation.lean`, which define the binary solution group and construct its matrix representations.

Finally, the abstract framework is instantiated in `LCS/Games/MagicSquare`, which develops the Mermin-Peres Magic Square game as the main case study.

== Linear Constraint System Games Formalization 

We begin by formalising Linear Constraint System games. 

=== The Mathematical Object
More generally, a linear constraint system over a field $K$ consists of a finite family of variables $x_1, dots, x_s$ together with a finite family of $r$ equations
$ sum_(j=1)^s A_(i j) x_j = b_i $,
where $A_(i j), b_i in K$.

In this project, we restrict to the binary setting over $F_2$.
In this case, variables take values in $\{0,1\}$ and the equations are evaluated modulo $2$.
The support-based presentation used throughout the development records, for each equation, the set of variables that occur in it; equivalently, this is the binary case where the coefficients are implicitly equal to $1$ on the support of the equation.

=== The Game
In the associated game, the referee selects an equation $i$ and sends it to Alice, while Bob receives a variable $j$ that appears in that equation.

Alice responds with an assignment of values to the variables appearing in the chosen equation, while Bob responds with a value for the queried variable.

The players win if Alice's assignment satisfies the chosen equation and if Bob's answer agrees with Alice's value on the queried variable.

=== Representation in Lean
_Code snippets of this section are taken from `LCS/Basic.lean`._

\

We define an `LCSLayout` structure to represent the following data:
- the number of variables `s`,
- the number of equations `r`,
- the support of each equation, as a family of finite sets `V : Fin r -> Finset (Fin s)`.


This structure does not capture the constants $b_i$ on the right-hand side of the equations, since many constructions depend only on the incidence pattern of the variables in each equation.

\

#sourcecode[```lean

structure LCSLayout where
  r : ℕ
  s : ℕ
  V : Fin r → Finset (Fin s)

```]

\

Next, we define an `LCSGame` structure that extends `LCSLayout` by including the constants `b : Fin G.r -> Fin 2`, which represent the right-hand side of the equations in the binary setting.

#sourcecode[```lean
structure LCSGame (G : LCSLayout) where
  b : Fin G.r → Fin 2
```]
\

Finally, for the group-theoretic constructions, we also define a `LinearSystem` structure as an alternative description of a binary LCS game.
This structure consists of a coefficient matrix $A$ and a right-hand side vector $b$.

#sourcecode[```lean
structure LinearSystem where
  layout : LCSLayout
  A : Fin layout.r → Fin layout.s → Fin 2
  b : Fin layout.r → Fin 2
```]

Any support-based game can be converted into such a system by taking $A_(i j) = 1$ when variable $j$ appears in equation $i$, and $A_(i j) = 0$ otherwise.

\

The project therefore uses both a support-based description, via `LCSLayout` and `LCSGame`, and a matrix-based description, via `LinearSystem`, depending on which is more convenient for the construction at hand.

For a concrete example of these definitions, see the case study of the Mermin-Peres Magic Square game in @magic-square.


== Quantum Strategy Formalisms

=== Projector-Based Strategies

=== Observable-Based Strategies

=== Bridge Between Projector and Observable-Based Strategies

=== Bipartite Observable Strategies


== Winning Conditions and Local Loss 

=== Local Winning and Loss Operators

=== Sum-of-Squares Decomposition

== EPR-State Argument and Row Identity Extraction

=== Bipartite Setting

=== Extraction of Row Identities

== Solution Groups and Matrix Representations

=== Defining the Solution Group of a Binary Linear System

=== From Row Identities to Matrix Representations


= Results

== Main Verified Theorems

== Magic Square Game Case Study <magic-square>

= Limitations and Future Work


= Conclusion
