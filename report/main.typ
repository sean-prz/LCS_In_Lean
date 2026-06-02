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

#show: ieee.with(
  title: [Formalising Binary Linear Constraint System Games in Lean 4],
  abstract: [
  This project presents a Lean 4 formalization of binary Linear Constraint System (LCS) games and their quantum strategies. 
  It provides the core definitions for LCS games over $F_2$, together with two complementary quantum strategy formalisms: a project based formalism, where strategies are described by projector measurement systems for the players, and an observable based formalism, where strategies are described by self-adjoing involutive operators satisfying the relevant commutation relations. 
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

== Linear Constraint System Games

=== What is a Linear Constraint System Game?

=== Why are Linear Constraint System Games interesting?


== Quantum Strategies for Linear Constraint System Games

== Mermin Peres Magic Square Game

== Contributions and Scope


= Approach

== Linear Constraint System Games Formalization 

== Quantum Strategy Formalisms

=== Projector Based Strategies

=== Observable-Based Strategies

=== Bridge Between Projector and Observable-Based Strategies

=== Bipartite Strategies (maybe later)


== Winning Conditions and Local Loss 

=== Local Winning and Loss Operators

=== Sum-of-Squares Decomposition

== EPR-State Argument and Row Identities Extraction

=== Bipartite Setting

=== Extraction of Row Identities

== Solution Groups and Matrix Representations

=== Defining the Solution Group of a Binary Linear System

=== From Row Identities to Matrix Representations


= Results

== Main Verified Theorems

== Magic Square Game Case Study

= Limitations and Future Work


= Conclusion


