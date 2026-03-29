---
trigger: always_on
---

# LCS Project Summary: Architecture & Status

A formalization of **Linear Constraint System Games (LCS)** in Lean 4.

The goal of this project is 
1. To prove that the Mermin-Peres well known strategy given in terms of 9 observables is equivalent to a valid strategy given in terms of projector for each pair of question, answer for each player. 
2. By a sum of square decomposition of a local loss operator prove a condition on the existence of a perfect strategy for a given LCS.

## Module Structure

1.  **Core Geometry & Game Definition**
    *   [`Basic.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Basic.lean): Includes `LCSLayout`, `Assignment`, and `LCSGame`.
2.  **Algebraic Foundations**
    *   [`Measurement.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Measurement.lean): Theory of **Projector Measurement Systems** (`IsMeasurementSystem`).
    *   [`Observable.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Observable.lean): Definitions of **Observables** (`IsObservable`).
    *   [`Common.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Common.lean): Utilities for signs (`observableSign`) and arithmetic lemmas.
3.  **Strategy Implementations**
    *   [`Strategy/ProjectorStrategy.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Strategy/ProjectorStrategy.lean): The **Projector-based Strategy** (`LCSStrategy`). Defines derived observables **`Alice_A`** and **`Bob_B`**.
    *   [`Strategy/ObservableStrategy.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Strategy/ObservableStrategy.lean): The **Observable-based Strategy** (`ObservableStrategyData`).
    *   [`Strategy/Equivalence.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/Strategy/Equivalence.lean): Bridge construction `ObservableStrategy_To_ProjectorStrategy`.
4.  **Results**
    *   [`WinningCondition.lean`](file:///Users/sean/Documents/MA2/lean/projects/LCS/LCS/WinningCondition.lean): Formal verification of Theorem 4.7, defining the **Winning Operator** and proving relevant algebraic identities.
