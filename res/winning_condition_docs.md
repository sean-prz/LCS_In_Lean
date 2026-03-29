# Documentation: WinningCondition.lean

This file defines the mathematical operators representing the winning conditions of a Linear Constraint System (LCS) game and provides the technical lemmas needed to calculate win probabilities.

## Core Definitions

### `winning_assignments`
- **Purpose**: Defines the set of local assignments $x: V_i \to \{0, 1\}$ that satisfy the $i$-th equation of the LCS ($ \sum_{j \in V_i} x_j = b_i \pmod 2 $).
- **Role**: This is the "classical" definition of a valid local solution for a specific player's constraint.

### `winning_operator`
- **Purpose**: A quantum operator whose expectation value in a given state represents the probability of winning the LCS game.
- **Formula**: $ \frac{1}{R|V_i|} \sum_{i, j} \ldots $ (summing over winning projectors).

## Technical Helper Lemmas

### `measurement_sum_mul_projector`
- **What it proves**: $(\sum_{y \in S} E_y) \cdot E_x = E_x$ if $x \in S$, and $0$ otherwise.
- **Why we need it**: Measurement systems consist of orthogonal projectors ($E_x E_y = \delta_{xy} E_x$). This lemma allows us to "filter" sums of projectors when they interact with a specific measurement outcome $E_x$.

### `alice_A_mul_projector`
- **What it proves**: $A_j \cdot E_x = (-1)^{x_j} \cdot E_x$.
- **Why we need it**: It establishes that the projectors $E_x$ are eigenvectors of the observables $A_j$. The bit $x_j$ in the assignment determines the eigenvalue (either $+1$ or $-1$).

### `alice_partial_prod_mul_projector`
- **What it proves**: $(\prod_{j \in s} A_j) \cdot E_x = (-1)^{\sum_{j \in s} x_j} \cdot E_x$.
- **Why we need it**: Generalizes the single-variable case to products. Since Alice's measurements for a single equation commute, they can be diagonalized simultaneously.

### `prod_sign_eq_sum_sign`
- **What it proves**: $\prod_j (-1)^{x_j} = (-1)^{\sum_j x_j}$.
- **Why we need it**: Converts a product of signs into a sign of a sum, allowing us to relate operator products to the parity condition of the LCS equations.

### `sign_indicator`
- **What it proves**: $\frac{1}{2}(1 + (-1)^b \cdot (-1)^s) = \mathbb{1}_{s=b}$.
- **Why we need it**: This is the "algebraic trick" that connects the parity of an assignment ($s$) and the equation target bit ($b$) to a binary $0/1$ value. It is used to "select" winning assignments.

## Principal Lemmas (The "Bridge" Lemmas)

### `lemma_4_7_1`
- **What it proves**: Relates the sum of winning projectors $\sum_{x \in \text{win}} E_x$ to the algebraic expression $\frac{1}{2}(1 + (-1)^{b_i} \prod_{j \in V_i} A_j)$.
- **Why we need it**: This is the most critical step in the proof. It translates the "set-based" winning condition into a "product-of-operators" form, which is necessary for calculating expectation values in quantum states.

### `lemma_4_7_2`
- **What it proves**: Relates the sum of projectors where a specific variable $x_j$ takes value $y$ to the observable $A_j$: $\sum_{x: x_j=y} E_x = \frac{1}{2}(1 + (-1)^y A_j)$.
- **Why we need it**: Provides a simplified version of the bridge lemma for single variables, useful for breaking down the full winning operator into individual components.
