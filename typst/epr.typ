#import "@preview/physica:0.9.8" : *
#let Row = math.op("Row")

$ ket(Omega) = sum_k ket(k) times.o ket(k) $

We use the unnormalised EPR vector
$ ket(Omega) $.
In coordinates, for $a,b in n$,
$ ket(Omega)_(a,b) = 1 $ if $a=b$, and $ket(Omega)_(a,b) = 0$ otherwise.

== Kronecker action on the EPR vector

Let $M,N in mat(n times n, CC)$.
Then
$ ((M times.o N) ket(Omega))_(a,b)
    = sum_(k,l) M_(a,k) N_(b,l) ket(Omega)_(k,l). $

Since $ket(Omega)$ is supported only on the diagonal $k=l$,
$ ((M times.o N) ket(Omega))_(a,b)
    = sum_k M_(a,k) N_(b,k). $

This is the lemma `kronecker_mulVec_epr`.

Therefore
$ (M times.o N) ket(Omega) = 0 $
is equivalent to
$ sum_k M_(a,k) N_(b,k) = 0 wide text("for all ") a,b. $

But
$ (M N^T)_(a,b) = sum_k M_(a,k) (N^T)_(k,b)
    = sum_k M_(a,k) N_(b,k). $

Hence
$ (M times.o N) ket(Omega) = 0 arrow.double.long M N^T = 0. $

Conversely, if $M N^T = 0$, then every coordinate above is zero, so
$ (M times.o N) ket(Omega) = 0. $

Thus
$ (M times.o N) ket(Omega) = 0 arrow.double.long M N^T = 0. $

This is the lemma `kronecker_mulVec_epr_eq_zero_iff`.

== Alice-side injectivity

Take $N = I$.
Then
$ (M times.o I) ket(Omega) = 0 arrow.double.long M I^T = 0. $

Since $I^T = I$,
$ (M times.o I) ket(Omega) = 0 arrow.double.long M = 0. $

In the Lean notation $M times.o I$ is `bipartiteAliceLift M`.
Thus
$ ("bipartiteAliceLift"(M)) ket(Omega) = 0
    arrow.double.long M = 0. $

This is the lemma `alice_lift_mulVec_epr_eq_zero_iff`.

== The affine Kronecker relation

Let $M,N in mat(n times n, CC)$.
Assume
$ (I - M times.o N) ket(Omega) = 0. $

Then
$ ket(Omega) = (M times.o N) ket(Omega). $

Taking the $(a,b)$ coordinate gives
$ ket(Omega)_(a,b) = sum_k M_(a,k) N_(b,k). $

The left hand side is $I_(a,b)$, and the right hand side is $(M N^T)_(a,b)$.
Therefore
$ M N^T = I. $

Conversely, if $M N^T = I$, then every coordinate of
$ (I - M times.o N) ket(Omega) $
is zero.
Thus
$ (I - M times.o N) ket(Omega) = 0
    arrow.double.long M N^T = I. $

This is the lemma `one_sub_kronecker_mulVec_epr_eq_zero_iff`.

With a scalar $c in CC$, the same argument gives
$ (I - c (M times.o N)) ket(Omega) = 0
    arrow.double.long c (M N^T) = I. $

This is the lemma `one_sub_smul_kronecker_mulVec_epr_eq_zero_iff`.

On Alice's side only,
$ (I - c (M times.o I)) ket(Omega) = 0
    arrow.double.long I - c M = 0. $

This is the lemma `alice_lift_one_sub_smul_mulVec_epr_eq_zero_iff`.

== Bipartite lift algebra

The bipartite lifts are
$ A_A = A times.o I, wide B_B = I times.o B. $

Their products reduce to ordinary Kronecker products:
$ (I times.o B)(A times.o I) = A times.o B, $
$ (A times.o I)(I times.o B) = A times.o B, $
$ (A times.o I)(C times.o I) = (A C) times.o I. $

Also,
$ (I - c A) times.o I = I - c (A times.o I). $

These are the lift lemmas used before applying the EPR identities in Stage 3.

== Stage 2 transpose and adjoint argument

Stage 2 uses positivity:
$ (T_1^2 + T_2^2 + T_3^2) ket(Omega) = 0 $
and the self-adjointness assumptions
$ T_i^dagger = T_i. $

Taking the inner product with $bra(Omega)$ gives
$ bra(Omega) (T_1^2 + T_2^2 + T_3^2) ket(Omega) = 0. $

By linearity,
$ bra(Omega) T_1^2 ket(Omega)
  + bra(Omega) T_2^2 ket(Omega)
  + bra(Omega) T_3^2 ket(Omega) = 0. $

Since $T_i^dagger = T_i$,
$ bra(Omega) T_i^2 ket(Omega)
    = bra(Omega) T_i^dagger T_i ket(Omega)
    = braket(T_i Omega, T_i Omega)
    = norm(T_i ket(Omega))^2. $

Hence every summand is nonnegative, and all must vanish:
$ T_1 ket(Omega) = 0, wide
  T_2 ket(Omega) = 0, wide
  T_3 ket(Omega) = 0. $

The Lean proof must first show that the three concrete SOS terms are self-adjoint.
The transpose-adjoint facts used are:
$ (X Y)^dagger = Y^dagger X^dagger, $
$ (X - c Y)^dagger = X^dagger - overline(c) Y^dagger, $
$ I^dagger = I. $

For a finite product of commuting self-adjoint matrices,
$ (product_x F_x)^dagger
    = product_x F_x^dagger
    = product_x F_x. $

This is the lemma `noncommProd_conjTranspose_eq_self`.
Applied to Alice's row product,
$ Row_i(A)^dagger = Row_i(A). $

The LCS sign is real:
$ overline((-1)^(b_i)) = (-1)^(b_i). $

Therefore, if $T^dagger = T$ and $c = (-1)^(b_i)$, then
$ (I - c T)^dagger = I - c T. $

This is the helper `one_sub_smul_conjTranspose_eq_self`.

For the consistency term,
$ T_1 = I - B_j A_(i,j). $

Using $A_(i,j)^dagger = A_(i,j)$, $B_j^dagger = B_j$, and
$ A_(i,j) B_j = B_j A_(i,j)$,
$ T_1^dagger
  = I - (B_j A_(i,j))^dagger
  = I - A_(i,j) B_j
  = I - B_j A_(i,j)
  = T_1. $

For the row term,
$ T_2 = I - (-1)^(b_i) Row_i(A). $

Since the sign is real and $Row_i(A)^dagger = Row_i(A)$,
$ T_2^dagger = T_2. $

For the product term,
$ T_3 = I - (-1)^(b_i) Row_i(A) A_(i,j) B_j. $

The core product is self-adjoint because the factors are self-adjoint and the
local commutation rules reorder the reversed adjoint product:
$ (Row_i(A) A_(i,j) B_j)^dagger
  = B_j A_(i,j) Row_i(A)
  = Row_i(A) A_(i,j) B_j. $

Together with the real sign,
$ T_3^dagger = T_3. $

This is the transpose argument needed by Stage 2.

== Stage 3 extraction

Let
$ A_(i,j) = A times.o I, wide B_j = I times.o B, wide Row_i(A) = Row times.o I. $

The three SOS terms are
$ T_1 = I - B_j A_(i,j), $
$ T_2 = I - (-1)^(b_i) Row_i(A), $
$ T_3 = I - (-1)^(b_i) Row_i(A) A_(i,j) B_j. $

Assume Stage 2 has proved
$ T_1 ket(Omega) = 0, wide
  T_2 ket(Omega) = 0, wide
  T_3 ket(Omega) = 0. $

For consistency,
$ B_j A_(i,j) = (I times.o B)(A times.o I) = A times.o B. $

Thus
$ (I - A times.o B) ket(Omega) = 0. $

By the affine Kronecker relation,
$ A B^T = I. $

If $B$ is an observable, then $B^2 = I$.
Transposing gives
$ (B^T)^2 = I. $

Therefore
$ A
  = A I
  = A (B^T B^T)
  = (A B^T) B^T
  = B^T. $

This is the lemma `consistency_of_epr_annihilates`.

For the row relation, set $c = (-1)^(b_i)$.
Since
$ T_2 = I - c (Row times.o I), $
Alice-side injectivity gives
$ I - c Row = 0. $

So
$ c Row = I. $

Since $c^2 = 1$,
$ Row = c I = (-1)^(b_i) I. $

This is the lemma `row_relation_of_epr_annihilates`.

For the product relation,
$ Row_i(A) A_(i,j) B_j
  = ((Row A) times.o I)(I times.o B)
  = (Row A) times.o B. $

Thus
$ (I - c ((Row A) times.o B)) ket(Omega) = 0. $

By the scalar affine Kronecker relation,
$ c ((Row A) B^T) = I. $

Equivalently,
$ (-1)^(b_i) (Row A B^T) = I. $

This is the lemma `product_relation_of_epr_annihilates`.

Bundling the three extracted identities gives
$ A = B^T, wide
  Row = (-1)^(b_i) I, wide
  (-1)^(b_i) Row A B^T = I. $

This is `local_matrix_identities_of_sos_terms_annihilate_epr`.
