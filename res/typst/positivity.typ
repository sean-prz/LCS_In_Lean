#import "@preview/physica:0.9.8" : *

$ (T_1^2 + T_2^2 + T_3^2) ket(v) = 0 $

Assume that each $T_i$ is self-adjoint, i.e.
$ T_i^dagger = T_i wide text("for ") i = 1,2,3. $

Taking the inner product with $bra(v)$, we get
$ bra(v) (T_1^2 + T_2^2 + T_3^2) ket(v) = 0. $

By linearity,
$ bra(v) T_1^2 ket(v) + bra(v) T_2^2 ket(v) + bra(v) T_3^2 ket(v) = 0. $

Since $T_i^dagger = T_i$, we have
$ bra(v) T_i^2 ket(v) = bra(v) T_i^dagger T_i ket(v) = braket(T_i v, T_i v) = norm(T_i ket(v))^2. $

Therefore,
$ norm(T_1 ket(v))^2 + norm(T_2 ket(v))^2 + norm(T_3 ket(v))^2 = 0. $

Each term is nonnegative, so each term must be zero:
$ norm(T_1 ket(v))^2 = 0, wide norm(T_2 ket(v))^2 = 0, wide norm(T_3 ket(v))^2 = 0. $

Hence,
$ T_1 ket(v) = 0, wide T_2 ket(v) = 0, wide T_3 ket(v) = 0. $

Thus,
$ (T_1^2 + T_2^2 + T_3^2) ket(v) = 0 arrow.double.long T_1 ket(v) = T_2 ket(v) = T_3 ket(v) = 0, $
provided $T_1, T_2, T_3$ are self-adjoint.
