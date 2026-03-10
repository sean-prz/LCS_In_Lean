import VersoBlog

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "../TestLCS"
set_option verso.exampleModule "TestLCS.LCS"
#doc (Page) "Archive" => 


Posts about learning Lean 4, formal verification, and writing proofs alongside code. I'm documenting what I figure out as I go, mostly focusing on how to apply these ideas to practical programming problems.


# But does markdown work full y? 
that is weird it was supposed to work
$$`x= x+1`

Why nothing works

```leanInit welcome
```

```lean welcome
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```



```anchor IsMeasurementSystem

```



