
type bool =
| True
| False

type nat =
| O
| S of nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val lef : nat -> nat -> bool

val div : nat -> ((nat -> nat -> bool) -> nat -> nat) -> nat
