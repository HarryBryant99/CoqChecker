
type bool =
| True
| False

type nat =
| O
| S of nat

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val lef : nat -> nat -> bool **)

let rec lef n m =
  match n with
  | O -> True
  | S n0 -> (match m with
             | O -> False
             | S m0 -> lef n0 m0)

(** val div : nat -> ((nat -> nat -> bool) -> nat -> nat) -> nat **)

let rec div x y =
  match x with
  | O -> O
  | S x' ->
    let z = div x' y in (match mul (S z) (y lef x) with
                         | O -> S z
                         | S _ -> z)
