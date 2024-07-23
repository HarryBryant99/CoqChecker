Require Import String.
Require Import Ascii.
Open Scope string_scope.

Inductive literal : Type := 
empty
| l: string -> literal.


Definition a : literal := l "a".

Check l "a".
Check empty.

(*---------------------------------------------------------*)

Inductive ty: Set :=
| I
| O.

Check I.

(*Won't work because I is not built upon strings
Definition a : ty := I 2.
*)

Definition ty_eq_dec : forall (x y : ty), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.

Definition f (x: ty) (y: ty): nat :=
  if ty_eq_dec x y then 0 else 1.



Definition f2 x y := 
match x,y with 
I, I 
| O, O => 0 
| _,_ => 1 end.

(*---------------------------------------------------------*)

Definition equals (a b : ty) : nat :=
if ty_eq_dec a b then 1 else 0.

Compute equals I O.
Compute equals I I.