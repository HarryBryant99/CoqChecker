Require Import codegen.codegen.

Open Scope list_scope.

CodeGen InductiveType nat => "nat".
CodeGen InductiveMatch nat => ""
| O => "case 0"
| S => "default" "predn".
CodeGen Constant O => "0".
CodeGen Primitive S => "succn".
Print CodeGen Inductive nat.

Fixpoint my_add n m :=
  match n with
  | 0 => m
  | S p => my_add p (S m)
  end.

Compute my_add 1 2.

Require Import String.
Open Scope string_scope.

Inductive nn :=
| O : nn
| S : nn -> nn.

Check nn.

Check nn_ind.

Check S (S O).

Inductive le (n : nn) : nn -> Prop :=
| le_n : le n n
| le_S : forall m : nn, le n m -> le n (S m).

Check le.

Inductive even : nn -> Prop :=
| even_0 : even O
| even_S : forall n : nn, even n -> even (S(S n)).

Check even.

Check even_ind.

Fixpoint add (n m: nn) : nn :=
  match n with 
  | O => m
  | S n' => S (add n' m)
end.

(*
Compute add 1 2.
*)

Fixpoint add2 (n m: nn) : nn := 
  match n with
  | O => m
  | S n' => S(S(add2 n' m))
  end.

Check add2.

(*
Compute add2 1 2.
*)




Fixpoint add_even (n m: even) : nn := 
  match n with
  | O => m
  | S n' => S(S(add_even n' m))
  end.




Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Definition a: nat_list := (1::nil).