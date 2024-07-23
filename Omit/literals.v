Require Import String.
Require Import Ascii.
Open Scope string_scope.

(*
Inductive literal : Type := 
empty
| l: string -> literal.
*)

Inductive literal : Type :=
| lit: literal
| notlit : literal -> literal.

(*
Definition neg_lit (L : literal) : literal :=
  match L with
    | lit => notlit
    | notlit => lit
  end.
*)

Definition eq : forall (x y : literal), { x = y } + { x <> y }.
Proof.
intros.
decide equality.
Qed.








Inductive unitres :=
| subsumption : list string -> unitres
| resolution : unitres -> unitres -> unitres.

Definition eq : forall (x y : unitres), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.
