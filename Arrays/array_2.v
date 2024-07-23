Require Import codegen.codegen.

Require Import List.

Primitive int := #int63_type.

Primitive array := #array_type.

Primitive get := #array_get.
Primitive set := #array_set.

Require Import ZArith.
Open Scope Z_scope.

(*
Notation "t .[ i ]" := (get t i).
Notation "t .[ i <- a ]" := (set t i a).
*)

Inductive array2 (n : nat) : Type :=
ca : forall l : list Z, length l = n -> array2 n.

Check array2.

Definition test (a : array2) : array2 := a.