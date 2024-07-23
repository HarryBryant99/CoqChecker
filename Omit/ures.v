Require Import String.
Require Import Ascii.
Open Scope string_scope.

Inductive unitres :=
| subsumption : list string -> unitres
| resolution : unitres -> unitres -> unitres.

(*
Inductive unitres :=
| subsumption : formula -> unitres
| resolution : unitres -> unitres -> unitres.
*)

Check unitres.
Check unitres_rect.
Check unitres_ind.
Check unitres_rec.
Check unitres_sind.

Check subsumption.
Check resolution.

(*
Old

Inductive unitres :=
clause : list string -> unitres
| subsumption : unitres -> unitres -> unitres.

Check unitres_ind.

Check clause listA.
(*
Check subsumption listA listB.
*)

Definition clause1 : unitres := clause listA.
Definition clause2 : unitres := clause listB.

Check clause1.
Check clause2.

Definition subsumption1 : unitres := subsumption clause1 clause2.

Print subsumption1.




Inductive unitres2 (V : list string) : Type :=
E
| C (E : unitres2 V) (v : list string) (C : unitres2 V)
| S (l : unitres2 V) (v : list string) (r : unitres2 V).

Check C.
Check S.

Definition empty_tree {V : list string} : unitres2 V :=
  E.

Definition clause3 : unitres2 := C (listA).
Definition clause4 : unitres2 := clause listB.

Check clause1.
Check clause2.

Definition subsumption1 : unitres := subsumption clause1 clause2.

*)