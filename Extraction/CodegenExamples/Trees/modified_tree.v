Require Import String.
Open Scope string_scope.

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}.

Definition empty_tree {V : Type} : tree V :=
  E.

Definition ex_tree : tree string :=
  (T (T E "two" E) "four" (T E "five" E))%string.

Print ex_tree.

Definition new {V : Type} (l : V) (c : V) (r : V) : tree V := (T (T E l E) c (T E r E)).

Compute new "l" "c" "r".

Definition t1 := new "l" "c" "r".
Print t1.

Definition t2 := new t1 t1 t1.
Print t2.