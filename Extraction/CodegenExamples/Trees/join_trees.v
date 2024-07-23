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

Definition nat_tree : tree nat :=
  (T (T E 2 E) 4 (T E 5 E)).

Print nat_tree.

Fixpoint insert {V : Type} (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E v E
  | T l v' r => T (insert v l) v' (insert v r)
  end.

Definition inserted : tree string := insert "node" empty_tree.
Compute inserted.

Definition inserted2 : tree string := insert "left" inserted.
Compute inserted2.

Definition tree2 : tree string :=
  (T (T E ex_tree E) "four" (T E "five" E))%string.

Print ex_tree.