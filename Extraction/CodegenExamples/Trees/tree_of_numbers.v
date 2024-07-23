Require Import String.
Open Scope string_scope.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}.

Definition empty_tree {V : Type} : tree V :=
  E.

Definition new {V : Type} (l : V) (c : V) (r : V) : tree V := (T (T E l E) c (T E r E)).

Fixpoint lookup {V : Type} (d : V) (t : tree V) : V :=
  match t with
  | E => d
  | T l v r => v
  end.

Fixpoint add n m :=
  match n with
  | 0 => m
  | S p => add p (S m)
  end.

Definition one : tree nat :=
  (T E 1 E).

Definition two : tree nat :=
  (T E 2 E).

Definition three : tree nat :=
  (T E (add (lookup 0 one) (lookup 0 two)) E).

Compute three.

Compute lookup 0 three.

Compute add one two.