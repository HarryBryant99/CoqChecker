Inductive number (V : Type) : Type :=
| v
| add (l : number V) (r : number V).

Definition one : number nat := 1.

Fixpoint add n m :=
  match n with
  | 0 => m
  | S p => add p (S m)
  end.