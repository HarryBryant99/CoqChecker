Require Import String.
Open Scope string_scope.

Definition key := nat.

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}.

Definition empty_tree {V : Type} : tree V :=
  E.

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

Print ex_tree.

Definition nat_tree : tree nat :=
  (T (T E 2 2 E) 4 4 (T E 5 5 E)).

Print nat_tree.

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | 0  , _   => true
  | _  , 0   => false
  | S n, S m => leb n m
  end.

Fixpoint lt (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => false
         | S m => true
         end
  | S n' => match m with
            | O => false
            | S m' => lt n' m'
            end
  end.

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if lt x y then bound x l
                else if negb'(leb x y) then bound x r
                     else true
  end.

Compute bound 5 ex_tree = false.

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if lt x y then lookup d x l
                else if negb'(leb x y) then lookup d x r
                     else v
  end.

Compute lookup "" 5 ex_tree = "five".

Compute lookup "" 5 ex_tree.

Fixpoint insert {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if lt x y then T (insert x v l) y v' r
                 else if negb'(leb x y) then T l y v' (insert x v r)
                      else T l x v r
  end.

Definition inserted : tree string := insert 3 "three" empty_tree.
Compute inserted.

Definition inserted2 : tree string := insert 7 "7" inserted.
Compute inserted2.

Definition inserted3 : tree string := insert 1 "1" inserted2.
Compute inserted3.

Definition inserted4 : tree string := insert 6 "6" inserted3.
Compute inserted4.