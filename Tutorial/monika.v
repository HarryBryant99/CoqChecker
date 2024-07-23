Definition x := 10.

Definition inc_nat (x : nat) : nat := x + 1.

Compute (1 + 1).

Check tt.

About plus.

Print true.

Search nat.

Search "_ + _".

Search (?a -> ?a -> bool).

Search (?a * ?a).

Locate "+".

Definition make_inc x y := x + y.

Definition inc_2 := make_inc 2.

Compute inc_2 3.

Definition add_xy : nat := let x := 10 in
                           let y := 20 in
                           x + y.

Compute add_xy.

Definition is_zero (x : nat) :=
    match x with
    | 0 => true
    | _ => false  (* The "_" pattern means "anything else". *)
    end.

Fixpoint factorial n := match n with
                        | 0 => 1
                        | (S n') => n * factorial n'
                        end.

Compute factorial 5.

Compute factorial (5-1).

Fixpoint is_even (n : nat) : bool := match n with
  | 0 => true
  | (S n) => is_odd n
end with
  is_odd n := match n with
  | 0 => false
  | (S n) => is_even n
              end.

Definition my_square : nat -> nat := fun x => x * x.

Definition my_id (A : Type) (x : A) : A := x.
Definition my_id2 : forall A : Type, A -> A := fun A x => x.
Compute my_id nat 3. (* 3 : nat *)

Compute my_id _ 3.

Definition my_id3 {A : Type} (x : A) : A := x.
Compute my_id3 3. (* 3 : nat *)

Compute @my_id3 nat 3.

Compute my_id3 (A:=nat) 3.

Require Import ZArith.

Open Scope Z_scope.

Compute 1 + 7.

Compute 1 =? 2.

Locate "_ =? _". (* Z.eqb x y : Z_scope *)
Close Scope Z_scope.

Require Import QArith.

Open Scope Q_scope.

Compute 2. (* 2 : nat *)
Compute (2 # 3). (* The fraction 2/3 *)
Compute (1 # 3) ?= (2 # 6). (* Eq : comparison *)
Close Scope Q_scope.

Check tt.

Compute None.

Check Some 3.

Print sum.
Check inl 3. (* inl 3 : nat + ?B *)
Check inr true. (* inr true : ?A + bool *)
Check sum bool nat. (* (bool + nat)%type : Set *)
Check (bool + nat)%type. (* Notation for sum *)

Check (1, true). (* (1, true) : nat * bool *)
Compute prod nat bool.

Definition my_fst {A B : Type} (x : A * B) : A := match x with
                                                  | (a,b) => a
                                                  end.

Definition my_fst2 {A B : Type} (x : A * B) : A := let (a,b) := x in
                                                   a.

Compute cons 1 (cons 2 (cons 3 nil)).
Compute (1 :: 2 :: 3 :: nil)%list.

Require Import List.
Import ListNotations.
Compute [1 ; 2 ; 3].

Definition my_list : list nat := [47; 18; 34].
Compute List.length my_list.

Compute List.nth 1 my_list 0. (* 18 : nat *)
Compute List.map (fun x => x * 2) my_list. (* [94; 36; 68] : list nat *)
Compute List.filter (fun x => Nat.eqb (Nat.modulo x 2) 0) my_list.
                                               (* [18; 34] : list nat *)
Compute (my_list ++ my_list)%list. (* [47; 18; 34; 47; 18; 34] : list nat *)

Require Import Strings.String.

Open Scope string_scope.

Compute String.append "Hello " "World". (* "Hello World" : string *)
Compute "Hello " ++ "World". (* "Hello World" : string *)

Compute String.eqb "Coq is fun!" "Coq is fun!". (* true : bool *)
Compute "no" =? "way". (* false : bool *)

Close Scope string_scope.

Definition my_three : nat := 3.
Definition my_nat : Type := nat.

Inductive ml := OCaml | StandardML | Coq.
Definition lang := Coq.  (* Has type "ml". *)

Inductive my_number := plus_infinity
                     | nat_value : nat -> my_number.

Compute nat_value 3.

Record Point2d (A : Set) := mkPoint2d { x2 : A ; y2 : A }.

Definition mypoint : Point2d nat :=  {| x2 := 2 ; y2 := 3 |}.
Compute x2 nat mypoint. (* 2 : nat *)
Compute mypoint.(x2 nat). (* 2 : nat *)

Definition list_of_lists a := list (list a).
Definition list_list_nat := list_of_lists nat.

Inductive my_nat_list :=
  EmptyList | NatList : nat -> my_nat_list -> my_nat_list.

Compute NatList 1 EmptyList.

Inductive animal := Dog : string -> animal | Cat : string -> animal.

Definition say x :=
    match x with
    | Dog x => (x ++ " says woof")%string
    | Cat x => (x ++ " says meow")%string
    end.

Compute say (Cat "Fluffy").

Fixpoint sum_list l :=
    match l with
    | [] => 0
    | head :: tail => head + (sum_list tail)
    end.

Compute sum_list [1; 2; 3].

 Definition my_theorem : forall A B, A /\ B -> A :=
  fun A B ab => match ab with
                  | (conj a b) => a
                end.

Theorem my_theorem2 : forall A B, A /\ B -> A.
Proof.
  intros A B ab.  destruct ab as [ a b ]. apply a.
Qed.

Require Import Ring.
Require Import Arith.
Theorem simple_poly : forall (x : nat), (x + 1) * (x + 2) = x * x + 3 * x + 2.
  Proof. intros. ring. Qed.

Fixpoint sumn (n : nat) : nat :=
  match n with
  | 0 => 0
  | (S n') => n + (sumn n')
  end.

Compute sumn 3.

Theorem sum_formula : forall n, 2 * (sumn n) = (n + 1) * n.
Proof. intros n. induction n.
       - reflexivity. (* 0 = 0 base case *)
       - simpl. ring [IHn]. (* induction step *)
Qed.

