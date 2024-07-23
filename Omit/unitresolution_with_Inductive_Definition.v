Open Scope list_scope.

Require Import List.

Require Import String.
Require Import Ascii.
Open Scope string_scope.

(*-----------------------------------------------------------------------------*)
(*Literals*)

Inductive literal : Set :=
  | EmptyLiteral : literal
  | Literal : ascii -> literal -> literal.

Definition literal_dec : forall s1 s2 : literal, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.

Definition compare_literals (a b : literal) : bool :=
  if literal_dec a b then true else false.

Fixpoint append (s1 s2 : literal) : literal :=
  match s1 with
  | EmptyLiteral => s2
  | Literal c s1' => Literal c (s1' ++ s2)
  end
where "s1 ++ s2" := (append s1 s2) : literal_scope.

(*-----------------------------------------------------------------------------*)
(*Define some test literals*)

Definition E : literal := EmptyLiteral.

Definition negation : literal := Literal "!" E. 

Definition A : literal := Literal "A" E.
Definition B : literal := Literal "B" E.
Definition AB : literal := Literal "A" B.
Definition BA : literal := Literal "B" A.

Definition negA : literal := Literal "!" A.

Print AB.
Print BA.

(*-----------------------------------------------------------------------------*)

Fixpoint eq_nat n m {struct n} : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

Compute eq_nat 2 43.

Definition not (a b neg: literal) : bool := 
if (compare_literals a (append neg b)) then true 
else if (compare_literals b (append neg a))  then true
else false.

Compute not A negA negation.

Fixpoint omit (l:list literal) (c:nat) {struct l} : list literal :=
    match l with
      | nil => nil
      | a :: tail => if (eq_nat c 0) then tail else a :: omit tail (c-1)
    end.

Compute omit (A::B::AB::nil) 0.

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

Fixpoint loop (l:list literal) (n neg:literal) (c:nat):=
match l with
nil => 0
| a::tl => if not a n neg then c else loop tl n neg c+1
end.

Definition listA := (A::B::AB::nil).
Definition unitClause := negA.

Definition listAPos := loop listA unitClause negation 0.

Compute omit listA listAPos.