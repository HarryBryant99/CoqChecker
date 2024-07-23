Require Import String.
Require Import Ascii.
Open Scope string_scope.

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.


Inductive literal : Set :=
  | EmptyLiteral : literal
  | Literal : ascii -> literal -> literal.

Definition literal_dec : forall s1 s2 : literal, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.

Definition E : literal := EmptyLiteral.

Definition A : literal := Literal "A" E.
Definition B : literal := Literal "B" E.

Check A.

Compute literal_dec A B.

Definition f (a b : literal) : bool :=
  if literal_dec a b then true else false.

Compute f A A.
Compute f A B.


(*-----------------------------------------------------------------------*)

Fixpoint append (s1 s2 : literal) : literal :=
  match s1 with
  | EmptyLiteral => s2
  | Literal c s1' => Literal c (s1' ++ s2)
  end
where "s1 ++ s2" := (append s1 s2) : literal_scope.