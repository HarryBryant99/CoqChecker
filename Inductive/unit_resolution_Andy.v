Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.

Inductive clause : Type :=
  | nilclause : clause
  | consclause : literal -> clause -> clause.

Infix "::" := consclause (at level 60, right associativity) : clause_scope.
Open Scope clause_scope.

Inductive formula : Type :=
| nilformula : formula
| consformula : clause -> formula -> formula.

Infix "::" := consformula (at level 60, right associativity) : formula_scope.
Open Scope formula_scope.

(* Function to check if two strings are equal *)
Definition string_beq (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* Function to check if two literals are equal *)
Definition literal_eqb (l1 l2 : literal) : bool :=
  match (l1, l2) with
  | (pos s1, pos s2) | (neg s1, neg s2) => string_beq s1 s2
  | (_, _) => false
  end.

(* Function to check if two clauses are equal *)
Fixpoint clause_eqb (c1 c2 : clause) : bool :=
  match (c1, c2) with
  | (nilclause, nilclause) => true
  | (consclause l1 ls1, consclause l2 ls2) =>
    if literal_eqb l1 l2 then clause_eqb ls1 ls2 else false
  | (_, _) => false
  end.

(* Function to check if a clause is a member of the complement of a formula *)
Fixpoint memcf (f : formula) (c : clause) : bool :=
  match f with
  | nilformula => false
  | consformula cl rest => if clause_eqb cl c then true else memcf rest c
  end.

(* Subclause relation *)
Definition subclause (c1 c2 : clause) : Prop :=
  memcf (consformula c1 nilformula) c2 = true.

(* Opposite literal *)
Definition opposite (l : literal) : literal :=
  match l with
  | pos s => neg s
  | neg s => pos s
  end.

Fixpoint remlc (l : literal) (f : clause) : clause :=
  match f with
  | nilclause => nilclause
  | consclause l' ls =>
    if literal_eqb l l' then
      ls
    else
      consclause l' (remlc l ls)
  end.

(* Function to check if a literal exists in a clause *)
Fixpoint exists_literal (l : literal) (c : clause) : bool :=
  match c with
  | nilclause => false
  | consclause l' rest => if literal_eqb l l' then true else exists_literal l rest
  end.

(* Function to check if there exists a literal in a clause where its negation also exists *)
Fixpoint exists_opposite_literal (c : clause) : bool :=
  match c with
  | nilclause => false
  | consclause l rest =>
    exists_literal (opposite l) rest || exists_opposite_literal rest
  end.

(*
(* Resolution operation *)
Inductive resolve (f : formula) (c : clause) : Prop :=
  | Resolution : forall c1 c2,
      subclause c1 c ->
      subclause c2 c ->
      memcf c1 f ->
      memcf c2 f ->
      unit_resolution f c1 c2 ->
      (forall l, c1 :: l -> ~memcf (inslc (opposite l) c2) f) ->
      (forall l, c2 :: l -> ~memcf (inslc (opposite l) c1) f) ->
      resolve f c.
*)

(* Function to resolve a single clause *)
Fixpoint resolve_clause (c : clause) (cl : clause) : clause :=
  match cl with
  | nilclause => nilclause
  | consclause lit rest =>
    let filtered_rest := resolve_clause c rest in
    if exists_literal (opposite lit) rest then
      remlc lit (remlc (opposite lit) filtered_rest)
    else
      consclause lit filtered_rest
  end.

(* Function to resolve a clause in a formula *)
Fixpoint resolve (c : clause) (f : formula) : formula :=
  match f with
  | nilformula => nilformula
  | consformula cl rest =>
    let filtered_cl := resolve_clause c cl in
    consformula filtered_cl (resolve c rest)
  end.

(* Test clauses *)
Definition c1 := consclause (pos "p") (consclause (neg "q") nilclause).
Definition c2 := consclause (neg "q") (consclause (pos "r") nilclause).
Definition c3 := consclause (pos "p") (consclause (neg "p") nilclause).

(* Test formula *)
Definition f := consformula c1 (consformula c2 (consformula c3 nilformula)).

(* Test the resolve function *)
Compute resolve c1 f.
Compute resolve c2 f.
Compute resolve c3 f.

(* Insert literal into clause *)
Fixpoint inslc (lit : literal) (cl : clause) : clause :=
  match cl with
  | nilclause => consclause lit nilclause
  | consclause lit' cl' => consclause lit' (inslc lit cl')
  end.

(* Concatenation of clauses *)
Fixpoint ConcClause (c1 c2 : clause) : clause :=
  match c1 with
  | nilclause => c2
  | consclause l c1' => consclause l (ConcClause c1' c2)
  end.

(* Unit resolution *)
Inductive unit_resolution (f : formula) (c1 c2 : clause) : Prop :=
  | Subsumption : forall c2,
      subclause c1 c2 ->
      memcf c1 f ->
      resolve f c2 ->
      unit_resolution f c1 c2
  | Resolution : forall l c1' c2',
      resolve f (inslc l c1') ->
      resolve f (inslc (opposite l) c2') ->
      resolve f (ConcClause c1' c2') ->
      unit_resolution f c1 c2.