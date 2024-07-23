Require Import Bool.
Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope string_scope.
(* Class EqDec A : Type := {
  eq_dec: forall a1 a2 : A, {a1 = a2} + {a1 <> a2}
  }.
*)
Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.
Definition clause := list(literal).
Definition formula := list(clause).
Fixpoint contains_clause (f : formula) (cl : clause) : Prop :=
  match f with
  | nil => False
  | cs :: rest => cs = cl \/ contains_clause rest cl
  end.
Fixpoint is_unit_clause (l : literal) (c : clause)  : Prop :=
  match c with
  | nil => False
  | hd :: nil => hd = l
  | _ :: _ => False
  end.
Definition concat_clauses (c1 c2 : clause) : clause :=
  match c1 with
      | nil => c2
      | a :: l1 => a :: app l1 c2
  end.
(* Define the equality function for literals *)
Lemma literal_eq_dec : forall (l1 l2 : literal), {l1 = l2} + {l1 <> l2}.
Proof.
intros.
decide equality; apply string_dec.
Defined.
(*fix*)

Fixpoint is_literal_in_clause (l : literal) (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: tl => if literal_eq_dec l hd then true else is_literal_in_clause l tl
  end.

(*
Lemma lit_eq_dec : forall a b : literal, {a = b} + {a <> b}.
Proof.
   intros a b.
   destruct a as [s1 | s1]; destruct b as [s2 | s2].
   - destruct (string_dec s1 s2).
    + left. rewrite e. reflexivity.
    + right. intro H. inversion H. contradiction.
   - right. intro H. inversion H.
   - right. intro H. inversion H.
   - destruct (string_dec s1 s2).
    + left. rewrite e. reflexivity.
    + right. intro H. inversion H. contradiction.
Qed.
*)

Definition lit_eq_dec (a b : literal) : bool :=
  match a, b with
  | pos s1, pos s2 => if string_dec s1 s2 then true else false
  | neg s1, neg s2 => if string_dec s1 s2 then true else false
  | _, _ => false
  end.

Fixpoint remove (x : literal) (l : list literal){struct l} : list literal :=
      match l with
        | nil => nil
        | y::tl => if (lit_eq_dec x y) then remove x tl else y::(remove x tl)
      end.

(* Instance literal_EqDec : EqDec literal :=
  { eq_dec: forall x y : literal, {x = y} + {x <> y}}.
*)
Definition remove_literal_from_clause (l : literal) (c : clause) : clause :=
  remove l c.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

Fixpoint literal_eq (l1 l2 : literal) : bool :=
  match l1, l2 with
  | pos s1, pos s2 => if string_dec s1 s2 then true else false
  | neg s1, neg s2 => if string_dec s1 s2 then true else false
  | _, _ => false
  end.

(*
Lemma literal_eq_dec : forall (l1 l2 : literal), {l1 = l2} + {l1 <> l2}.
Proof.
intros.
decide equality; apply string_dec.
Defined.
*)

Fixpoint memlc (a:literal) (l:clause) : bool :=
    match l with
      | nil => false
      | b :: m => if literal_eq_dec a b then true else memlc a m
    end.

Fixpoint clause_eq_dec (c1 c2 : clause) : bool :=
    match c1, c2 with
    | nil, nil => true
    | x :: xs, y :: ys => if literal_eq_dec x y then clause_eq_dec xs ys else false
    | _, _ => false
    end.

Fixpoint memcf (a:clause) (l:formula) : bool :=
    match l with
      | nil => false
      | b :: m => if clause_eq_dec a b then true else memcf a m
    end.
 
(* Membership test *)
Fixpoint inb (l: literal) (c: clause) : bool :=
  match c with
  | [] => false
  | x :: xs => if literal_eq l x then true else inb l xs
  end.

(* Boolean version of subset *)
Definition subset (c1 c2: clause) : bool :=
  forallb (fun l => inb l c2) c1.

Inductive unitres : formula -> clause -> Prop :=
| subsumption : forall (c c2 : clause) (f : formula),
    memcf c f = true ->
    subset c c2 = true ->
    unitres f c2
| resolution : forall (c : clause) (l : literal) (f : formula),
    unitres f c ->
    is_literal_in_clause l c = true ->
    unitres f (cons (opposite l) []) ->
    unitres f (remove_literal_from_clause l c).

Check unitres.

(*---------------------------------------------------------------------*)

(*
- Write a definition to set up a subsumption
  - Takes in f and c, produces UnitRes
- Write a definition to compute a resolution
  - Takes in c, l and f, produces UnitRes
*)

Inductive formula_clause_pair : Set :=
| mk_fcp : formula -> clause -> formula_clause_pair.
Check mk_fcp.
Definition example_pair : formula_clause_pair := mk_fcp [[pos "a"; neg "b"]] [pos "a"].
Check example_pair.
Compute example_pair.

Definition list_of_ures := list(formula_clause_pair).

Definition check_subsumption (c c2 : clause) (f : formula) : bool :=
  match memcf c f with
  | true => subset c c2
  | false => false
  end.

Definition append_to_list_of_ures (n : formula_clause_pair) (s : list_of_ures) : list_of_ures :=
  n :: s.

Definition compute_subsumption (c c2 : clause) (f : formula) (s : list_of_ures) : list_of_ures :=
  match check_subsumption c c2 f with
  | true => append_to_list_of_ures (mk_fcp f c2) s
  | false => s
  end.

(* Define the equality relation for formula_clause_pair *)
Definition fcp_eq_dec (a b : formula_clause_pair) : bool :=
  match a, b with
  | mk_fcp f1 c1, mk_fcp f2 c2 =>
    if list_eq_dec (list_eq_dec literal_eq_dec) f1 f2 then
      if list_eq_dec literal_eq_dec c1 c2 then
        true
      else
        false
    else
      false
  end.

Definition example_pair1 : formula_clause_pair := mk_fcp [[pos "a"; neg "b"]] [pos "a"].
Definition example_pair2 : formula_clause_pair := mk_fcp [[pos "a"; neg "b"]] [pos "b"].

Compute fcp_eq_dec example_pair1 example_pair1.


Fixpoint mempu (a:formula_clause_pair) (l:list_of_ures) : bool :=
    match l with
      | nil => false
      | b :: m => if fcp_eq_dec a b then true else mempu a m
    end.

Definition check_resolution (c : clause) (l : literal) (f : formula) (s : list_of_ures) : bool :=
  match mempu (mk_fcp f c) s with
  | true =>
    match is_literal_in_clause l c with
    | true => match mempu (mk_fcp f [opposite l]) s with
      | true => true
      | false => false
      end
    | false => false
    end
  | false => false
  end.

Definition compute_resolution (c : clause) (l : literal) (f : formula) (s : list_of_ures) : clause :=
  match check_resolution c l f s with
  | true => remove_literal_from_clause l c
  | false => c
end.

Definition is_resolution_complete (c : clause) (l : literal) (f : formula) (s : list_of_ures) : list_of_ures :=
  let result := compute_resolution c l f s in
  match result with
  | [] => []
  | _  => append_to_list_of_ures (mk_fcp f result) s
  end.

(*---------------------------------------------------------------------*)
(*Examples*)
(*(a or b) and (¬a)*)
Definition c1: clause := [pos "a"; pos "b"].
Definition c2: clause := [neg "a"].
Definition f: formula := [c1; c2].
Definition s: list_of_ures := [].

Compute subsumption c1 c1 f.
Compute subsumption c2 c2 f.

Compute In [pos "a"; pos "b"] [[pos "a"; pos "b"]; [neg "a"]].
Compute In [pos "c"] [[pos "a"; pos "b"]; [neg "a"]].

Compute memcf [pos "a"; pos "b"] [[pos "a"; pos "b"]; [neg "a"]].
Compute memcf [pos "c"] [[pos "a"; pos "b"]; [neg "a"]].

Compute subset c1 c1.
Compute subset [pos "a"] c1.

Compute resolution c1 (pos "a") f.

Compute is_literal_in_clause (pos "a") c1.

Compute resolution [pos "a"; pos "b"] (pos "a") [[pos "a"; pos "b"]; [neg "a"]].

Compute remove_literal_from_clause (pos "a") [pos "a"; pos "b"].


Compute lit_eq_dec (pos "a") (pos "a").
Compute lit_eq_dec (pos "a") (pos "b").
Compute if lit_eq_dec (pos "a") (pos "b") then [] else [pos "b"].
Compute if lit_eq_dec (pos "a") (pos "a") then if lit_eq_dec (pos "a") (pos "b") then [] else [pos "b"] else pos "a" :: (if lit_eq_dec (pos "a") (pos "b") then [] else [pos "b"]).

Definition s1 := compute_subsumption c1 c1 f s.
Compute s1.
Definition s2 := compute_subsumption c2 c2 f s1.
Compute s2.
Definition r1 := compute_resolution c1 (pos "a") f s2.
Compute r1.

Definition p1 : formula_clause_pair := mk_fcp f c1.
Compute mempu p1 s1.
Compute mempu p1 s.

(*(p or ¬q or r) and (q)*)
Definition c3: clause := [pos "p"; neg "q"; pos "r"].
Definition c4: clause := [pos "q"].
Definition f2: formula := [c3; c4].

Compute subsumption c3 c3 f2.
Compute subsumption c4 c4 f2.
Definition s3 := compute_subsumption c3 c3 f2 s.
Compute s3.
Definition s4 := compute_subsumption c4 c4 f2 s3.
Compute s4.
Definition r2 := compute_resolution c3 (neg "q") f2 s4.
Compute r2.
Compute resolution c3 (neg "q") f2.

(*(p) and (¬p or q) and (¬q)*)
Definition c5: clause := [pos "p"].
Definition c6: clause := [neg "p"; pos "q"].
Definition c7: clause := [neg "q"].
Definition f3: formula := [c5; c6; c7].

Compute subsumption c5 c5 f2.
Compute subsumption c6 c6 f2.
Compute subsumption c7 c7 f2.

Compute resolution c5 (pos "p") f3.
Compute resolution c6 (neg "p") f3.

Definition add_element {A : Type} (x : A) (lst : list A) : list A :=
  x :: lst.

Definition c8: clause := [pos "q"].
Definition f3':= (add_element c8 f3).
Compute resolution c8 (pos "q") f3'.

Definition s5 := compute_subsumption c5 c5 f3 s.
Compute s5.
Definition s6 := compute_subsumption c6 c6 f3 s5.
Compute s6.
Definition r3 := compute_resolution c6 (neg "p") f3 s6.
Compute r3.

Definition s7 := is_resolution_complete c6 (neg "p") f3 s6.
Compute s7.

Definition s8 := compute_subsumption c7 c7 f3 s7.
Compute s8.
Definition c8: clause := [pos "q"].
Definition r4 := compute_resolution c8 (pos "q") f3 s8.
Compute r4.

Compute is_resolution_complete c8 (pos "q") f3 s8.
