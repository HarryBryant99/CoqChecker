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
 
Inductive clause : Type :=
  | consclause : list(literal) -> clause.
 
Inductive formula : Type :=
  | nilformula : formula
  | consformula : list(clause) -> formula.
 
Fixpoint contains_clause (f : formula) (cl : clause) : Prop :=
  match f with
  | nilformula => False
  | consformula cs  => In cl cs
  end.
 
Fixpoint unit_literal_in_clause (l : literal) (c : clause)  : Prop :=
  match c with
  | consclause (nil) => False
  | consclause (l::nil)=> True
  | consclause _ => False
  end.
 
Fixpoint concat_clauses (c1 c2 : clause) : clause :=
  match c1 with
  | consclause ls1 => 
    match c2 with
     | consclause ls2 => consclause (ls1 ++ ls2)
    end
  end. 
 
Fixpoint is_literal_in_clause (l : literal) (c : clause) : Prop :=
  match c with
  | consclause ls => In l ls
  end.
 
Lemma eq_dec : forall a b : literal, {a = b} + {a <> b}.
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
 
(* Instance literal_EqDec : EqDec literal :=
  { eq_dec: forall x y : literal, {x = y} + {x <> y}}.
*)

Fixpoint remove_literal_from_clause (l : literal) (c : clause) : clause :=
  match c with
  | consclause ls => consclause (remove eq_dec l ls)
  end.
 
Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.

Fixpoint subset (c1 c2 : clause) : Prop :=
  match c1 with
  | consclause ls1 => forall (l : literal), In l ls1 -> is_literal_in_clause l c2
  end.
 
Inductive unitres : formula -> clause -> Prop :=
| subsumption : forall c:clause, forall f:formula, contains_clause f c -> forall c2:clause, subset c c2 -> unitres f c2
| resolution : forall c:clause, forall f:formula, unitres f c -> 
                forall l, is_literal_in_clause l c -> 
                  forall c2:clause, unit_literal_in_clause (opposite l) c2 ->
                     unitres f c2 -> unitres f (remove_literal_from_clause l c) .

Definition subsumption_unitres (c : clause) (f : formula) (c2 : clause) : Prop :=
  forall (H : contains_clause f c), subset c c2 -> unitres f c2.

Compute subsumption_unitres
  (consclause [pos "p"; neg "q"; pos "r"])
  (consformula [consclause [pos "p"; neg "q"; pos "r"]; consclause [neg "p"; pos "q"; pos "s"]; consclause [pos "p"; pos "q"; neg "r"]])
  (consclause [pos "p"; neg "q"; pos "r"; neg "s"]).

Definition resolution_unitres (c : clause) (f : formula) (l : literal) (c2 : clause) : Prop :=
  forall (H : unitres f c),
  forall (H_lit : is_literal_in_clause l c),
  forall (H_unit : unit_literal_in_clause (opposite l) c2),
  unitres f (remove_literal_from_clause l c).

Compute resolution_unitres
  (consclause [pos "p"; neg "q"; pos "r"])
  (consformula [consclause [pos "p"; neg "q"; pos "r"]; consclause [neg "p"; pos "q"; pos "s"]; consclause [pos "p"; pos "q"; neg "r"]])
  (pos "r")
  (consclause [pos "p"; neg "q"; pos "r"; neg "s"]).


(*Proofs*)

Definition model (m : formula -> Prop) (f : formula) : Prop :=
  m f.

Definition entails_OLD (f : formula) (c : clause) : Prop :=
  (exists (m : formula -> Prop), model m f /\ contains_clause f c).

Lemma unit_resolution_entails_logical_entailment_OLD : forall (f : formula) (c : clause),
  (forall (m : formula -> Prop), model m f ->
    contains_clause f c ->
    unitres f c ->
    entails_OLD f c).
Proof.
  intros f c m H_model_m H_contains_c H_unitres_c.
  unfold entails_OLD.
  exists m.
  split.
  - assumption.
  - assumption.
Qed.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : formula -> Prop), model m f -> contains_clause f c).

Theorem unit_resolution_soundness : forall (f : formula) (c : clause),
    unitres f c ->
    entails f c.
Proof.
  intros f c H_unitres.
  destruct H_unitres as [c1 | c2].
  - (* Case 1: c1 directly contained in f *)
    (* We need to show that f entails c2 *)
    unfold entails.
    intros m H_model.
    
  - (* Case 2: c2 derived from c1 by removing a literal *)
    
Abort.



















