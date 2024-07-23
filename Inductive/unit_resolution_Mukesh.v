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
Definition remove_literal_from_clause (l : literal) (c : clause) : clause :=
  match c with
  | consclause ls => consclause (remove eq_dec l ls)
  end.

Definition opposite (L : literal) : literal :=
  match L with
    | pos s => neg s
    | neg s => pos s
  end.
Definition memlc (l : literal) (c : clause) : Prop :=
  match c with
  | consclause ls => In l ls
  end.
 
 
Definition subset (c1 c2 : clause) : Prop :=
  match c1 with
  | consclause ls1 => forall (l : literal), In l ls1 -> memlc l c2
  end.

Inductive unitres : formula -> clause -> Prop :=
| subsumption : forall c:clause, forall f:formula, contains_clause f c -> forall c2:clause, subset c c2 -> unitres f c2
| resolution : forall c:clause, forall f:formula, unitres f c -> 
                forall l, is_literal_in_clause l c ->
                     unitres f (consclause [opposite l]) -> 
                      unitres f (remove_literal_from_clause l c) .


(*Proofs*)
Definition model_property (m : literal -> Prop) : Prop :=
    forall l:literal, ( m l -> m (opposite l) -> False) /\ ( (m (opposite l) -> False) -> m l).
Definition models_clause (m : literal -> Prop) (c : clause) : Prop :=
  model_property m -> exists l: literal, memlc l c /\ m l.
Definition models_formula (m : literal -> Prop) (f : formula) : Prop :=
  model_property m -> forall c: clause, contains_clause f c -> models_clause m c.

Definition entails (f : formula) (c : clause) : Prop :=
  (forall (m : literal -> Prop), model_property m -> models_formula m f -> models_clause m c).
(*
Assume m is a model of f, and c is a member of f, if c is derived from f with unit resolution then c is we have Logical Entailment
*)

Lemma subset_clause_prop : forall c1:clause,forall m:literal->Prop, (exists l:literal , memlc l c1 /\ m l) -> 
  forall c2:clause, subset c1 c2 -> exists l2:literal, memlc l2 c2 /\ m l2.
Proof.
intros c1 m c1prop c2 c1c2subset.
elim c1prop.
intros l0 meml0prop.
exists l0.
unfold subset in c1c2subset.
induction c1.
specialize c1c2subset with (l := l0).
unfold memlc in meml0prop.
split.
apply c1c2subset.
apply meml0prop.
apply meml0prop. 
Qed.

(*Lemma: Opposite is Idempotent*)
Lemma opp_is_idempotent:
forall l : literal, opposite( opposite l) =  l.
Proof.
destruct l.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

(* Function to check if two strings are equal *)
Definition string_beq (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

(* Function to check if two literals are equal *)
Definition literal_eqb (l1 l2 : literal) : bool :=
  match (l1, l2) with
  | (pos s1, pos s2) | (neg s1, neg s2) => string_beq s1 s2
  | (_, _) => false
  end.

Lemma remove_literal_from_empty_clause : forall l : literal,
  remove_literal_from_clause l (consclause []) = consclause [].
Proof.
  intros l.
  unfold remove_literal_from_clause.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma models_remove_literal_from_empty_clause : forall m l,
  (models_clause m (remove_literal_from_clause l (consclause [])) <-> 
  models_clause m (consclause [])).
Proof.
  intros m l.
  split.
  - (* Proving the forward direction *)
    intros H.
    rewrite remove_literal_from_empty_clause in H.
    exact H.
  - (* Proving the backward direction *)
    intros H.
    rewrite remove_literal_from_empty_clause.
    exact H.
Qed.

(*
1 goal
m : literal -> Prop
l' : literal
ls : list literal
l : literal
Hm_c : models_clause m (consclause (l' :: ls))
Hm_neg_l : models_clause m (consclause [opposite l])
IHls : models_clause m (consclause ls) ->
       models_clause m (remove_literal_from_clause l (consclause ls))
Heq : l' = l
______________________________________(1/1)
models_clause m (remove_literal_from_clause l (consclause (l' :: ls)))
*)

Theorem remove_equals : forall (l : literal) (ls : list literal),
(remove eq_dec l (l :: ls) = 
remove eq_dec l ls).
Proof.
Search (remove _ _ (_::_)). 
apply remove_cons.
Qed.

Check eq_dec.

Lemma remove_l_from_cons_l : forall
(ls : list literal)
(l : literal), ((remove_literal_from_clause l (consclause (l :: ls))) = 
(remove_literal_from_clause l (consclause ls))).
Proof.
intros.
cbn.
destruct (eq_dec l l) as [H | H] eqn:Ha.
reflexivity.
contradiction.
Qed.

(*1 goal
m : literal -> Prop
ls : list literal
l : literal
Hm_c : models_clause m (consclause (l :: ls))
Hm_neg_l : models_clause m (consclause [opposite l])
IHls : models_clause m (consclause ls) ->
       models_clause m (remove_literal_from_clause l (consclause ls))
______________________________________(1/1)
models_clause m (consclause ls)
*)

(*Current stage*)
Lemma models_ls : forall 
(m : literal -> Prop) 
(ls : list literal)
(l : literal),
models_clause m (consclause (l :: ls)) ->
models_clause m (consclause [opposite l]) ->
models_clause m (consclause ls).
Proof.
intros m ls l ha hb hc.

unfold models_clause in ha, hb |- *.

unfold memlc in ha, hb |- *.

pose proof (ha hc) as hd.

clear ha.

specialize (hb hc).

destruct hb as (l2 & hbl & hbr).
destruct hd as (l3 & hdl & hdr).

simpl in hdl.
destruct hdl as [hdl|hdl].

+
simpl in hbl.
rewrite hdl in hbl.
rewrite <- hdl in hdr.
rewrite <- hdl in hbl.
destruct hbl; try contradiction.
rewrite <- H in hbr.
unfold model_property in hc.
specialize (hc l).
destruct hc.
specialize (H0 hdr hbr).
contradiction.

+
exists l3.
split; assumption.
Qed.