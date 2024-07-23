Require Import Bool.
Require Import String.
Require Import List.
Import List.ListNotations.
Open Scope string_scope.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
(* Class EqDec A : Type := {
  eq_dec: forall a1 a2 : A, {a1 = a2} + {a1 <> a2}
  }.
*)
Inductive literal : Type :=
  | pos : string -> literal
  | neg : string -> literal.
Definition clause := list(literal).
Definition formula := list(clause).

Fixpoint In (a:literal) (l:clause) {struct l} : Prop :=
  match l with
    | nil => False
    | b :: m => b = a \/ In a m
  end.

(*memlc*)

Definition memlc (l : literal) (c : clause) : Prop :=
  In l c.

(* Assume we have a decision procedure for literal equality *)
Lemma literal_eq_dec : forall (l1 l2 : literal), {l1 = l2} + {l1 <> l2}.
Proof.
intros.
decide equality; apply string_dec.
Defined.


Fixpoint memlc_bool (a:literal) (l:clause) : bool :=
  match l with
    | nil => false
    | b :: m => if literal_eq_dec a b then true else memlc_bool a m
  end.

(* Lemma: Soundness *)
Lemma memlc_bool_implies_memlc_true : forall (a : literal) (l : clause),
  memlc_bool a l = true -> In a l.
Proof.
  induction l as [| b m IHm].
  - (* Case: l = nil *)
    simpl. intros H. discriminate H.
  - (* Case: l = b :: m *)
    simpl. destruct (literal_eq_dec a b) as [H_eq | H_neq].
    + (* Subcase: a = b *)
      intros _. left. assert (b = a) as H_eq_rev by auto. assumption.
    + (* Subcase: a <> b *)
      intros H. right. apply IHm. exact H.
Qed.


Lemma memlc_bool_implies_memlc_false : forall (a : literal) (l : clause),
  memlc_bool a l = false -> ~In a l.
Proof.
  intros a l H.
  unfold not. intros H_in.
  induction l as [| b m IH].
  - (* Case when l is empty *)
    inversion H_in.
  - (* Case when l is not empty *)
    simpl in H. simpl in H_in.
    destruct H_in as [H_eq | H_in].
    + (* Case: a = b *)
      subst. 
      destruct (literal_eq_dec a a) as [H_eq_dec | H_neq_dec].
      * (* a = a is true *)
        discriminate H.
      * (* a = a is false, contradiction *)
        apply H_neq_dec. reflexivity.
    + (* Case: a is in the tail m *)
      destruct (literal_eq_dec a b) as [H_eq_dec | H_neq_dec].
      * (* a = b is true *)
        discriminate H.
      * (* a = b is false *)
        apply IH; assumption.
Qed.

(* Lemma: Completeness *)
Lemma memlc_implies_memlc_bool_true : forall (a : literal) (l : clause),
  In a l -> memlc_bool a l = true.
Proof.
  induction l as [| b m IHm].
  - (* Case: l = nil *)
    simpl. intros H. contradiction H.
  - (* Case: l = b :: m *)
    simpl. intros [H_eq | H_in].
    + (* Subcase: b = a *)
      subst. destruct (literal_eq_dec a a) as [_ | H_neq].
      * reflexivity.
      * exfalso. apply H_neq. reflexivity.
    + (* Subcase: In a m *)
      destruct (literal_eq_dec a b) as [H_eq | H_neq].
      * reflexivity.
      * apply IHm. exact H_in.
Qed.

Lemma memlc_implies_memlc_bool_false : forall (a : literal) (l : clause),
  ~In a l -> memlc_bool a l = false.
Proof.
  induction l as [| b m IHm].
  - (* Case: l = nil *)
    simpl. intros H. reflexivity.
  - (* Case: l = b :: m *)
    simpl. intros H.
    unfold not in H.
    assert (~ In a m) as H_tail.
    {
      intros H_in.
      apply H. right. assumption.
    }
    destruct (literal_eq_dec a b) as [H_eq | H_neq].
    + (* Case: a = b *)
      subst. exfalso. apply H. left. reflexivity.
    + (* Case: a <> b *)
      apply IHm. assumption.
Qed.

(* Theorem: Equivalence *)
Theorem memlc_equiv_true : forall (a : literal) (l : clause),
  memlc_bool a l = true <-> In a l.
Proof.
  split.
  - apply memlc_bool_implies_memlc_true.
  - apply memlc_implies_memlc_bool_true.
Qed.

Theorem memlc_equiv_false : forall (a : literal) (l : clause),
  memlc_bool a l = false <-> ~In a l.
Proof.
  split.
  - apply memlc_bool_implies_memlc_false.
  - apply memlc_implies_memlc_bool_false.
Qed.

(*is_literal_in_clause_prop*)

Fixpoint is_literal_in_clause_prop (l : literal) (c : clause) : Prop :=
  match c with
  | nil => False
  | hd :: tl => hd = l \/ is_literal_in_clause_prop l tl
  end.

Fixpoint is_literal_in_clause_bool (l : literal) (c : clause) : bool :=
  match c with
  | nil => false
  | hd :: tl => if literal_eq_dec l hd then true else is_literal_in_clause_bool l tl
  end.


Lemma in_clause_bool_implies_in_clause_prop_true :
  forall (l : literal) (c : clause),
    is_literal_in_clause_bool l c = true -> is_literal_in_clause_prop l c.
Proof.
  intros l c.
  induction c as [| hd tl IH].
  - simpl. intros H. inversion H.  (* Nil case: contradiction because false = true is impossible *)
  - simpl. intros H.
    destruct (literal_eq_dec l hd) as [H_eq | H_neq].
    + left. assert (hd = l) as H_eq_rev by auto. assumption.  (* If l equals hd, then we can conclude l is in the clause *)
    + right. apply IH. exact H.  (* Otherwise, we proceed with the induction hypothesis on the tail *)
Qed.

Lemma in_clause_bool_implies_in_clause_prop_false :
  forall (l : literal) (c : clause),
    is_literal_in_clause_bool l c = false -> ~is_literal_in_clause_prop l c.
Proof.
  intros l c.
  induction c as [| hd tl IH].
  - simpl. intros H. unfold not. intros. assumption.
  - simpl. intros H.
    destruct (literal_eq_dec l hd) as [H_eq | H_neq].
    + intros H_disj. discriminate.
    + intros H_disj. destruct H_disj.
      * assert (l = hd) as H_eq_rev by auto. contradiction.
      * apply IH in H. contradiction.
Qed.

Lemma in_clause_prop_implies_in_clause_bool_true :
  forall (l : literal) (c : clause),
    is_literal_in_clause_prop l c -> is_literal_in_clause_bool l c = true.
Proof.
  intros l c.
  induction c as [| hd tl IH].
  - simpl. intros H. contradiction.  (* Nil case: contradiction because False cannot be true *)
  - simpl. intros [H_eq | H_in].
    + destruct (literal_eq_dec l hd) as [H_dec | H_dec].
      * reflexivity.  (* If l equals hd, then we can conclude true *)
      * assert (l = hd) as H_eq_rev by auto. contradiction.  (* This case cannot happen as H_eq implies l equals hd *)
    + destruct (literal_eq_dec l hd) as [H_dec | H_dec].
      * reflexivity.  (* If l equals hd, then we can conclude true *)
      * apply IH. exact H_in.  (* Otherwise, we proceed with the induction hypothesis on the tail *)
Qed.

Lemma in_clause_prop_implies_in_clause_bool_false :
  forall (l : literal) (c : clause),
    ~ is_literal_in_clause_prop l c -> is_literal_in_clause_bool l c = false.
Proof.
  intros l c H_not_in_prop.
  induction c as [| hd tl IH].
  - (* Base case: Empty clause *)
    reflexivity.
  - (* Inductive case: Non-empty clause *)
    unfold is_literal_in_clause_bool.
    simpl.
    destruct (literal_eq_dec l hd) as [Heq | Hneq].
    + (* l = hd *)
      exfalso.
      apply H_not_in_prop.
      simpl.
      left.
      symmetry.
      exact Heq.
    + (* l <> hd *)
      apply IH.
      intro H_in_prop.
      apply H_not_in_prop.
      simpl.
      right.
      exact H_in_prop.
Qed.


Theorem is_literal_in_clause_equiv_true :
  forall (l : literal) (c : clause),
    is_literal_in_clause_bool l c = true <-> is_literal_in_clause_prop l c.
Proof.
  split.
  - apply in_clause_bool_implies_in_clause_prop_true.
  - apply in_clause_prop_implies_in_clause_bool_true.
Qed.

Theorem is_literal_in_clause_equiv_false :
  forall (l : literal) (c : clause),
    is_literal_in_clause_bool l c = false <-> ~is_literal_in_clause_prop l c.
Proof.
  split.
  - apply in_clause_bool_implies_in_clause_prop_false.
  - apply in_clause_prop_implies_in_clause_bool_false.
Qed.

(*Subset*)

Fixpoint literal_eq (l1 l2 : literal) : bool :=
  match l1, l2 with
  | pos s1, pos s2 => if string_dec s1 s2 then true else false
  | neg s1, neg s2 => if string_dec s1 s2 then true else false
  | _, _ => false
  end.

(* Correctness of literal_eq *)
Lemma literal_eq_correct : forall l1 l2, literal_eq l1 l2 = true <-> l1 = l2.
Proof.
  intros l1 l2.
  split.
  - intro H.
    destruct l1, l2; simpl in H.
    + destruct (string_dec s s0); [subst | discriminate]. reflexivity.
    + discriminate.
    + discriminate.
    + destruct (string_dec s s0); [subst | discriminate]. reflexivity.
  - intro H. subst.
    destruct l2; simpl.
    + destruct (string_dec s s). reflexivity. contradiction.
    + destruct (string_dec s s). reflexivity. contradiction.
Qed.

Fixpoint inb (l: literal) (c: clause) : bool :=
  match c with
  | [] => false
  | x :: xs => if literal_eq l x then true else inb l xs
  end.

Definition subset_bool (c1 c2: clause) : bool :=
  forallb (fun l => inb l c2) c1.

Definition subset_prop (c1 c2 : clause) : Prop :=
  forall l : literal, In l c1 -> In l c2.

Lemma subset_bool_implies_subset_prop_true:
  forall (c1 c2: clause), subset_bool c1 c2 = true -> subset_prop c1 c2.
Proof.
  intros c1 c2 H.
  unfold subset_bool in H.
  unfold subset_prop.
  intros l H_in_c1.
  apply forallb_forall with (x := l) in H.
  - unfold inb in H.
    revert H.
    induction c2 as [| x xs IH]; simpl; intros H.
    + discriminate H.
    + destruct (literal_eq l x) eqn:Heq.
      * apply literal_eq_correct in Heq. subst. left. reflexivity.
      * right. apply IH. exact H.
  - exact H_in_c1.
Qed.

(* Helper lemma for literal equality reflexivity *)
Lemma literal_eq_refl : forall l, literal_eq l l = true.
Proof.
  intros l. destruct l as [pos_str | neg_str].
  - unfold literal_eq. destruct (string_dec pos_str pos_str).
    + reflexivity.
    + contradiction n. reflexivity.
  - unfold literal_eq. destruct (string_dec neg_str neg_str).
    + reflexivity.
    + contradiction n. reflexivity.
Qed.

Lemma true_neq_false : true = false -> False.
Proof.
  intros H.
  discriminate H.
Qed.

Lemma true_false_iff_False : true = false <-> False.
Proof.
  split.
  - apply true_neq_false.
  - apply False_ind.
Qed.

Lemma inb_false_iff_not_in : forall l c,
  inb l c = false <-> ~ In l c.
Proof.
  intros l c. split.
  - intros H. unfold not. intros HIn.
    induction c as [| x xs IH].
    + inversion HIn.
    + simpl in H. simpl in HIn. destruct HIn as [H_eq | H_in].
      * subst. rewrite literal_eq_refl in H. discriminate H.
      * destruct (literal_eq l x) eqn:Heq.
        -- apply literal_eq_correct in Heq. subst. discriminate H.
        -- apply IH; assumption.
  - intros H. unfold not in H. induction c as [| x xs IH].
    + reflexivity.
    + simpl. destruct (literal_eq l x) eqn:Heq.
      * apply literal_eq_correct in Heq. subst. apply true_false_iff_False. apply H. left. reflexivity.
      * apply IH. intros H_in. apply H. right. assumption.
Qed.


Lemma forallb_false : forall (f : literal -> bool) (l : list literal),
  forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros f l.
  induction l as [| hd tl IH]; intros H.
  - simpl in H. discriminate H.
  - simpl in H. destruct (f hd) eqn:Hf_hd.
    + apply IH in H. destruct H as [x [H_in Hf_x]]. exists x. split.
      * right. exact H_in.
      * exact Hf_x.
    + exists hd. split.
      * left. reflexivity.
      * exact Hf_hd.
Qed.

Lemma subset_bool_implies_subset_prop_false :
  forall (c1 c2: clause), subset_bool c1 c2 = false -> ~subset_prop c1 c2.
Proof.
  intros c1 c2 H_subset_bool H_subset_prop.
  unfold subset_bool in H_subset_bool.
  unfold subset_prop in H_subset_prop.
  apply forallb_false in H_subset_bool.
  destruct H_subset_bool as [l [H_in_c1 H_inb_false]].
  apply inb_false_iff_not_in in H_inb_false.
  unfold not in H_inb_false.
  apply H_inb_false.
  apply H_subset_prop.
  exact H_in_c1.
Qed.

Lemma literal_eq_reflexive : forall l,
  literal_eq l l = true.
Proof.
  intros l.
  destruct l; simpl.
  - destruct (string_dec s s); [reflexivity | contradiction].
  - destruct (string_dec s s); [reflexivity | contradiction].
Qed.

Lemma literal_eq_false_in_tail : forall l x xs,
  literal_eq l x = false ->
  In l (x :: xs) ->
  In l xs.
Proof.
  intros l x xs H_eq H_in.
  simpl in H_in.
  destruct H_in as [H_eq_x | H_in_tail].
  - (* Case: l = x *)
    rewrite H_eq_x in H_eq.
    rewrite literal_eq_reflexive in H_eq. (* Apply the lemma *)
    discriminate H_eq. (* Derive a contradiction *)
  - (* Case: l is in the tail xs *)
    assumption.
Qed.

Lemma subset_prop_implies_subset_bool_true:
  forall (c1 c2: clause), subset_prop c1 c2 -> subset_bool c1 c2 = true.
Proof.
  intros c1 c2 H.
  unfold subset_bool.
  apply forallb_forall.
  intros l H_in_c1.
  unfold subset_prop in H.
  specialize (H l H_in_c1).
  clear H_in_c1.
  induction c2 as [| x xs IH].
  - simpl in H. contradiction.
  - simpl.
    destruct (literal_eq l x) eqn:Heq.
    + reflexivity.
    + simpl in IH.
      apply IH.
      apply literal_eq_false_in_tail in H.
      apply H.
      assumption.
Qed.

Lemma inb_true_iff_in : forall (l : literal) (c : clause),
  inb l c = true <-> In l c.
Proof.
  intros l c. split.
  - (* -> direction *)
    intros H. induction c as [| x xs IH].
    + simpl in H. discriminate H.
    + simpl in H. destruct (literal_eq l x) eqn:Heq.
      * apply literal_eq_correct in Heq. subst. left. reflexivity.
      * right. apply IH. assumption.
  - (* <- direction *)
    intros H. induction c as [| x xs IH].
    + simpl in H. contradiction.
    + simpl. destruct H as [H_eq | H_in].
      * subst. rewrite literal_eq_refl. reflexivity.
      * destruct (literal_eq l x) eqn:Heq.
        -- reflexivity.
        -- apply IH. assumption.
Qed.

Lemma subset_prop_implies_subset_bool_false :
  forall (c1 c2 : clause),
    ~ subset_prop c1 c2 -> subset_bool c1 c2 = false.
Proof.
  intros c1 c2 H_not_subset.
  unfold subset_bool.
  unfold not in H_not_subset.
  induction c1 as [| l1 c1' IH].
  - (* Base case: c1 is empty *)
    exfalso. (* derive a contradiction *)
    apply H_not_subset.
    intros l H_in. 
    inversion H_in. (* `[]` is a subset of any list *)
  - (* Inductive case: c1 has at least one literal *)
    simpl.
    destruct (inb l1 c2) eqn:H_inb_l1.
    + (* inb l1 c2 = true *)
      apply inb_true_iff_in in H_inb_l1.
      assert (H: ~ subset_prop c1' c2).
      {
        unfold not. intros H_subset_prop'.
        apply H_not_subset.
        intros l H_in.
        destruct H_in as [H_eq | H_in].
        - subst. assumption.
        - apply H_subset_prop'. assumption.
      }
      apply IH in H.
      simpl.
      assumption.
    + (* inb l1 c2 = false *)
      simpl.
      reflexivity.
Qed.

Theorem subset_bool_iff_subset_prop:
  forall (c1 c2: clause), subset_bool c1 c2 = true <-> subset_prop c1 c2.
Proof.
  split.
  - apply subset_bool_implies_subset_prop_true.
  - apply subset_prop_implies_subset_bool_true.
Qed.

Theorem subset_bool_iff_subset_prop_false:
  forall (c1 c2: clause), subset_bool c1 c2 = false <-> ~subset_prop c1 c2.
Proof.
  split.
  - apply subset_bool_implies_subset_prop_false.
  - apply subset_prop_implies_subset_bool_false.
Qed.