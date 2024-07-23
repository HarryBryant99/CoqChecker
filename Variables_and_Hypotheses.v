(*Coq Art Book*)

Variables P Q R T : Prop.

Section example_of_assumption. 
Hypothesis H : P->Q->R. 
Lemma Ll : P->Q->R. 
Proof.
Show 1.
assumption. 
Qed. 

End example_of_assumption. 

(*Example Proofs*)
Lemma id_P : P -> P.
Proof.
intros p.
assumption.
Qed.

Lemma id_PP : (P->P)->(P->P).
Proof.
intros p p'.
assumption.
Qed.

Lemma imp_trans : (P->Q)->(Q->R)->P->R.
Proof.
intros a b p.
apply b.
apply a.
assumption.
Qed.

Lemma imp_perm : (P->Q->R)->(Q->P->R).
Proof.
intros a q p.
apply a.
assumption.
assumption.
Qed.

Lemma ignore_Q : (P->R)->P->Q->R.
Proof.
intros a p q.
apply a.
assumption.
Qed.

Lemma delta_imp : (P->P->Q)->P->Q.
Proof.
intros a p.
apply a.
assumption.
assumption.
Qed.

Lemma delta_impR : (P->Q)->(P->P->Q).
Proof.
intros a p p'.
apply a.
assumption.
Qed.

Lemma diamond : (P->Q)->(P->R)->(Q->R->T)->P->T.
Proof.
intros a b c p.
apply c.
apply a.
assumption.
apply b.
assumption.
Qed.

Lemma weak_peirce : ((((P->Q)->P)->P)->Q)->Q.
Proof.
intros a.
apply a.
intros b.
apply b.
intros p.
apply a.
intros c.
assumption.
Qed.

Section proof_of_triple_impl. 
Hypothesis H : ((P->Q)->Q)->Q. 
Hypothesis p : P. 
Lemma Rem: (P->Q)->Q. 
Proof (fun HO:P->Q => HO p). 
Theorem triple_impl : Q. 
Proof (H Rem). 
End proof_of_triple_impl.
Print triple_impl.

Theorem triple_impl_one_shot : (((P->Q)->Q)->Q)->P->Q. 
Proof. 
intros H p; apply H; intro HO; apply HO; assumption. 
Qed.

Lemma L3 : (P->Q)->(P->R)->(P->Q->R->T)->P->T. 
Proof. 
intros H HO Hi p. 
apply Hi; [idtac | apply H | apply HO]; assumption. 
Qed. 

Theorem then_fail_example : (P->Q)->(P->Q). 
Proof. 
intro X; apply X; fail. 
Qed. 

(*
Theorem then_fail_example2 : ((P->P)->(Q->Q)->R)->R.
Proof. 
intro X; apply X; fail. 
Error : Tactic failure 
Abort.
*)

Theorem try_example : (P->Q->R->T) -> (P->Q) -> (P->R->T) .
Proof.
intros H H' P r. 
apply H; try assumption. 
(*Can use try to use the fact that T is implied by R which is a hyptothesis, 
and Q implies R*) 
apply H'; assumption. 
Qed.

(*Example Proofs - one step*)
Lemma id_P2 : P -> P.
Proof.
intros p; assumption.
Qed.

Lemma imp_trans2 : (P->Q)->(Q->R)->P->R.
Proof.
intros a b p; apply b; apply a; assumption.
Qed.

Lemma delta_impR2 : (P->Q)->(P->P->Q).
Proof.
intros a p p'; apply a; assumption.
Qed.

Section section_for_cut_example. 
Hypotheses (H : P->Q) 
(H0 : Q->R) 
(H1 : (P->R)->T->Q) 
(H2 : (P->R)->T). 

Theorem cut_example: Q. 
Proof. 
cut (P->R).
intros H3.
apply H1; [assumption | apply H2; assumption].
intro p. apply H0. apply H. assumption.
Qed.

Theorem non_cut_example: Q.
Proof.
apply H1.
intros.
apply H0; apply H; assumption.
apply H2.
intros.
apply H0; apply H; assumption.
Qed.
End section_for_cut_example.

Theorem disj4_3 : forall P Q R S:Prop, R -> P\/Q\/R\/S. 
Proof 
(fun P Q R S r => or_intror _ (or_intror _ (or_introl _ r))). 

Theorem conv_example : forall n: nat, 7*5 < n -> 6*6 <= n. 
intros.
exact H. 
Qed.

Theorem le_i_SSi : forall i : nat, i <= S (S i).
Proof. 
intro i. 
apply le_S.
apply le_S.
apply le_n.
Qed.

Theorem lt_S : forall n p:nat, n < p -> n < S p. 
Proof. 
intros n p H. 
unfold lt. apply le_S; trivial. 
Qed.

Section ex_falso_quodlibet. 
Hypothesis ff : False. 
Lemma ex1 : 220 = 284. 
Proof. 
apply False_ind. 
exact ff. 
Qed. 
Lemma ex2 : 220 = 284. 
Proof. 
elim ff. 
Qed. 
End ex_falso_quodlibet. 

Theorem double_neg_i : forall P: Prop, P -> ~~P. 
Proof. 
intros P p H.
apply H. assumption.
Qed.

(*Exercise 5.3*)
Theorem e5_3_1 : ~False.
Proof.
unfold not.
intros.
assumption.
Qed.

Theorem e5_3_2 : forall P : Prop,  ~~~P -> ~P.
Proof.
intros P H HP.
apply H.
intros HNP.
apply HNP.
assumption.
Qed.

Theorem e5_3_3 : forall P Q : Prop, ~~~P -> P -> Q.
Proof.
unfold not.
intros.
destruct H.
intros.
apply H.
assumption.
Qed.

Theorem e5_3_4 : forall P Q : Prop, (P->Q)->~Q->~P.
Proof.
intros.
unfold not.
intros.
destruct H0.
apply H.
assumption.
Qed.

Theorem e5_3_5 : forall P Q R : Prop, (P->Q)->(P->~Q)->P->R.
Proof.
intros.
destruct H0.
assumption.
apply H.
assumption.
Qed.

Theorem conj3' : forall P Q R:Prop, P->Q->R->P/\Q/\R. 
Proof. 
repeat split. assumption. assumption. assumption. 
Qed.

Theorem disj4_3' : forall P Q R S:Prop, R->P\/Q\/R\/S. 
Proof. 
right. right. left. assumption. 
Qed.

Theorem and_commutes: forall A B:Prop, A/\B->B/\A. 
Proof. 
intros A B H.
elim H.
split.
assumption. assumption.
Qed.

(*Exercise 5.5*)
Theorem e5_5: forall (A : Set) (a b c d: A), a=c \/ b=c \/ c=c \/ d=c.
Proof.
intros.
right. right. left. reflexivity.
Qed.

(*Exercise 5.6*)
Theorem e5_6_1: forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
intros.
destruct H. destruct H0.
split. split.
assumption. assumption. assumption.
Qed. 

(*Exercise 5.9*)
Parameter A : Type.
Parameter P1 Q1 : A -> Prop.
Theorem e5_9_1: (exists x : A, P1 x \/ Q1 x) -> (exists x : A, P1 x) \/ (exists x : A, Q1 x).
Proof.
  intros H.
  destruct H as [x [HP | HQ]].
  - left. exists x. apply HP.
  - right. exists x. apply HQ.
Qed.

(*Exercise 5.16*)
Definition my_le (n p:nat) := 
forall P:nat -> Prop, P n ->(forall q:nat, P q -> P (S q)) -> P p. 

Lemma my_le_n: forall n: nat, my_le n n.
Proof.
intros n P H_base H_step.
induction n as [|n' IHn'].
  - apply H_base.
  - apply H_base.
Qed.

(*Exercise 6.3*)
Theorem bool_equal : forall b:bool, b = true \/ b = false.
Proof.
intros.
destruct b.
left. reflexivity.
right. reflexivity.
Qed.

