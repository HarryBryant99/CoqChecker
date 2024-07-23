Search True.
Search (_ <= _) (_ + _).
SearchPattern (_ <= _).
SearchPattern (_ + _ <= _ + _).
SearchRewrite (_ + (_ - _)).

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
intros a b H.
split.
destruct H as [H1 H2]. (*Assing A to H1 and B to H2*)
exact H2.
intuition.
Qed.

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
intros A B H.
destruct H as [H1 | H1].
right; assumption.
left.
assumption.
Qed.


Check le_n.
Check le_S.

Lemma example4 : 3 <= 5.
Proof.
apply le_S.
apply le_S.
apply le_n.
Qed.

(*Reflexivity and Transitivity*)
Theorem le_refl : forall n, n <= n.
Proof.
  exact le_n.
Qed.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  induction 2; auto.
Qed.


Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
intros x y x10 y10.
apply le_trans with (m := 10).
assumption.
assumption.
Qed.


Print Nat.pred.

Lemma pred_S_eq : forall x y, x = S y -> Nat.pred x = y.
Proof.
intros x y q.
unfold Nat.pred.
rewrite q.
reflexivity.
Qed.


(*Exercises*)
Lemma q1: forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
intros A B C H.
destruct H as [H H1].
destruct H1 as [H1 H2].
split.
split.
assumption.
assumption.
assumption.
Qed.

Lemma q2: forall A B C D: Prop,(A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
intros A B C D H.
destruct H as [f [g [h1 h2]]].
split.
apply f.
exact h1.
apply g.
exact h2.
Qed.

Lemma q3: forall A: Prop, ~(A/\~A).
Proof.
intros A.
intros H.
destruct H as [h1 h2].
destruct h2.
exact h1.
Qed.

Lemma q4: forall A B C: Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
intros A B C H.
destruct H as [H | [H1 | H2]].
left.
left.
exact H.
left.
right.
exact H1.
right.
exact H2.
Qed.

Lemma q5: forall A B: Prop, (A\/B)/\~A -> B.
Proof.
intros A B H.
destruct H as [[h1 | h2] h3].
destruct h3.
exact h1.
exact h2.
Qed.


Lemma ex1 :
forall A:Type, forall P Q:A->Prop,
(forall x, P x) \/ (forall y, Q y) -> forall x, P x \/ Q x.
Proof.
intros A P Q H.
elim H.
intros H1.
left.
apply H1.
intros H2.
right.
apply H2.
Qed.

(*Harry Examples*)
Lemma Monika : forall a b:Prop, not((a \/ b) /\ (a \/ not b) /\ (not a \/ b) /\ (not a \/ not b)).
Proof.
intuition.
Qed.

(*More examples*)
Theorem or_left : forall (P Q : Prop), P -> P \/ Q.
Proof.
intros P Q P_holds.
left.
assumption.
Qed.


Variables P Q R : Prop. 
Theorem hilbert : (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
intros h1.
intros h2 h3.
apply h1.
exact h3.
apply h2.
exact h3.
Qed.