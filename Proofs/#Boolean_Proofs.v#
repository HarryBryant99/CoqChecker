Lemma q3: forall A: Prop, ~(A/\~A).
Proof.
intros A.
intros H.
destruct H as [h1 h2].
destruct h2.
exact h1.
Qed.


Lemma and : forall X Y Z:Prop, ~((Z \/ Y) /\ ~(Z \/ Y)).
Proof.
intros.
intros h.
destruct h as [h1 h2].
destruct h1 as [j1 | j2].
destruct h2.
left.
assumption.
destruct h2.
right.
assumption.
Qed.

(*
{{X, ¬Y }, {Y, Z}, {¬X, ¬Y, Z}, {¬Z}}
*)

Lemma aandnota : forall X Y Z:Prop, ~((X\/~Y) /\ (Y\/Z) /\ (~X\/~Y\/Z) /\ (~Z)).
Proof.
intros X Y Z h.
destruct h as [h1 [h2 [h3 h4]]].
destruct h1 as [j1 | j2].
destruct h2 as [j3 | j4].
destruct h3 as [j5 | [j6 | j7]].
destruct j5.
assumption.
destruct j6.
assumption.
destruct h4.
assumption.
destruct h4.
assumption.
destruct h2.
destruct j2.
assumption.
destruct h4.
assumption.
Show Proof.
Qed.