Require Import String.

Add LoadPath "/mnt/c/Users/z004u5bh/Documents/Coq/Inductive/" as Inductive.
From Inductive Require CNFOp.

Definition literal_eq (l1 l2 : CNFOp.literal) : bool :=
  match l1, l2 with
  | CNFOp.pos s1, CNFOp.pos s2 | CNFOp.neg s1, CNFOp.neg s2 =>
    match string_dec s1 s2 with
    | left _ => true
    | right _ => false
    end
  | _, _ => false
  end.


(* Equality check for clauses *)
Fixpoint clause_eq (c1 c2 : CNFOp.clause) : bool :=
  match c1, c2 with
  | CNFOp.nilclause, CNFOp.nilclause => true
  | CNFOp.consclause l1 ls1, CNFOp.consclause l2 ls2 =>
    if literal_eq l1 l2 then clause_eq ls1 ls2 else false
  | _, _ => false
  end.

(* Membership for a literal in a clause of literals *)
Fixpoint memcl (l : CNFOp.literal) (c : CNFOp.clause) : bool :=
  match c with
  | CNFOp.nilclause => false
  | CNFOp.consclause l2 ls => if literal_eq l l2 then true else memcl l ls
  end.

(* Membership for a clause in a formula *)
Fixpoint memcf (c : CNFOp.clause) (f : CNFOp.formula) : bool :=
  match f with
  | CNFOp.nilformula => false
  | CNFOp.consformula c2 cs => if clause_eq c c2 then true else memcf c cs
  end.

(* Example usage: *)
Compute (memcl (CNFOp.pos "p") (CNFOp.consclause (CNFOp.pos "q") (CNFOp.consclause (CNFOp.neg "r") CNFOp.nilclause))).
(* This should return false. *)

Compute (memcf (CNFOp.consclause (CNFOp.pos "p") (CNFOp.consclause (CNFOp.neg "q") CNFOp.nilclause))
               (CNFOp.consformula (CNFOp.consclause (CNFOp.pos "p") CNFOp.nilclause)
                             (CNFOp.consformula (CNFOp.consclause (CNFOp.neg "r") CNFOp.nilclause) CNFOp.nilformula))).
(* This should return false. *)


(*------------------------------------------------------------------*)
(*Proofs*)
(* - need to do -
memit-lemma
memlemma6
mem-singleton
*)

Lemma mem_lemma : forall (f : CNFOp.formula) (c1 c : CNFOp.clause),
  memcf c (CNFOp.remcf c1 f) -> memcf c f.
Proof.
  intros f c1 c Hmem.
  induction f as [|c2 f' IH] using CNFOp.formula_ind.
  - (* Base case: Empty formula *)
    simpl in Hmem. assumption.
  - (* Inductive step: Non-empty formula *)
    simpl in Hmem.
    destruct (clause_eqb c1 c2) eqn:Heq1.
    + (* c1 = c2 *)
      destruct (clause_eqb c c2) eqn:Heq2.
      * (* c = c2 *)
        apply IH in Hmem. simpl. rewrite Heq1, Heq2. assumption.
      * (* c <> c2 *)
        simpl. right. apply IH in Hmem. assumption.
    + (* c1 <> c2 *)
      simpl. right. apply IH in Hmem. assumption.
Qed.



