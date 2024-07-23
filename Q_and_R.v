From Coq Require Import Arith Utf8 Psatz
  Peano NArith.

Fixpoint monika_proof (a : nat) : forall b, 
    0 < b -> {'(q, r) : nat * nat | a = q * b + r /\ 0 <= r < b}.
  Proof.
    induction a as [|a Iha].
    +
      intros * Ha.
      exists (0, 0).
      nia.
    +
      intros * Ha.
      destruct (monika_proof a b Ha) as ((q, r) & (Hb & Hc)).
      destruct ((1 + r <? b)) eqn:Hd.
      ++
        exists (q, 1 + r).
        split; try nia. 
        eapply Nat.ltb_lt in Hd.
        nia.
      ++
        exists (1 + q, 0).
        split; try nia.
        simpl.
        eapply Nat.ltb_ge in Hd.
        assert (b = 1 + r). nia.
        subst. nia.
  Defined.