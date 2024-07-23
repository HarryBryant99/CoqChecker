(* Import necessary libraries *)
Require Import PeanoNat.

(* Define a data type for signals *)
Inductive Signal : Set :=
  | Red
  | Green.

(* Define a function to switch a signal *)
Definition switch_signal (signal : Signal) : Signal :=
  match signal with
  | Red => Green
  | Green => Red
  end.

(* Theorem: If one signal is red, the other must be green, and vice versa *)
Theorem alternate_signals : forall signal1 signal2 : Signal,
  signal1 = Red -> signal2 = Green \/ signal2 = Red.
Proof.
  intros signal1 signal2 H1.
  destruct signal2; auto.
Qed.

(* Theorem: Both signals cannot be green simultaneously *)
Theorem no_both_green : forall signal1 signal2 : Signal,
  signal1 = Green -> signal2 = Green -> False.
Proof.
  intros signal1 signal2 H1 H2.
  inversion H1; inversion H2; subst.
Qed.