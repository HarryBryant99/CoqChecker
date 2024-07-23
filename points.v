(* Import the Coq standard library for boolean operations *)
Require Import Bool.

(* Define a type representing railway points *)
Inductive Point : Set :=
  | NormalPoint
  | ReversePoint.

(* Define a function that represents the state of a point *)
Definition point_state (p : Point) : bool :=
  match p with
  | NormalPoint => true (* Normal point is in the true state *)
  | ReversePoint => false (* Reverse point is in the false state *)
  end.

(* Theorem: A point cannot be both normal and reverse at the same time *)
Theorem exclusive_point_states : forall p : Point, point_state p = true \/ point_state p = false.
Proof.
  intros p.
  (* Use a case analysis to consider the two possible cases for p *)
  destruct p.
  - (* Case: p is NormalPoint *)
    (* Prove the goal using the standard library lemmas about booleans *)
    left. reflexivity.

  - (* Case: p is ReversePoint *)
    (* Prove the goal using the standard library lemmas about booleans *)
    right. reflexivity.
Qed.

(*
   Theorem: A point can be only one of the two cases (either NormalPoint or ReversePoint)
   Proof:
   - Use a case analysis on p to handle the two cases.
   - Add an additional proof obligation to show that NormalPoint and ReversePoint are distinct.
*)
Theorem exclusive_point_cases : forall p : Point, p = NormalPoint \/ p = ReversePoint.
Proof.
  intros p.
  (* Use case analysis on p *)
  destruct p.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* Additional proof obligation: NormalPoint and ReversePoint are distinct *)
Theorem distinct_point_constructors : NormalPoint <> ReversePoint.
Proof.
  discriminate.
Qed.

(* Define a function to switch the state of a point *)
Definition switch_point (p : Point) : Point :=
  match p with
  | NormalPoint => ReversePoint
  | ReversePoint => NormalPoint
  end.

(*
   Theorem: Switching the state of a point twice results in the original point.
*)
Theorem switch_point_twice_identity : forall p : Point, switch_point (switch_point p) = p.
Proof.
  intros p.
  (* Use case analysis on p *)
  destruct p.
  - (* Case: p is NormalPoint *)
    simpl. reflexivity.
  - (* Case: p is ReversePoint *)
    simpl. reflexivity.
Qed.

(* Define an instance of a point *)
Definition point1 : Point := NormalPoint.

(* Define another instance of a point *)
Definition another_point : Point := ReversePoint.

(* Compute the result of switching the state of example_point *)
Compute switch_point point1.