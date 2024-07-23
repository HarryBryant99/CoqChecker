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

(* Define a function to switch the state of a point *)
Definition switch_point (p : Point) : Point :=
  match p with
  | NormalPoint => ReversePoint
  | ReversePoint => NormalPoint
  end.

(* Define an instance of a point *)
Definition point1 : Point := NormalPoint.

(* Define another instance of a point *)
Definition another_point : Point := ReversePoint.

(* Compute the result of switching the state of example_point *)
Compute switch_point point1.

(*
CodeGen Gen switch_point.
*)

Require Coq.extraction.Extraction.

(* Use the Extraction command to generate OCaml code *)
Extraction Language OCaml.
Extraction "C:\Users\z004u5bh\Documents\Coq\OCaml\points.ml" switch_point.