(*https://softwarefoundations.cis.upenn.edu/lf-current/Extraction.html*)

Require Coq.extraction.Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
(*From LF Require Import ImpCEvalFun.*)

Extraction "imp1.ml" ceval_step.