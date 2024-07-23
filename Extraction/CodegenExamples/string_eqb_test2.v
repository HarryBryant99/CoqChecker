Require Import codegen.codegen.


Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Import IfNotations.

(** *** Definition of strings *)

(** Implementation of string as list of ascii characters *)

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Declare Scope string_scope.
Delimit Scope string_scope with string.
Bind Scope string_scope with string.
Local Open Scope string_scope.

Register string as core.string.type.
Register EmptyString as core.string.empty.
Register String as core.string.string.

(** Equality is decidable *)

Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.

Local Open Scope lazy_bool_scope.

Fixpoint eqb1 s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => Ascii.eqb c1 c2 &&& eqb1 s1' s2'
 | _,_ => false
 end.

Infix "=?" := eqb1 : string_scope.

CodeGen Gen eqb1.