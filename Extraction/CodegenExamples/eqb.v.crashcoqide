Require Import codegen.codegen.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

(*uses Inductive String, Inductive Ascii.
  doesn't use indimp
  requires the ascii datatype to be defined as per strings/compare.c
*)

Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool).

(*
Require Import Ascii.

CodeGen InductiveType ascii => "unsigned char".
CodeGen Primitive Ascii => "make_char".
*)

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Definition isEmpty (str body1 body2 :string) :=
match str with
  | EmptyString => body1
  | String ch rest => body2
  end.

CodeGen Gen isEmpty.

Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.

(*CodeGen Gen string_dec.*)

Definition bool_eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Definition ascii_eqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    bool_eqb a0 b0 && bool_eqb a1 b1 && bool_eqb a2 b2 && bool_eqb a3 b3
    && bool_eqb a4 b4 && bool_eqb a5 b5 && bool_eqb a6 b6 && bool_eqb a7 b7
 end.


(*CodeGen Gen ascii_eqb.*)


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(*CodeGen Gen andb.*)

Fixpoint compare s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' => ascii_eqb c1 c2 && compare s1' s2'
 | _,_ => false
 end.

(*
CodeGen Gen compare ascii_eqb bool_eqb.
*)

CodeGen SourceFile "strings/equal.c".
(*CodeGen IndImp string.*)
(*CodeGen IndImp ascii.*)
CodeGen StaticFunc compare.
CodeGen GenerateFile.