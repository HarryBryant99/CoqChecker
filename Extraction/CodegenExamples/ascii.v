Require Import codegen.codegen.

Require Import Bool BinPos BinNat PeanoNat Nnat Coq.Strings.Byte.
Import IfNotations.

Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool).

Declare Scope char_scope.
Delimit Scope char_scope with char.
Bind Scope char_scope with ascii.

Register ascii as core.ascii.type.
Register Ascii as core.ascii.ascii.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

Definition zero := Ascii false false false false false false false false.

Definition one := Ascii true false false false false false false false.

Definition shift (c : bool) (a : ascii) :=
  match a with
    | Ascii a1 a2 a3 a4 a5 a6 a7 a8 => Ascii c a1 a2 a3 a4 a5 a6 a7
  end.

Definition ascii_dec : forall a b : ascii, {a = b} + {a <> b}.

Local Open Scope lazy_bool_scope.

Definition chareqb (a b : ascii) : bool :=
 match a, b with
 | Ascii a0 a1 a2 a3 a4 a5 a6 a7,
   Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
    Bool.eqb a0 b0 &&& Bool.eqb a1 b1 &&& Bool.eqb a2 b2 &&& Bool.eqb a3 b3
    &&& Bool.eqb a4 b4 &&& Bool.eqb a5 b5 &&& Bool.eqb a6 b6 &&& Bool.eqb a7 b7
 end.

Infix "=?" := chareqb : char_scope.

CodeGen SourceFile "ascii.c".
CodeGen StaticFunc chareqb.

CodeGen GenerateFile.