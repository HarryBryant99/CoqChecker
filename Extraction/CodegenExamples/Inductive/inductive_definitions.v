Inductive bin : Type :=
L : bin
| N : bin -> bin -> bin.

Check bin.

Check N L (N L L).

Check N L L.

Inductive tree3 : Type :=
tree3_c
| tree3_3 (n : nat) (t1 t2 : tree3)
| tree3_4 (b : bool) (t1 t2 t3 : tree3).

Check tree3.

Check tree3_c.

Check tree3_3.

(*
Check true (tree3_c tree3_c tree3_c).
*)

