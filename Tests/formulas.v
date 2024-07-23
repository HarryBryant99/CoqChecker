Check True.
Check False.
Check 3.
Check (3+4).
Check (3=5).
Check (3,4).
Check ((3=5)/\True).
Check nat -> Prop.
Check (3 <= 6).

Check (3,3=5):nat*Prop.

Check (fun x:nat => x = 3).
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).

Check (let f := fun x => (x * 3,x) in f 3).

Locate "_ <= _".

Check and.
Check (and True False).

Compute let f := fun x => (x * 3, x) in f 24930.


(*Exercise*)

Check fun a b c d e => a + b + c + d + e.
Compute (fun a b c d e => a + b + c + d + e) 1 2 3 4 5.

Definition h := fun a b c d e => a + b + c + d + e.
Compute h 1 2 3 4 5.