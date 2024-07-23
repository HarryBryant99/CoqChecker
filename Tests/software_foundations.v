Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday tuesday).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
simpl.
reflexivity.
Qed.

Inductive bool : Type :=
  | true
  | false.
Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute andb true true.
Compute andb true false.
Compute orb false true.
Compute orb false false.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => (negb' b2)
  end.

Compute nandb true true.
Compute nandb false true.
Compute nandb true false.
Compute nandb false false.

Example test_nandb1: (nandb true false) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
simpl.
reflexivity.
Qed.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).
Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Compute isred (black : color).
Compute isred (primary green : color).

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=  negb' (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof.
reflexivity.
Qed.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint factorial (n: nat) :=
  match n with
    | O => 1
    | S n => S n * factorial n
  end.

Compute factorial 5.
Example test_factorial1: (factorial 3) = 6.
Proof.
simpl.
reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
simpl; reflexivity. 
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint lt (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => false
         | S m => true
         end
  | S n' => match m with
            | O => false
            | S m' => lt n' m'
            end
  end.

Compute negb'(leb 3 4).
Compute negb'(leb 4 4).
Compute negb'(leb 5 4).

Compute lt 3 4.
Example test_blt_nat1: (lt 2 2) = false.
Proof.
simpl; reflexivity. Qed.
Example test_blt_nat2: (lt 2 4) = true.
simpl; reflexivity. Qed.
Example test_blt_nat3: (lt 4 2) = false.
simpl; reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
intros n m h.
rewrite h.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros n m o h h1.
rewrite h.
rewrite h1.
reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_O_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
intros n m.
simpl.
intro h.
rewrite h.
reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  reflexivity.
  reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c.
destruct b.
destruct c.
simpl.
reflexivity.
simpl.
discriminate.
simpl.
discriminate.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
intros n.
destruct n.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
intros b.
destruct b.
intros c.
destruct c.
simpl.
reflexivity.
simpl.
discriminate.
intros c.
destruct c.
simpl.
discriminate.
reflexivity.
Qed.


Require Import ArithRing.
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
intros f c b.
rewrite c.
rewrite c.
reflexivity.
Qed.

