
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type letter =
| A
| B

type word = letter list

type bar =
| Bar1 of word list
| Bar2 of word list * (word -> bar)

val prop1 : word list -> bar

val letter_eq_dec : letter -> letter -> sumbool

val prop2 :
  letter -> letter -> word list -> bar -> word list -> bar -> word list -> bar

val prop3 : letter -> word list -> bar -> word list -> bar

val higman : bar

val good_prefix_lemma : word list -> (nat -> word) -> bar -> word list

val good_prefix : (nat -> word) -> word list
