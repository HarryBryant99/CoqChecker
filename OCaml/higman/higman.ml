
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

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

(** val prop1 : word list -> bar **)

let prop1 ws =
  Bar2 ((Cons (Nil, ws)), (fun w -> Bar1 (Cons (w, (Cons (Nil, ws))))))

(** val letter_eq_dec : letter -> letter -> sumbool **)

let letter_eq_dec a b =
  match a with
  | A -> (match b with
          | A -> Left
          | B -> Right)
  | B -> (match b with
          | A -> Right
          | B -> Left)

(** val prop2 :
    letter -> letter -> word list -> bar -> word list -> bar -> word list ->
    bar **)

let rec prop2 a b _ h ys x zs =
  match h with
  | Bar1 _ -> Bar2 (zs, (fun w -> Bar1 (Cons (w, zs))))
  | Bar2 (ws, b0) ->
    let rec f _ b1 zs0 =
      match b1 with
      | Bar1 _ -> Bar2 (zs0, (fun w -> Bar1 (Cons (w, zs0))))
      | Bar2 (ws0, b2) ->
        Bar2 (zs0, (fun w ->
          match w with
          | Nil -> prop1 zs0
          | Cons (a0, l) ->
            (match letter_eq_dec a0 a with
             | Left ->
               prop2 a b (Cons (l, ws)) (b0 l) ws0 (Bar2 (ws0, b2)) (Cons
                 ((Cons (a, l)), zs0))
             | Right -> f (Cons (l, ws0)) (b2 l) (Cons ((Cons (b, l)), zs0)))))
    in f ys x zs

(** val prop3 : letter -> word list -> bar -> word list -> bar **)

let rec prop3 a _ h zs =
  match h with
  | Bar1 _ -> Bar2 (zs, (fun w -> Bar1 (Cons (w, zs))))
  | Bar2 (ws, b) ->
    Bar2 (zs, (fun w ->
      let rec f = function
      | Nil -> prop1 zs
      | Cons (y, l0) ->
        (match letter_eq_dec y a with
         | Left -> prop3 a (Cons (l0, ws)) (b l0) (Cons ((Cons (a, l0)), zs))
         | Right ->
           prop2 y a (Cons (l0, zs)) (f l0) ws (Bar2 (ws, b)) (Cons ((Cons
             (y, l0)), zs)))
      in f w))

(** val higman : bar **)

let higman =
  Bar2 (Nil, (fun w ->
    let rec f = function
    | Nil -> prop1 Nil
    | Cons (y, l0) ->
      prop3 y (Cons (l0, Nil)) (f l0) (Cons ((Cons (y, l0)), Nil))
    in f w))

(** val good_prefix_lemma : word list -> (nat -> word) -> bar -> word list **)

let rec good_prefix_lemma _ f = function
| Bar1 ws -> ws
| Bar2 (ws, b) ->
  let w = f (length ws) in good_prefix_lemma (Cons (w, ws)) f (b w)

(** val good_prefix : (nat -> word) -> word list **)

let good_prefix f =
  good_prefix_lemma Nil f higman