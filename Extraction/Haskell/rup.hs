module Rup where

import qualified Prelude

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False ->
    case b2 of {
     Prelude.True -> Prelude.False;
     Prelude.False -> Prelude.True}}

data Ascii0 =
   Ascii Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool Prelude.Bool 
 Prelude.Bool Prelude.Bool Prelude.Bool

eqb0 :: Ascii0 -> Ascii0 -> Prelude.Bool
eqb0 a b =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    case b of {
     Ascii b0 b1 b2 b3 b4 b5 b6 b7 ->
      case case case case case case case eqb a0 b0 of {
                                     Prelude.True -> eqb a1 b1;
                                     Prelude.False -> Prelude.False} of {
                                Prelude.True -> eqb a2 b2;
                                Prelude.False -> Prelude.False} of {
                           Prelude.True -> eqb a3 b3;
                           Prelude.False -> Prelude.False} of {
                      Prelude.True -> eqb a4 b4;
                      Prelude.False -> Prelude.False} of {
                 Prelude.True -> eqb a5 b5;
                 Prelude.False -> Prelude.False} of {
            Prelude.True -> eqb a6 b6;
            Prelude.False -> Prelude.False} of {
       Prelude.True -> eqb a7 b7;
       Prelude.False -> Prelude.False}}}

data String =
   EmptyString
 | String0 Ascii0 String

append :: String -> String -> String
append s1 s2 =
  case s1 of {
   EmptyString -> s2;
   String0 c s1' -> String0 c (append s1' s2)}

eqb1 :: String -> String -> Prelude.Bool
eqb1 s1 s2 =
  case s1 of {
   EmptyString ->
    case s2 of {
     EmptyString -> Prelude.True;
     String0 _ _ -> Prelude.False};
   String0 c1 s1' ->
    case s2 of {
     EmptyString -> Prelude.False;
     String0 c2 s2' -> (Prelude.&&) (eqb0 c1 c2) (eqb1 s1' s2')}}

data List =
   Nil
 | Cons String List

already :: String -> List -> Prelude.Bool
already n l =
  case l of {
   Nil -> Prelude.False;
   Cons a tl ->
    let {r = already n tl} in
    case eqb1 n a of {
     Prelude.True -> Prelude.True;
     Prelude.False -> r}}

app :: List -> List -> List
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

app_unique :: List -> List -> List
app_unique l m =
  case l of {
   Nil -> m;
   Cons a l1 ->
    case already a m of {
     Prelude.True -> app_unique l1 m;
     Prelude.False -> Cons a (app_unique l1 m)}}

rup :: String -> List -> List
rup n l =
  case l of {
   Nil -> Nil;
   Cons a tl ->
    let {r = rup n tl} in
    case eqb1
           (append (String0 (Ascii Prelude.True Prelude.False Prelude.False
             Prelude.False Prelude.False Prelude.True Prelude.False
             Prelude.False) EmptyString) a) n of {
     Prelude.True -> r;
     Prelude.False ->
      case eqb1
             (append (String0 (Ascii Prelude.True Prelude.False Prelude.False
               Prelude.False Prelude.False Prelude.True Prelude.False
               Prelude.False) EmptyString) n) a of {
       Prelude.True -> r;
       Prelude.False -> app (Cons a Nil) r}}}

loop :: List -> List -> List
loop l n =
  case l of {
   Nil -> n;
   Cons a tl -> loop tl (rup a n)}

clause :: List -> List -> List
clause b1 b2 =
  app_unique (loop b1 b2) (loop b2 b1)

