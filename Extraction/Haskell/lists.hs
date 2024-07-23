module Lists where

import qualified Prelude

data Bool =
   True
 | False

data List a =
   Nil
 | Cons a (List a)

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

data String =
   EmptyString
 | String0 Ascii0 String

hd :: String -> (List String) -> String
hd default0 l =
  case l of {
   Nil -> default0;
   Cons x _ -> x}

