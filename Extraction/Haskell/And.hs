module And where

import qualified Prelude

aandb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
aandb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

