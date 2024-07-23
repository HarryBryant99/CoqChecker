module Main( main ) where

import And
import Prelude

main = do
   print (aandb False False)
   print (aandb False True)
   print (aandb True False)
   print (aandb True True)