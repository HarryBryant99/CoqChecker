module Main( main ) where

import Lists
import Prelude

main = do
  let xs = Lists.List ["2","3","4","5","6"]
  print (hd xs)