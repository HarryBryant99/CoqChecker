module Main( main ) where

import Prelude

main = do
  let list = [2,3,4,5,6]
  print(rev list) 
 
rev :: [a] -> [a]
rev x = reverse(reverse x)