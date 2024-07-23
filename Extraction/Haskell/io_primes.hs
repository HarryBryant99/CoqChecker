module Main( main ) where

import PrimesCoq
import Prelude

main = do
   putStrLn "Enter an integer: "
   input <- getLine
   let number = read input :: Integer
   putStrLn ("You entered: " ++ show number)
   
   if ((isPrime number) == True)
    then
        print "Prime"
    else
        print "Non Prime"