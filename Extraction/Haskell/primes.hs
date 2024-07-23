module Main( main ) where

import PrimesCoq
import Prelude

main = do
    if ((isPrime 43) == True)
    then
        print "Prime"
    else
        print "Non Prime"