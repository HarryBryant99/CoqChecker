main = do
  putStrLn "List 1"
  xs <- getList []
  putStrLn "List 2"
  ys <- getList []
  print (xs ++ ys)
  
getList :: [String] -> IO [String]
getList list =  do line <- getLine
                   if line ==  ""
                      then return list
                      else getList (line : list)