import My_add

a :: My_add.Nat
a = 3

intToString :: My_add.Nat -> String
intToString n = show n

main = do
    putStrLn "Printing"
    putStrLn(intToString (My_add.my_add a a))