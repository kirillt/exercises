type Matrix a = [[a]]

identity :: Integer -> Matrix Integer
identity n = [ map (\j -> if i == j then 1 else 0) [1..n] | i <- [1..n] ]
