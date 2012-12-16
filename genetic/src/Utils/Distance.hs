module Utils.Distance (distance) where

import Data.Map

type Arg = (Int,Int)

distance :: Eq a => [a] -> [a] -> Int
distance xs ys = cache ! query
    where
        query :: Arg
        query@(n,m) = (length xs, length ys)

        cache :: Map Arg Int
        cache = fromList [((i,j), distance' i j) | i <- [0..n], j <- [0..m]]

        distance' :: Int -> Int -> Int
        distance' i j | i == 0 = j
                      | j == 0 = i
                      | True   = let e = eq i j
                                 in  minimum [
                                     1 + cache ! ((i-1), j   )
                                   , 1 + cache ! ( i   ,(j-1))
                                   , e + cache ! ((i-1),(j-1))
                                 ]

        eq :: Int -> Int -> Int
        eq i j = if (xs !! (i-1)) == (ys !! (j-1))
                 then 0 else 1
