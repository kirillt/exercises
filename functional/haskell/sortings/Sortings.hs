{-# LANGUAGE ImpredicativeTypes #-}

import Data.Traversable

main = for sortings $ \(s,f) -> do
         putStrLn $ "Testing '" ++ s ++ "':"
         for cases $ \c -> do
           let c' = f c
           putStrLn $ "\t"
             ++ show c ++ " -> " ++ show c'
             ++ " " ++ if check c' then "GOOD" else "BAD"

check :: Ord a => [a] -> Bool
check xs = all (uncurry (<=)) $ zip xs $ safetail xs
  where
    safetail [] = []
    safetail xs = tail xs

cases :: [[Integer]]
cases = [[],
         [1],
         [2,1],
         [3,2,1],
         [2,3,1],
         [2,2,1],
         [1,1,1],
         [4,3,2,1]]

type Sorting = forall a . Ord a => [a] -> [a]

sortings :: [(String, Sorting)]
sortings = [("mergesort", mergesort)]

mergesort :: Sorting
mergesort []  = []
mergesort [z] = [z]
mergesort zs  = let (xs,ys) = split zs
                in merge (mergesort xs) (mergesort ys)
  where
    merge [] ys = ys
    merge xs [] = xs
    merge xs@(x:xt) ys@(y:yt) = if x <= y then x : merge xt ys else y : merge xs yt

    split :: [a] -> ([a],[a])
    split = foldr (\z (xs,ys) -> (z:ys,xs)) ([],[])
