{-# OPTIONS_GHC -O -Wall #-}

module Utils.NumberDecomposition where

import Data.Map

decompositions :: Int -> Map Int [[Int]]
decompositions n = cache
    where
        args        = [2..n]
        base        = (1, [[1]])
        cache       = fromList $ base:[entry x | x <- args]

        entry x     = (x, decompose x)
        decompose x = [x]:concat [ith i x | i <- [1..(x-1)]]
        ith i     x = [(x-i):d | d <- cache ! i]
