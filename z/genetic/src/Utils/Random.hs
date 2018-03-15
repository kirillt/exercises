{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE UndecidableInstances #-}

module Utils.Random where

import System.Random

instance (Random a, Ord a, Bounded a, Bounded [a]) => Random [a] where
    random            = randomR (minBound,maxBound)
    randomR (ls,rs) g = let ls'    = min ls rs
                            rs'    = max ls rs
                            d      = length rs' - length ls'
                            ls''   = map Just ls' ++ replicate d Nothing
                        in foldr rand ([],g) $ zip ls'' rs'
                        -- Workaround (proper instances requires proper Enum instance for []),
                        -- which isn't possible since Enum operates with Int instead of Integer.
                        -- I'm not sure, that distribution is correct.
        where
            rand (Nothing,r) (xs,g) = case random g of
                                          (True ,g') -> rand' (minBound,r) (xs,g') 
                                          (False,g') -> (xs,g')
            rand  (Just l,r) rest   = rand' (l,r) rest
            rand' bounds (xs,g) = let (x   ,g') = randomR bounds g
                                  in  (x:xs,g')
