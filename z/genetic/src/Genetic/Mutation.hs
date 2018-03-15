module Genetic.Mutation (
    
    Mutable, Intensity
) where

import Data.Map
import Data.Functor
import System.Random
import Utils.NumberDecomposition

import Debug.Trace

newtype Intensity = Intensity { unpack :: Float } deriving (Eq, Ord, Show)

class Mutable a where
    mutations :: Map Intensity (a -> a)

mutate :: (Mutable a, RandomGen g) => g -> Intensity -> a -> (a, g)
mutate g i x = undefined
    where
        table :: Map Intensity [[Intensity]]
        table = int `mapKeys` (((int <$>) <$>) <$> ds)
            where
                int = Intensity . (* quantum) . fromIntegral
                ds  = decompositions n
                n   = round $ 1 / quantum

quantum :: Float
quantum = 0.0625

quantize :: Intensity -> Intensity
quantize (Intensity x) = Intensity $ quantum * charges x
    where
        charges intensity = fromIntegral $ (x1000 intensity) `div` (x1000 quantum)
        x1000 = round . (*1000)
