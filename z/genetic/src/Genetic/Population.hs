{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Genetic.Population where

import Genetic.Individ

type Population = [Individ]

instance Bounded Population where
    minBound = replicate 16 minBound
    maxBound = replicate 64 maxBound
