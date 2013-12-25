{-# OPTIONS_GHC -O -Wall #-}

module HReal.Core.History where

import HReal.Core.World

type History = [(String,World)]

wrap  :: (World -> a) -> History -> a
wrap f = f . snd . head

clean :: History
clean  = [("()",zero)]
