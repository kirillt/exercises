module Trader.Strategies where

import Prelude hiding (lookup)
import Data.Map

import Trader.Strategy
import Trader.Strategy.Naive

strategies :: Map String StrategyBox
strategies = fromList [("naive", naive)]

get :: String -> Maybe StrategyBox
get k = k `lookup` strategies
