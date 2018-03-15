{-# LANGUAGE ExistentialQuantification #-}

module Trader.Strategy where

import Money.Rate
import Money.Money
import Money.Wallet
import Money.Quotations
import History.History

import Data.Map

data Exchanger = Exchanger {
    fee :: Double
}

type Strategy s = Exchanger -> Quotations -> s -> Wallet -> Action s
data LearnableStrategy s = Ready (Strategy s)
                         | NeedLearning (History -> Strategy s)

data StrategyBox = forall s . Box s (LearnableStrategy s)

data Operation = Wait | Buy (Map Pair Double) deriving (Show,Eq)
data Action  s = Action s Operation

instance Show s => Show (Action s) where
    show (Action x op) = "{ operation: " ++ show op ++ "; state is " ++ show x ++ "}"
