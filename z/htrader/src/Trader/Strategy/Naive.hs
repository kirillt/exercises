module Trader.Strategy.Naive where

import Money.Rate
import Money.Money
import Money.Wallet
import Money.Quotations

import Trader.Strategy
import History.History

import Data.Map

import Debug.Trace

data State = Start | Previous (Map Pair Double)

naive :: StrategyBox
naive = Box base $ Ready strategy
    where
        base :: State
        base = Start

        strategy :: Exchanger -> Quotations -> State -> Wallet -> Action State
        strategy _ q1 Start         w = Action (Previous $ Money.Quotations.unpack q1) Wait
        strategy e q1 (Previous q0) w = Action (Previous $ Money.Quotations.unpack q1) $ Buy $ Data.Map.fromList $ Prelude.filter ((>0).snd) $ Prelude.map buy $ pairs q1
            where
                buy :: Pair -> (Pair,Double)
                buy p@(Pair f t) | w & f > 0 =
                    let (c0, c1) = (q0 ! p, q1 ? p)
                    in let diff = c1 / c0
                        in case trace (show diff) $ diff > 1.0005 of -- TODO: should choose f with maximum delta of (Pair f t_i) for every i
                        False -> (p,0)
                        True  -> (p, w & f)
