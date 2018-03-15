module Trader.Trader where

import Control.Monad.Identity
import Data.Map (toList, fromList)

import Money.Rate
import Money.Money
import Money.Wallet
import Money.Quotations
import Trader.Strategy

import Time.Time

realtime :: Exchanger -> Strategy x                 -> x -> Wallet -> IO ()
realtime e s    x w = undefined

simulate :: Exchanger -> Strategy x -> [Quotations] -> x -> Wallet -> IO ()
simulate e s qs x w = run qs x w
    where
        fee = Trader.Strategy.fee e
        decide q x w = s e q x w

        run (q:qs) x w = do
            case decide q x w of
                Action x' (Buy m) -> do
                    w' <- buyAll (Data.Map.toList m) w
                    run qs x' w'
                Action x' Wait -> run qs x' w
                where
                    buyAll :: [(Pair,Double)] -> Wallet -> IO Wallet
                    buyAll []     w = return w
                    buyAll (m:ms) w = do
                        w' <- buy m w
                        buyAll ms w'

                    buy :: (Pair,Double) -> Wallet -> IO Wallet
                    buy m@(Pair f t, b) w = do
                        let b' = b * (1 + fee)
                        putStrLn $ "Buying " ++ show m ++ " + fee = " ++ show (Money t b')
                        let p  = q ? (Pair f t)
                        let v  = w & f
                        let cost = b' * p
                        let v' = v - (b' * p)
                        if v' >= 0
                            then do
                                let b'' = (w & t) + b'
                                let w' = w $$ Money f v' $$ Money t b''
                                putStrLn $ "Now have " ++ show w'
                                return w'
                            else fail $ "Lack of funds: trying to buy " ++ show m
                                        ++ " which costs " ++ show cost ++ " " ++ show f
                                        ++ " but have only " ++ show (Money f v)
                                        ++ "."

        run [] _ w = return ()

cost :: Quotations -> (Pair, Double) -> Money
cost q (p@(Pair f t), n) = Money f $ n * q ? p
