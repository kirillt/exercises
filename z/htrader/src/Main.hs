import System.Environment
import Debug.Trace

import Utils.Range
import Time.Time

import Money.Rate
import Money.Money
import Money.Quotations
import Trader.Trader
import Trader.Strategy
import Trader.Strategies
import History.History

import Data.Map (fromList)

main = do
    args@(mode:wallet:strategy:params) <- getArgs
    debug $ "Arguments: " ++ show args
    let w = read wallet
    debug $ "Wallet:    " ++ show w
    case get strategy of
        Nothing -> do
            putStrLn $ "Can't find strategy " ++ strategy ++ "." 
        Just (Box x s)  -> do
            debug $ "Strategy:  " ++ strategy
            (s', params') <- learn s params
            case mode of
                "simulate" -> do
                    let [range] = params'
                    let r = read range
                    debug $ "RangeS:    " ++ show r
                    h <- getHistoryRange r
                    debug $ "Running simulation."
                    simulate btce s' (map quote $ entries h) x w
                "realtime" -> do
                    let [] = params
                    realtime btce s' x w

learn :: LearnableStrategy s -> [String] -> IO (Strategy s, [String])
learn (Ready        s) params = return (s,params)
learn (NeedLearning s) params = do
    debug $ "Performing learning."
    let (range:params') = params
    let r = read range
    debug $ "RangeL:    " ++ show r
    h <- getHistoryRange r
    return (s h, params')

debug m = trace m $ return ()

btce  :: Exchanger
btce  = Exchanger 0.002

quote :: Entry -> Quotations
quote (Entry _ v _) = Quotations $ fromList [(btc2usd,v),(usd2btc,(1/v)*(1-0.0025))]
