module History where

import Text.ParserCombinators.Parsec
import Data.CSV

import System.Exit
import Data.Word

data Entry = Entry {
    time   :: Word32,
    price  :: Double,
    amount :: Double
} deriving (Show, Eq)

type History = [Entry]

--http://www.google.com/url?q=http://api.bitcoincharts.com/v1/csv/&usd=2&usg=ALhdy28dpsn3ZvJQYR07HJUqO-Gq130Krg
parseHistory :: IO History
parseHistory = do
    putStrLn "Parsing history file..."
    result <- parseFromFile csvFile "btce-usd.csv"
    case result of
        Left  error   -> do
            putStr "*** "
            print error
            exitFailure
        Right history -> do
            putStrLn "*** Done."
            return $ process history
            where
                process = map (\[t,p,a] -> Entry (read t) (read p) (read a))
