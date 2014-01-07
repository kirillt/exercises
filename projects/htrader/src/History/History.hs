{-# LANGUAGE MultiParamTypeClasses #-}

module History.History where

import Prelude hiding (readFile, writeFile)

import Data.Csv             as Cassava
import Data.Word
import Data.Maybe
import Data.Serialize       as Cereal
import Data.Vector                    (Vector, toList)
import Data.ByteString      as Strict (readFile, writeFile)
import Data.ByteString.Lazy as Lazy   (readFile)

import System.Exit
import System.Directory
import Control.Applicative

import Time.Time
import Utils.Range
import Utils.Tuple
import Utils.FileName
import Money.Money

data Entry = Entry {
    time   :: UnixTime,
    price  :: Price,
    amount :: Double
} deriving (Show, Eq)

instance Tuple3 Entry Word32 Double Double where
    toTuple3 (Entry (UnixTime t) b2u a) = (t, b2u, a)
    fromTuple3 (t, b2u, a) = Entry (UnixTime t) b2u a

instance Serialize Entry where
    put e = put (toTuple3 e :: (Word32, Double, Double))
    get   = (fromTuple3 :: (Word32, Double, Double) -> Entry) <$> get

newtype History = History {
    entries :: [Entry]
} deriving (Show, Eq)

extract :: History -> Range UnixTime -> History
extract (History h) (Range low high) = History $ takeWhile (earlier high) $ dropWhile (earlier low) h
    where
        earlier :: UnixTime -> Entry -> Bool
        earlier b = (<b) . time

--http://api.bitcoincharts.com/v1/csv/btceUSD.csv

prefix :: FilePath
prefix = "../data/"

getHistoryAll :: IO History
getHistoryAll = do
    cached <- recallAll
    case cached of
        Just h  -> return h
        Nothing -> do
            input <- Lazy.readFile $ prefix ++ "btce-usd.csv"
            let result = Cassava.decode False input :: Either String (Vector (Word32,Double,Double))
            case result of
                Left error -> do
                    print error
                    exitFailure
                Right entries -> do
                    let history = History $ map fromTuple3 $ toList entries
                    memoizeAll history
                    return history

memoizeAll :: History -> IO ()
memoizeAll = memoize $ prefix ++ "btce-usd.bin"

recallAll :: IO (Maybe History)
recallAll  = recall  $ prefix ++ "btce-usd.bin"

getHistoryRange :: Range UnixTime -> IO History
getHistoryRange r = do
    cached <- recallRange r
    case cached of
        Just  h -> return h
        Nothing -> do
            all <- getHistoryAll
            let h = extract all r
            memoizeRange r h
            return h

memoizeRange :: Range UnixTime -> History -> IO ()
memoizeRange r = memoize $ prefix ++ toFileName r

recallRange :: Range UnixTime -> IO (Maybe History)
recallRange  r = do
    fs <- getDirectoryContents prefix
    let rs = map fromJust $ filter isJust $ map fromFileName fs :: [Range UnixTime]
    let r' = minimum $ r:(filter (`contain` r) rs)
    result <- recall $ prefix ++ toFileName r'
    case (result, r == r') of
        (Nothing, _    ) -> return Nothing
        (Just h', False) -> do
            let h = extract h' r
            memoizeRange r h
            return $ Just h
        (Just h', True ) -> do
            return result

memoize :: FilePath -> History -> IO ()
memoize f h = do
    let binary = Cereal.encode $ entries h
    writeFile f binary

recall  :: FilePath -> IO (Maybe History)
recall  f = do
    cached <- doesFileExist f
    case cached of
        False -> return Nothing
        True  -> do
            binary <- Strict.readFile f
            let result = Cereal.decode binary
            case result of
                Left error -> do
                    print error
                    exitFailure
                Right entries -> do
                    return $ Just $ History entries
