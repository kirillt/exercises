module Scanner where

import Money
import Common
import Time.Time

import Data.Maybe
import System.Exit
import System.IO.Unsafe

import Data.Csv as Cassava (decode, HasHeader(NoHeader))
import Data.Vector    (Vector, toList)
import Data.ByteString.Lazy (readFile)
import Prelude       hiding (readFile)

exit msg = do
  putStrLn $ "Exit: " ++ msg
  exitFailure

type Row = (String,String,String,String,String)

scan :: [String] -> String -> IO [Entry]
scan opts file = do
  input <- readFile file
  either exit
    (return . map convert . toList)
    (decode NoHeader input)
  where
    convert :: Row -> Entry
    convert (t1,t2,d,mc,mn) =
      (timestamp t1 t2, d, money mc mn)

    timestamp :: String -> String -> UnixTime
    timestamp t _ = read t

    money :: String -> String -> Money
    money mc mn = withSign $ cur2cur (read mc) currency
      where
        sign :: Double
        sign = signum (read mn :: Double)

        withSign :: Money -> Money
        withSign (Money c n) = Money c $ n * sign

        currency :: Currency
        currency = fromMaybe RUR $ listToMaybe $
          map    (read      . fst) $
          filter ((== True) . snd)
          [ (c, c `elem` opts) |
             c <- currencies]

