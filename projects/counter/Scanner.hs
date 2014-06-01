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

scan :: String -> [String] -> IO [Entry]
scan file opts = do
  input <- readFile file
  either exit
    (return . map convert . toList)
    (decode NoHeader input)
  where
    convert :: Row -> Entry
    convert r@(t1,t2,d,mc,mr) =
      (timestamp t1 t2, d, money mc mr)

    timestamp t1 t2 | t1 /= t2 =
      unsafePerformIO $ exit "Timestamps don't match."
    timestamp t _ = read t :: UnixTime

    money mc _ = cur2cur (read mc) currency
      where
        currency :: Currency
        currency = fromMaybe RUR $ listToMaybe $
          map    (read      . fst) $
          filter ((== True) . snd)
          [ (c, c `elem` opts) |
             c <- currencies]

