import Data.Int
import Data.Foldable
import Data.Array                 as A
import Data.Array.Unboxed         as U
import Data.ByteString.Lazy.Char8 as B hiding (map, empty, foldr, reverse)

import System.IO
import System.IO.Unsafe
import System.Random

generateTest n = do
    file <- openFile "floyd.auto.in" WriteMode
    let printer   = printElem file n rnd
    hPrint file n
    mapM printer [(x,y) | x <- [1..n], y <- [1..n]]
    hClose file

rnd (i,j) = if i == j then 0 else (unsafePerformIO $ getStdRandom $ randomR (1,100)) :: Int

printElem handle n f i@(y,x) = do
    hPutStr handle $ show $ f i
    let suffix = if x == n then "\n" else " "
    hPutStr handle suffix
