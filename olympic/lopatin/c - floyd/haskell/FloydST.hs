{-# GHC_OPTIONS -O2 -Wall #-}
{-# LANGUAGE BangPatterns #-}

import System.IO

import Data.Word
import Data.Char (ord)
import Data.Array.Unboxed
import Data.Array.ST
import Data.ByteString.Lazy (ByteString)
import Control.Monad (when,forM_)
import Control.Monad.ST
import qualified Data.ByteString.Lazy.Char8 as SL8 
import qualified Data.ByteString.Lazy as SL

type Matrix = UArray Word16 Word16

main :: IO ()
main = do
    lazyData <- SL.readFile "floyd.in"
    let dat = (map b2w $ SL8.words lazyData) :: [Word16] -- we are tricky ^_^
        n   = head dat
        matrixData = tail dat
        mt  = runSTUArray $ do
                matrix <- newListArray (1, n*n) matrixData :: ST s (STUArray s Word16 Word16)
                forM_ [(k,i,j) | k<-[1..n], i<-[1..n], j<-[1..n]] $! \(k,i,j) -> do
                      ikV  <- readArray matrix (i!!!k)
                      kjV  <- readArray matrix (k!!!j)
                      ijV  <- readArray matrix (i!!!j)
                      let   ikjV = ikV + kjV
                      when (ikjV < ijV) $! writeArray matrix (i!!!j) ikjV
                return matrix
                where
                  a !!! b = (a-1)*n+b
    file <- openFile "floyd.out" WriteMode
    printMatrix file n 1 mt
    hClose file


b2w :: ByteString -> Word16
b2w = SL8.foldl' (\a n -> a*10+(fromIntegral $! (ord n)-48)) 0  
              -- (c * 10 +) . fromIntegral . subtract 48 . ord  -- point free rules ^_^

printMatrix :: Handle -> Word16 -> Word16 -> Matrix -> IO ()
printMatrix file n i matrix = do
    hPutStr file $ show $ matrix ! i
    if i == n2
        then return ()
        else do
            let suffix = if i `mod` n == 0 then "\n" else " "
            hPutStr file suffix
            printMatrix file n (i+1) matrix
    where
        n2 = n*n
