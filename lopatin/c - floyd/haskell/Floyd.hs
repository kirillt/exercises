{-# LANGUAGE BangPatterns #-}

import System.IO

import Data.Word
import Data.Maybe
import Data.Foldable
import Data.Array.Unboxed
import Data.ByteString.Lazy.Char8 as B hiding (zip, map, empty, foldl', reverse)

main = do
    input               <- B.readFile "floyd.in"
    let Just (n,input') =  readNum      input
    file <- openFile "floyd.out" WriteMode
    printMatrix file n 1 $ forMatrix (improve n) (readMatrix n input') (forIndices n)
    hClose file

printMatrix :: Handle -> Word16 -> Word16 -> Matrix -> IO ()
printMatrix file n i !matrix = do
    hPutStr file $ show $ matrix ! i
    if i == n2
        then return ()
        else do
            let suffix = if i `mod` n == 0 then "\n" else " "
            hPutStr file suffix
            printMatrix file n (i+1) matrix
    where
        n2 = n^2

forIndices n = [ (k,i,j) | k<-[1..n], i<-[1..n], j<-[1..n] ]
forMatrix  f matrix is = foldl' f matrix is

{-# INLINE improve #-}
improve :: Word16 -> Matrix -> (Word16,Word16,Word16) -> Matrix
improve n !matrix (k,i,j) =
    if ikjV < ijV
        then matrix // [(ij, ikjV)]
        else matrix
    where
        (!!!) = rowColumn n
        ij    = i !!! j
        ikV   = matrix ! (i !!! k)
        kjV   = matrix ! (k !!! j)
        ijV   = matrix ! ij
        ikjV  = ikV + kjV

type Matrix = UArray Word16 Word16

newMatrix :: Word16 -> Matrix
newMatrix n     = array (1, n^2) []

{-# INLINE rowColumn #-}
rowColumn n r c = (r-1)*n + c

readMatrix :: Word16 -> ByteString -> Matrix
readMatrix n source = fst $ fromJust $ readMatrix' n2 (newMatrix n) source
    where
        n2 = n^2
        readMatrix'  0 !matrix source = return (matrix, source)
        readMatrix' !k !matrix source = do
            (next, source) <- readNum source
            readMatrix' (k-1) (matrix // [(n2-k+1,next)]) source

readNum :: ByteString -> Maybe (Word16, ByteString)
readNum source = fmap convert $ readInt source
    where
        convert (a,b) = (fromIntegral a, trim b)
        trim source = case B.uncons source of
            Just (c, trimmed) | c == '\n' || c == '\r' || c == ' '
                -> trim trimmed
            _   -> source
