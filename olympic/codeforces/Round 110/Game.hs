{-# LANGUAGE BangPatterns #-}

import System.IO
import System.IO.Unsafe
import Unsafe.Coerce

import Data.Word
import Data.List                        hiding (concat)
import Data.Foldable                    hiding (concat, sum)
import Data.Array.Unboxed
import Data.ByteString.Lazy       as B  hiding (putStr, map, reverse, concat, length, filter, null)
import Data.ByteString.Lazy.Char8 as BC hiding (putStr, map, reverse, concat, length, filter, null)

w8to16 :: Word8 -> Word16
w8to16   = unsafeCoerce
square :: Word8 -> Word16
square x = w8to16 x^2

main = do
    hSetBuffering stdin LineBuffering
    first          <- fmap BC.pack   System.IO.getLine
    let Just (n,_) =  readNum first
    second         <- fmap (BC.pack . (\(' ':s) -> s) . concat . (map (' ':))) $ mapM (\_ -> getLine) [1..n]
    let Just (m,_) =  readMatrix n second
    print $ length $ filter (==True) $ map2 (wins m n) [1..n] [1..n]

map2 f xs ys = concat $ map (\y -> map (f y) xs) ys

printMatrix :: Word8 -> Word16 -> Matrix -> IO ()
printMatrix n i matrix = do
    putStr $ show $ matrix ! i
    if i == n2
        then return ()
        else do
            let suffix = if i `mod` n' == 0 then "\n" else " "
            putStr suffix
            printMatrix n (i+1) matrix
    where 
        n' = w8to16 n
        n2 = square n

wins :: Matrix -> Word8 -> Word8 -> Word8 -> Bool
wins m n r c = (not $ null $ lineV) && (not $ null $ lineH) && sum lineV > sum lineH
    where (!!!) = rowColumn n
          lineH = map (\i -> m ! (r !!! i)) $ [1..c-1]++[c+1..n]
          lineV = map (\j -> m ! (j !!! c)) $ [1..r-1]++[r+1..n]

type Matrix = UArray Word16 Word8

newMatrix :: Word8 -> Matrix
newMatrix n     = array (1, square n) []
rowColumn n r c =
    if r > n && c > n
        then undefined
        else (r'-1)*n' + c'
    where
        n' = w8to16 n
        r' = w8to16 r
        c' = w8to16 c

readMatrix :: Word8 -> ByteString -> Maybe (Matrix, ByteString)
readMatrix n source = readMatrix' n2 (newMatrix n) source
    where
        n2 = square n
        readMatrix' 0 matrix source = return (matrix, source)
        readMatrix' k matrix source = do
            (next, source) <- readNum source
            readMatrix' (k-1) (matrix // [(n2-k+1,next)]) source

readNum  ::            ByteString -> Maybe (Word8, ByteString)
readNum  source = fmap convert $ readInt source
    where
        convert (a,b) = (fromIntegral a, trim b)
        trim source = case BC.uncons source of
            Just (c, trimmed) | c == '\n' || c == '\r' || c == ' '
                -> trim trimmed
            _   -> source
