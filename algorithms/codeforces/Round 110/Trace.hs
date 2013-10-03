import Prelude hiding (readList)

import System.IO

import Data.Word
import Data.List
import Data.ByteString.Lazy       as B  hiding (map, reverse)
import Data.ByteString.Lazy.Char8 as BC hiding (map, reverse)

main = do
    hSetBuffering stdin LineBuffering
    first           <- fmap BC.pack System.IO.getLine
    second          <- fmap BC.pack System.IO.getLine
    let Just ( n,_) =  readNum                   first
    let Just (rs,_) =  readList (fromIntegral n) second
    print $ sum $ map (uncurry square) $ toPairs $ reverse $ sort $ 0:rs

toPairs :: [a] -> [(a,a)]
toPairs      []  = []
toPairs   (_:[]) = []
toPairs (a:b:ts) = (a,b):(toPairs ts)

square  :: Word16 -> Word16 -> Float
square a b = if a < b -- на всякий случай
             then square' b a
             else square' a b
    where
        square' a b = pi * ab1 * ab2
        ab1 = fromIntegral $ a - b
        ab2 = fromIntegral $ a + b

readList :: Word8 -> ByteString -> Maybe ([Word16], ByteString)
readList n source = readList' n [] source
    where
        readList' 0 acc source = return (acc, source)
        readList' i acc source = do
            (curr, source) <- readNum  source
            readList' (i-1) (curr:acc) source

readNum  ::          ByteString -> Maybe ( Word16  , ByteString)
readNum  source = fmap convert $ readInt source
    where
        convert (a,b) = (fromIntegral a, trim b)
        trim source = case BC.uncons source of
            Just (c, trimmed) | c == '\n' || c == '\r' || c == ' '
                -> trim trimmed
            _   -> source
