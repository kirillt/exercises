import Data.Int
import Data.IORef
import Data.Maybe
import Data.Array.IO
import Control.Monad

import Data.IntSet as S hiding (map, filter)
import Data.IntMap as M hiding (map, filter)

import Data.Maybe
import Data.ByteString.Lazy.Char8 as B hiding (map, filter, lines, words, unwords, hGetContents)
import Prelude hiding (readFile)

import System.IO.Unsafe


--import Data.ByteString       (ByteString)
--import Data.ByteString.Char8 (readFile, lines, words, readInt16)
--import Prelude     hiding    (readFile, lines, words)
import System.IO   hiding    (readFile)

readI  = fst.fromJust.(read :: String -> Int16)
parseI = (map (map readI).words).lines

parseE = (map (read :: Edge)).lines


data     Pair = Pair {l :: Int16, r :: Int16}
data     Edge = Edge {a :: Int16, b :: Int16}
instance Read Pair where
    readsPrec _ source = do
        (a,source) <- readsI source
        (b,source) <- readsI source
        return (Pair a b, source)
instance Read Edge where
    readsPrec _ source = do
        pair <- read source
        return $ edge pair

readsI = reads :: ReadS Int16

edge (Pair a b) = if b > a then Edge b a else Edge a b

main  = do
    input <- openFile "connect.in" ReadMode
    (descr:edges) <- hGetContents input
    ([n,m]:raw)   <- fmap parseI $ readFile "connect.in"
    let edgesList =   map (\[a,b] -> (a,b)) raw
    state         <- Main.init n
    color         <- newIORef  0
    mapM (connect $ em state) edgesList
    mapM (work True state color)  [1..n]
    colorValue    <- readIORef color
    components    <- mapM (readArray (nc state)) [1..n]
    file          <- openFile "connect.out" WriteMode
    hPrint    file colorValue
    hPutStrLn file $ unwords $ map show components
    hClose    file

-- walking through graph

work start state color curr = do
    exit <- used (un state) curr
    if exit then return () else do
        when start $ inc color
        use (un state) curr
        colorValue <- readIORef color
        writeArray (nc state) curr colorValue
        edges <- getEdgesFrom state color curr
        mapM (go state color curr) edges
        return ()

go   state color curr edge@(a,b) = do
    exit <- used (ue state) edge
    if exit then return () else do
        use (ue state) edge
        if curr == a
            then work False state color b
            else work False state color a

-- extracting edges

getEdgesFrom state color curr = do
    maybeEdges <- mapM (getEdgeIfExist (em state) curr) [1..n state]
    return $ map fromJust $ filter isJust maybeEdges

getEdgeIfExist matrix a b = do
    exist <- readArray matrix (a,b)
    if exist then return $ Just (a,b)
             else return Nothing

-- Graph and state arrays
--  em - edges matrix      ue - used edges
--  nc - node  component   un - used nodes
data State = State {
    n  :: Int16,
    em :: IOArray (Int16,Int16) Bool,
    ue :: IOArray (Int16,Int16) Bool,
    nc :: IOArray  Int16      Int16 ,
    un :: IOArray  Int16      Bool
}

init :: Int16 -> IO State
init n = do
    em <- newArray (cart 1 n) False
    ue <- newArray (cart 1 n) False
    nc <- newArray      (1,n) 0
    un <- newArray      (1,n) False
    return $ State n em ue nc un

-- cartesian product
cart l r = ((l,l), (r,r))

inc counter = do
    curr <- readIORef counter
    writeIORef counter (curr + 1)

use       array  thing = writeArray array thing True
used      array  thing =  readArray array thing
connect   matrix (a,b) = do
    writeArray matrix (a,b) True
    writeArray matrix (b,a) True
