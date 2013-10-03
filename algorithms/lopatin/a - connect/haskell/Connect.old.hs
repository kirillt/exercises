import Data.Maybe
import Data.Array                 as I
import Data.IntSet                as S hiding (map)
import Data.ByteString.Lazy.Char8 as B hiding (map)

main = do
    input <- B.readFile "connect.in"
    let Just ((n,_),remainder) = readPair  input
    let edgesLines             = trim remainder
    let (components,        _) = readEdges (initNodes n) edgesLines
    print $ components
    return ()

initNodes :: Int -> Array Int IntSet
initNodes n = listArray (1,n) $ map initNode [1..n]
    where initNode n = S.singleton n

readEdges :: Array Int IntSet -> ByteString -> (Array Int IntSet,ByteString)
readEdges components source = 
  case readEdge components source of
    Nothing -> (components, source)
    Just (components, source) -> readEdges components (trim source)

readEdge  :: Array Int IntSet -> ByteString -> Maybe (Array Int IntSet,ByteString)
readEdge components source = do
    ((a,b),source) <- readPair source
    return (merge components a b,source)

merge     :: Array Int IntSet -> Int -> Int -> Array Int IntSet
merge components a b = components // map (\k -> (k,commonNodes)) (S.elems commonNodes) where
    commonNodes = S.union (components ! a) (components ! b)

readPair source = do
    (a,source) <- readInt  source
    (_,source) <- B.uncons source
    (b,source) <- readInt  source
    return ((a,b), source)

trim source =
  case B.uncons source of
    Just (c, trimmed) | c == '\n' || c == '\r' -> trim trimmed
    _ -> source
