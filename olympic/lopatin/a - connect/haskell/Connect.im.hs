import Data.Int
import Data.Array                 as A
import Data.Array.Unboxed         as U
import Data.ByteString.Lazy.Char8 as B hiding (map, replicate)

main = do
    input <- B.readFile "connect.in"
    let Just ((n,_), lines) = readPair input
    let ((nodes,edges), _ ) = readEdges (graph n) lines
    print nodes

type Nodes = UArray Int16 Int16
type Edges =  Array Int16 Nears
type Nears = [Int16]
type Graph = (Nodes, Edges)

nodes n = U.listArray (1,n) [1..n]
edges n = A.listArray (1,n) $ map (const []) [1..n]
graph n = (nodes n, edges n)

readEdges :: Graph -> ByteString -> (Graph, ByteString)
readEdges graph source = 
    case readEdge graph source of
        Nothing -> (graph, source)
        Just (graph, source) -> readEdges graph source

readEdge graph source = do
    ((a,b),source) <- readPair source
    return (merge graph a b,source)
merge (ns,es) a b = 
    let aComp = ns U.! a
        fromA = b:(es A.! a)
        fromB = a:(es A.! b)
        newEs = es A.// [(a, fromA), (b, fromB)]
        newNs = ns U.// map (\n -> (n,aComp)) (fromA ++ fromB)
    in (newNs,newEs)

readPair :: ByteString -> Maybe ((Int16,Int16), ByteString)
readPair source = do
    (a,source) <- readInt  source
    (_,source) <- B.uncons source
    (b,source) <- readInt  source
    return ((conv a, conv b), trim source)
    where
        conv = fromIntegral
        trim source = case B.uncons source of
            Just (c, trimmed) | c == '\n' || c == '\r'
                -> trim trimmed
            _   -> source
