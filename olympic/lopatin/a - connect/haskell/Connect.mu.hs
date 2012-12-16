import Data.Int
import Data.List
import Data.Array.IO              as A
import Data.ByteString.Lazy.Char8 as B hiding (map, zip, elem, find, length, replicate, unwords, maximum, reverse)
import System.IO                       hiding (readFile)

main = do
    input                  <- B.readFile "connect.in"
    let Just ((n,_),lines) =  readPair input
    emptyGraph             <- graph n
    ((nodes,edges),    _ ) <- readEdges emptyGraph lines
    ns                     <- getElems nodes
    let uniqueNs           =  [ u | u <- [1..n], u `elem` ns ]
    let componentsCount    =  fromIntegral $ length uniqueNs
    let normalizingMap     =  zip uniqueNs [ 1..componentsCount ]
    let normalizedNs       =  [ u | x <- ns, let Just (_,u) = find (\(k,v) -> k == x) normalizingMap ]
    output                 <- openFile "connect.out" WriteMode
    hPrint    output componentsCount
    hPutStrLn output $ unwords $ map show normalizedNs
    hClose    output

type Nodes = IOUArray Int16 Int16
type Edges = IOArray  Int16 Nears
type Nears = [Int16]
type Graph = (Nodes, Edges)

graph :: Int16 -> IO Graph
graph n = do
    ns <- newListArray (1,n) [1..n]
    es <- newListArray (1,n) $ map (const []) [1..n]
    return (ns, es)

readEdges :: Graph -> ByteString -> IO (Graph, ByteString)
readEdges graph source = 
    case readEdge graph source of
        Nothing                 -> return (graph, source)
        Just    (graph, source) -> graph >>= (flip readEdges) source

readEdge :: Graph -> ByteString -> Maybe (IO Graph, ByteString)
readEdge graph source = do
    ((a,b),source) <- readPair source
    return (merge graph a b,source)
merge graph@(ns,es) a b = do
    aComp <- readArray ns a
    fromA <- readArray es a
    fromB <- readArray es b
    mapM (uncurry $ writeArray ns) $
        map (\i -> (i,aComp)) $ a:b:(fromA ++ fromB)
    mapM (uncurry $ writeArray es)
        [(a, b:fromA), (b, a:fromB)]
    return (ns,es)

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
