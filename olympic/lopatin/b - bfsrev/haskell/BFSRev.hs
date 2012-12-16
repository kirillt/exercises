import Data.Word
import Data.Array.IO              as A
import Data.IntMap                as M hiding (map)
import Data.IntSet                as S hiding (map)
import Data.ByteString.Lazy.Char8 as B hiding (map, zip, length,
replicate, unwords)
import System.IO                       hiding (readFile)

main = do
   input                    <- B.readFile "bfsrev.in"
   let Just ((n,s,_),lines) =  readTriple input
   emptyGraph               <- graph n
   ((nodes,edges),      _ ) <-  readEdges emptyGraph lines
   undefined
   output                   <- openFile "bfsrev.out" WriteMode
   hClose output

type Nodes = IOUArray Word Word
type Edges = IOArray  Word Nears
type Nears = [Word]
type Graph = (Nodes, Edges)

graph :: Word -> IO Graph
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
   return (process graph a b,source)
process graph@(ns,es) a b = do
   undefined

readPair :: ByteString -> Maybe ((Word,Word), ByteString)
readPair source = do
   (a,source) <- readInt  source
   (_,source) <- B.uncons source
   (b,source) <- readInt  source
   return ((conv a, conv b), trim source)

-- copy paste
readTriple :: ByteString -> Maybe ((Word,Word,Word), ByteString)
readTriple source = do
   (a,source) <- readInt  source
   (_,source) <- B.uncons source
   (b,source) <- readInt  source
   (_,source) <- B.uncons source
   (c,source) <- readInt  source
   return ((conv a, conv b, conv c), trim source)

conv = fromIntegral
trim source = case B.uncons source of
       Just (c, trimmed) | c == '\n' || c == '\r'
               -> trim trimmed
       _   -> source
