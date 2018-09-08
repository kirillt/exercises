module Main where

import Templates
import Data.IntMap
import Data.ByteString.Lazy.Char8 as B

-- ghc -prof -auto-all -O -rtsopts --make test.hs
-- ./test +RTS -p -RTS < data.csv > /dev/null
-- less test.prof

---------------------------
-- Files are like        --
-- nodesCount edgesCount --
-- nodeA nodeB           --
-- nodeC nodeD ...       --
---------------------------

main = do
    input <- B.readFile "test.in"
    let Just ((size,edges),_) = readAll input
    print $ edges ! 300
    return ()

readAll input = do
    ( size,input) <- readGraphSize input
    ( '\n',input) <- B.uncons      input
    (edges,input) <- readEdges     input
    return ((size,edges),input)
