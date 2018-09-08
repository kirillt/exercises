{-# LANGUAGE BangPatterns #-}

module Templates where

import Data.IntSet as S
import Data.IntMap as M

import Data.Maybe
import Data.ByteString.Lazy.Char8 as B
import Prelude hiding (readFile)

-----------
-- Types --
-----------

type Edges = IntMap IntSet
readEdge  :: Edges -> ByteString -> Maybe (Edges,ByteString)
readEdges ::          ByteString -> Maybe (Edges,ByteString)

------------
--  Impl  --
------------

readEdge edges source = do
    ((a,b),source) <- readPair source
    return (insertWith S.union a (S.singleton b) edges,
            source)

readEdges           source = readEdges' M.empty source where
    readEdges' !acc source = do
        let result = readEdge acc source
        if  result == Nothing
            then return (acc,source)
            else do
                (acc,source) <- result
                let splitted = B.uncons source
                if splitted == Nothing
                    then return (acc,source)
                    else do
                        (c,trimmed) <- splitted
                        readEdges' acc trimmed

readPair       source = do
    (a,source) <- readInt  source
    (_,source) <- B.uncons source
    (b,source) <- readInt  source
    return ((a,b), source)
