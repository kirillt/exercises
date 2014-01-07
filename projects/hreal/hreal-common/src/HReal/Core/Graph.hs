{-# OPTIONS_GHC -O -Wall #-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

module HReal.Core.Graph where

import Data.Set hiding (map, null)
import Data.Map  (Map , keys, (!))
import Data.Tree (Tree,  Forest, unfoldTreeM)
import Data.Maybe

import HReal.Core.Vertex

import Data.STRef
import Control.Monad.ST

data Node      k v =  Node k v                   deriving (Show, Eq, Ord)
data Edge      k v =  Edge (Node k v) (Node k v) deriving (Show, Eq, Ord)
type EdgesList k v = [Edge k v]

instance Functor (Node k) where
    fmap f (Node k v) = Node k $ f v
instance Functor (Edge k) where
    fmap f (Edge n m) = Edge (g n) (g m)
        where g = fmap f

toEdgesList   :: Map Id Vertex ->       EdgesList Id Vertex
toEdgesList   m   = keys m >>= extractEdges m

extractEdges  :: Map Id Vertex -> Id -> EdgesList Id Vertex
extractEdges  m k = extractEdges' (singleton k) $ from
    where
        extractEdges' vs (Knot  ks) = map (\k' -> Edge from' $ Node k' $ m ! k') $ toList $ ks `difference` vs
        extractEdges' _         _   = []
        from' = Node k from
        from  = m ! k

-- this function _doesn't_ build         -- it can be wasteful to use (Node (Node (Vertex)))
-- a forest of connection components     -- (we wrap Vertices with Nodes and Data.Tree too)
toNodesForest ::           Map Id Vertex ->               Forest (Node Id Vertex)
toNodesForest   m   = reverse $ fst $ foldl extract ([], empty) $ keys m
    where extract (f,   vs) k  = let (       tree  , vs') = extractTree vs m k
                                 in  (append tree f, vs')
          append   Nothing  xs =   xs
          append  (Just  x) xs = x:xs

extractTree  :: Set Id -> Map Id Vertex -> Id -> (Maybe (Tree   (Node Id Vertex)), Set Id)
extractTree  vs m k = if   k `member` vs
                      then (Nothing,  vs)
                      else runST $ do
                          vs'         <-   newSTRef vs
                          let visit n = modifySTRef vs' $ insert n
                          let visited =   readSTRef vs'
                          let extract k' = do
                              visit k'
                              vs'' <- visited
                              let vertex = m ! k'
                              return (Node k' vertex, toList $ children vertex `difference` vs'')
                          tree <- unfoldTreeM extract k
                          vs'' <- visited
                          return (Just tree, vs'')
    where children (Knot ks) = ks
          children       _   = empty
