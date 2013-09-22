import Data.Sequence

import Control.Monad
import Control.Monad.ST.Strict
import Data.STRef.Strict

import Criterion.Main

-- Benchmark

main =
    let
        left_only = generate 130000  0
        left_12x  = generate     38  3
        left_3x   = generate     18  5
        both      = generate      9  9
    in defaultMain [
      bench "naive     (130000 / 0)" $ whnf (normalize .    naive) left_only
    , bench "naive     (    38 / 3)" $ whnf (normalize .    naive) left_12x
    , bench "naive     (    15 / 5)" $ whnf (normalize .    naive) left_3x
    , bench "naive     (     9 / 9)" $ whnf (normalize .    naive) both
    , bench "tailrec   (130000 / 0)" $ whnf (normalize .  tailrec) left_only
    , bench "tailrec   (    38 / 3)" $ whnf (normalize .  tailrec) left_12x
    , bench "tailrec   (    15 / 5)" $ whnf (normalize .  tailrec) left_3x
    , bench "tailrec   (     9 / 9)" $ whnf (normalize .  tailrec) both
    , bench "strictst  (130000 / 0)" $ whnf (normalize . strictst) left_only
    , bench "strictst  (    38 / 3)" $ whnf (normalize . strictst) left_12x
    , bench "strictst  (    15 / 5)" $ whnf (normalize . strictst) left_3x
    , bench "strictst  (     9 / 9)" $ whnf (normalize . strictst) both
    ]

generate  0  0 = Empty
generate ld  0 = Node (ld, 0) (generate (ld-1) 0) Empty
generate  0 rd = Node ( 0,rd) Empty (generate (rd-1) 0)
generate ld rd = Node (ld,rd) (generate (ld-1) rd) (generate ld (rd-1))

-- Solution

data Tree a = Node !a !(Tree a) !(Tree a)
            | Empty
            deriving Show

-- In problem's example height of Node _ Empty Empty is 0, but I use 1 for this.
normalize = (max 0) . (flip (-) 1)
-- minHeight Empty              = 0
-- minHeight Node _ Empty Empty = 0, too

minHeight :: Tree a -> Integer
minHeight = normalize . naive

naive (Node _ l r) = (1+) $ naive l `min` naive r
naive  Empty       = 0

-- Common code

data Distance = Infinity | Finite !Integer
              deriving (Show, Eq)

inc :: Distance -> Distance
inc Infinity   = Infinity
inc (Finite x) = Finite $ x + 1

fromFinite :: Distance -> Integer
fromFinite (Finite x) = x 

instance Ord Distance where
    Finite l `compare` Finite r = l `compare` r
    Infinity `compare` Infinity = EQ
    Infinity `compare` _        = GT
    _        `compare` Infinity = LT

pop :: Seq a -> Maybe (Seq a, a)
pop = extract . viewl
    where
        extract EmptyL   = Nothing
        extract (l :< r) = Just (r,l)

push :: a -> Seq a -> Seq a
push r = (|> r)

-- Tail-recursive implementation with queue

tailrec root = work Infinity $ singleton (Finite 0,root)
    where
        work  m q = case pop q of
            Nothing         -> fromFinite m
            Just (q',(d,n)) ->
                if d > m then work m q'
                         else case n of
                             Node _ l r -> let d' = inc d
                                           in work  m $ push (d',l) $ push (d',r) q'
                             Empty      ->    work (m `min` d)                    q'

-- Implementation with queue and mutable state

strictst root = runST $ do
    mRef   <- newSTRef Infinity
    qRef   <- newSTRef $ singleton (Finite 0,root)
    result <- work mRef qRef
    return $ fromFinite result
    where
        work mRef qRef = work'
            where
                work' = do
                    m <- readSTRef mRef
                    q <- readSTRef qRef
                    case pop q of
                        Nothing         -> return m
                        Just (q',(d,n)) -> do
                            when (d >= m) $ writeSTRef qRef q'
                            when (d <  m) $ do
                                case n of
                                    Node _ l r -> do
                                        let d'  = inc d
                                        let q'' = push (d',l) $ push (d',r) q'
                                        writeSTRef qRef q''
                                    Empty      -> writeSTRef mRef $ m `min` d
                            work'
