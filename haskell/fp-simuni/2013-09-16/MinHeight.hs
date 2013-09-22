import Criterion.Main

-- Benchmark

main =
    let
        left_only = generate 130000  0
        left_12x  = generate     38  3
        left_3x   = generate     18  5
        both      = generate      9  9
    in defaultMain [
      bench "naive (130000 / 0)" $ whnf (normalize . naive) left_only
    , bench "naive (    38 / 3)" $ whnf (normalize . naive) left_12x
    , bench "naive (    15 / 5)" $ whnf (normalize . naive) left_3x
    , bench "naive (     9 / 9)" $ whnf (normalize . naive) both
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

cps = undefined

mutable = undefined
