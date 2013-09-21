import Data.Maybe

data Accumulator a = Fail | Step a Int | Begin

extract :: Accumulator a -> Bool
extract (Step _ 1) = False
extract (Step _ _) = True
extract _          = False

parts :: Ord a => [a] -> Bool
parts xs = or [ extract $ foldl (step l) Begin xs | l <- [2 .. length xs] ]
    where
        step _ Fail       _ = Fail
        step _ Begin      y = Step y 1
        step l (Step x k) y | k == l = Step y 1
        step _ (Step x k) y | x <  y = Step y $ k + 1
        step l (Step x k) _ | k <  l = Fail
        step _ _          _ = Fail
