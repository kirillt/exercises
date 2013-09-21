import Data.Maybe

data Accumulator a = Fail | Step a Int | Begin

extract :: Accumulator a -> Bool
extract (Step _ 1) = False
extract (Step _ _) = True
extract _          = False

parts  :: Ord a => [a] -> Bool
parts  xs = or [ extract $ foldl (step l) Begin xs | l <- [2 .. length xs] ]
    where
        step _ Fail       _ = Fail
        step _ Begin      y = Step y 1
        step l (Step x k) y | k == l = Step y 1
        step _ (Step x k) y | x <  y = Step y $ k + 1
        step l (Step x k) _ | k <  l = Fail
        step _ _          _ = Fail

parts2 :: Ord a => [a] -> Bool
parts2 xs =
    let n = length xs
    in if n `mod` 2 == 1
       then False
       else work (n `div` 2) 0 [] [] xs
           where
                check :: Ord a => (a -> a -> Bool) -> [a] -> Bool
                check f xs@(x:xt) = and $ zipWith f xs xt
                check _       []  = True

                work k = work'
                    where
                        work' l ls rs (y:ys) = work' (l + 1) (y:ls) rs ys || work' l ls (y:rs) ys
                        work' l ls rs    []  | l == k = check (>) ls && check (>) rs
                        work' _ _  _     _   = False
