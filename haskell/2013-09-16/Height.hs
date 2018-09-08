data Tree a = Node !a !(Tree a) !(Tree a)
            | Empty
            deriving Show

height :: Tree a -> Integer
height Empty = 0
height (Node _ Empty Empty) = 0
height (Node _ l     r    ) = 1 + max (height l) (height r)
