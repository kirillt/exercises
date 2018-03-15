module Utils.Misc where

evens :: [a] -> [a]
evens []     = []
evens (x:xs) = odds xs

odds  :: [a] -> [a]
odds  []     = []
odds  (x:xs) = x : evens xs

alternate :: [a] -> [a] -> [a]
alternate    []     rs  = rs
alternate    ls     []  = ls
alternate (l:ls) (r:rs) = l:r:(alternate ls rs)
