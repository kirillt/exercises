module Common where

import Money (Money (Money), Currency)
import Time.Time (UnixTime)

type Name  = String
type Time  = UnixTime
type Entry = (Time,Name,Money)

data Stats = Terminal    Name Money Time
           | Nonterminal Name Money

name :: Stats -> Name
name (Terminal    n _ _) = n
name (Nonterminal n _  ) = n

amount :: Stats -> Money
amount (Terminal    _ m _) = m
amount (Nonterminal _ m  ) = m

instance Show Stats where
  show s =
    case amount s of
      Money c m ->
        name s ++ " (" ++
          show m ++ " " ++ show c
        ++ ")"
