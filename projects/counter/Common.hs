module Common where

import Money (Money (Money), Currency)
import Time.Time (UnixTime)

type Name  = String
type Time  = UnixTime
type Entry = (Time,Name,Money)

data Stats = Rubric String Int
           | Amount Money

instance Show Stats where
  show (Rubric  name    n ) = name ++ " (" ++ show n ++ ")"
  show (Amount (Money c n)) = show c ++ " " ++ show n
