module Common where

import Money (Money, Currency)
import Time.Time (UnixTime)

type Name  = String
type Time  = UnixTime
type Entry = (Time,Name,Money)
