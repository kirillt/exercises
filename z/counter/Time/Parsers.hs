module Time.Parsers (DateToken (..), parsers) where

import Data.Char
import Data.Maybe

import System.Time (Month (..))

data DateToken = Year | Month | Day | Hour | Min | Sec deriving (Ord,Eq,Show)

type Parser = String -> [(DateToken,Int)]

parsers :: [Parser]
parsers = [toDate, toYear, toMonth, toDay, toTime]

toDate :: Parser
toDate s | checkDate s = parse s
         | otherwise = []
    where
        parse [y1,y2,y3,y4,'.',m1,m2,'.',d1,d2] = [(Year,toNumber4 y1 y2 y3 y4), (Month,toNumber2 m1 m2), (Day, toNumber2 d1 d2)]
        parse [d1,d2,'.',m1,m2,'.',y1,y2,y3,y4] = [(Year,toNumber4 y1 y2 y3 y4), (Month,toNumber2 m1 m2), (Day, toNumber2 d1 d2)]
        parse _ = []

        checkDate = all isDigit . filter (/= '.')

toYear :: Parser
toYear s | checkYear s = parse s
         | otherwise   = []
    where
        parse     s = [(Year,read s :: Int)]
        checkYear s = length s == 4 && all isDigit s

toMonth :: Parser
toMonth = map (\(m,_) -> (Month,monthToNumber m)) . (reads :: ReadS Month) . (\(c : cs) -> toUpper c : cs)

toDay :: Parser
toDay  s | checkDay  s = parse s
         | otherwise   = []
    where
        parse     s = [(Day,read s :: Int)]
        checkDay  s = (length s == 2 || length s == 1) && all isDigit s

toTime :: Parser
toTime s | checkTime s = parse s
         | otherwise   = []
    where
        parse [h1,h2,':',m1,m2,':',s1,s2] = [(Hour,toNumber2 h1 h2), (Min,toNumber2 m1 m2), (Sec,toNumber2 s1 s2)]
        parse [h1,h2,':',m1,m2]           = [(Hour,toNumber2 h1 h2), (Min,toNumber2 m1 m2)]
        parse _ = []

        checkTime = all isDigit . filter (/= ':')

toNumber4 :: Char -> Char -> Char -> Char -> Int
toNumber4 d1 d2 d3 d4 = read $ d1:d2:d3:d4:""

toNumber2 :: Char -> Char -> Int
toNumber2 d1 d2 = read $ d1:d2:""

monthToNumber :: Month -> Int
monthToNumber = fromJust . (flip lookup $ zip months [1..])
    where
        months = [January,February,
                  March,April,May,
                  June,July,August,
                  September,October,November,
                  December]
