{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Time.Time where

import Data.Map  (Map, fromList, insert, (!))
import Data.List (nub, filter, find)
import Data.Maybe
import Data.Word

import Data.Serialize
import Control.Applicative

import Time.Parsers
import System.Time

newtype UnixTime = UnixTime {
    fromUnixTime :: Word32
} deriving (Eq,Ord,Num)

instance Serialize UnixTime where
    put = put . fromUnixTime
    get = UnixTime <$> get

instance Read UnixTime where
    readsPrec _ s = let (l,r) = grab s in map (\x -> (x,r)) $ read' l
        where
            read' = map (toTime . toDiff) . maybeToList . toMap . parse

            toTime d = UnixTime $ (\(TOD i _) -> fromIntegral i) $ addToClockTime d $ TOD 0 0

            toDiff m = noTimeDiff {
                    tdYear  = max 0 $ m ! Year  - 1970,
                    tdMonth = max 0 $ m ! Month - 1,
                    tdDay   = max 0 $ m ! Day   - 1,
                    tdHour  = m ! Hour,
                    tdMin   = m ! Min,
                    tdSec   = m ! Sec
                }

            toMap :: [(DateToken,Int)] -> Maybe (Map DateToken Int)
            toMap l | checkUnique l = Just $ foldl put cleanMap l
                    | otherwise     = Nothing
                where
                    cleanMap = fromList $ zip [Year,Month,Day,Hour,Min,Sec] [0,0..]
                    put      = flip $ uncurry insert

                    checkUnique l =
                        let l' = nub $ map fst l
                        in length l == length l'

            parse :: String -> [(DateToken,Int)]
            parse s = do { w <- words s ; p <- parsers ; p w }

            grab  :: String -> (String,String)
            grab  s = (flip splitAt) s $ case findStop of
                    Just (_,k) -> k
                    Nothing    -> n
                where
                    findStop = find (\(e,i) -> elem e stoppers) $ zip s [0..]
                    stoppers = "[]();,"
                    n = length s

instance Show UnixTime where
    show = show . (flip TOD) 0 . fromIntegral . fromUnixTime
