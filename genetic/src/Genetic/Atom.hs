module Genetic.Atom where

import System.Random
import Utils.Aspects
import Data.Char
import Data.Map      hiding (map)

newtype Atom = Atom { unpack :: Char } deriving (Eq, Ord)

instance Show Atom where
    show        = show . unpack
    showList xs = id   . (showList $ map unpack xs)

instance Random Atom where
    random                     = randomR (minBound,maxBound)
    randomR (Atom l, Atom r) g = let (     c,g') = randomR (l,r) g
                                 in  (Atom c,g')
instance Bounded Atom where
    minBound = Atom 'A'
    maxBound = Atom 'z'

instance Aspected Atom where
    schema = AbstractSchema $ fromList
        [ ("isUpper" , ABoolType)
        , ("isLetter", ABoolType)
        , ("rawChar" , ACharType)
        ]
    assembleRaw (ConcreteSchema cs) =
        let ABool u = cs ! "isUpper"
            ABool l = cs ! "isLetter"
            AChar c = cs ! "rawChar"
            adjustCase   = if u
                           then toUpper else toLower
            adjustLetter = case (l, isLetter c) of
                               (True ,True ) -> c
                               (True ,False) -> 'a'
                               (False,True ) -> '!'
                               (False,False) -> c
        in  Atom $ adjustCase $ adjustLetter
    disassembleRaw (Atom c) =
        ConcreteSchema $ fromList
            [ ("isUpper" , ABool $ isUpper  c)
            , ("isLetter", ABool $ isLetter c)
            , ("rawChar" , AChar c)
            ]
