{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Genetic.Individ where

import Genetic.Atom
import Utils.Aspects
import Utils.Misc
import Data.Map hiding (map)

type Individ = [Atom]

instance Bounded Individ where
    minBound = replicate 4 minBound
    maxBound = replicate 8 maxBound

instance Aspected Individ where
    schema = AbstractSchema $ fromList
        [ ("evens" , AStringType )
        , ("odds"  , AStringType )
        , ("length", AIntegerType)
        ]
    assembleRaw (ConcreteSchema cs) = 
        let AString es = cs ! "evens"
            AString os = cs ! "odds"
            AInteger n = cs ! "length"
            rawResult  = alternate os es
            currentN   = length rawResult
            targetN    = fromInteger n
        in  map Atom $
            case compare targetN currentN of
                LT -> take targetN $ rawResult
                EQ -> rawResult
                GT -> rawResult ++ replicate (targetN - currentN) 'a'
    disassembleRaw as =
        let rawString = map unpack as
        in  ConcreteSchema $ fromList
            [ ("evens" , AString  $ evens $ rawString)
            , ("odds"  , AString  $ odds  $ rawString)
            , ("length", AInteger $ toInteger $ length as)
            ]
