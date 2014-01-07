{-# OPTIONS_GHC -O -Wall #-}
{-# LANGUAGE DeriveDataTypeable #-}
module HReal.Core.Vertex where

import Data.Int
import Data.Set

import Data.Typeable

data Value  = B !Bool
            | I !Int32
            | D !Double
            | S !String
            deriving (Eq, Show, Read)

type Id = Int32

data Vertex = Single {value :: Value}
            | Knot   {ids   :: Set Id}
            deriving Typeable

instance Show Vertex where
    show (Knot    is   ) = show $ elems is
    show (Single  val  ) = show val
