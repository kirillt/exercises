{-# OPTIONS_GHC -O -Wall -fno-warn-missing-signatures #-}

module HReal.Language.Sugar where

import Data.Set as S

import HReal.Core.World
import HReal.Core.Vertex
import HReal.Core.History

-- Aliases:

w  = wrap
a  = apply

-- Shortcuts:

onHistory = wrap . apply

bind      = onHistory . insertKnot . S.fromList
create    = onHistory . insertValue

int       = create . I
str       = create . S
bool      = create . B
double    = create . D
