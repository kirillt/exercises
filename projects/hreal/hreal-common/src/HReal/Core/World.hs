{-# OPTIONS_GHC -O -Wall #-}
{-# LANGUAGE DeriveDataTypeable #-}
module HReal.Core.World where

import Prelude hiding (null, lookup)

import Data.Map  as M (Map, (!), member, empty, keys, adjust, insert, delete, lookup, insertWith)
import Data.Set  as S (Set, elems, null)
import Data.List as L (find, delete)

import Data.Typeable

import HReal.Core.Vertex hiding (ids)

data World      = World {
    idToVertex  ::  Map Id Vertex,
    idToOwners  ::  Map Id [Id]
} deriving (Show, Typeable)

zero :: World
zero         = World empty empty

upVs :: World -> (Map Id Vertex -> Map Id Vertex) -> World
upVs w f     = w {idToVertex = f $ idToVertex w}

upOs :: World -> (Map Id [Id]   -> Map Id [Id]  ) -> World
upOs w f     = w {idToOwners = f $ idToOwners w}

upVO :: World -> (Map Id Vertex -> Map Id Vertex) ->
                 (Map Id [Id]   -> Map Id [Id]  ) -> World
upVO w fv fo = upOs (upVs w fv) fo

data Constraint = Constraint {
    -- must be True for continue
    constraint  ::  World -> Bool,
    name        ::  String
} deriving Typeable

instance Show Constraint where
    show (Constraint _ n) = n

data Action a   = Action {
    constraints :: [Constraint],
    createPost  ::  a -> [Constraint],
    action      ::  World -> (a, World)
}

apply  :: Action a -> World -> Either Constraint World
apply a before = onlyWorld $ apply' a before
    where
        onlyWorld (Right (_,w)) = Right w
        onlyWorld (Left   c   ) = Left  c

apply' :: Action a -> World -> Either Constraint (a, World)
apply' a before =     continueIf before (map  pre $ constraints a       )  next     Left
    where next  = let r@(result, after) = action a $ before
                  in  continueIf after  (map post $ createPost  a result) (Right r) Left
          pre  c = c {name = "[Pre  constraint] " ++ name c}
          post c = c {name = "[Post constraint] " ++ name c}

continueIf :: World -> [Constraint] -> a -> (Constraint -> a) -> a
continueIf w cs t e = case find check cs of
    Nothing -> t
    Just  c -> e c
    where check = not . (flip ($) w) . constraint

freeId :: World -> Id
freeId (World vs _)  = getFirstFree $ keys vs
    where getFirstFree = getFirstFree' 1
          getFirstFree' i []     = i
          getFirstFree' i (k:ks) =
              if i == k
                  then getFirstFree' (i+1) ks
                  else i

insertValue :: Value  -> Action Id
insertValue v    = Action pre post put
    where pre    = []
          post   = (:[]) . containsId
          put w  = (k, upVs w $ insert k (Single $! v)) where
                    k = freeId w

insertKnot  :: Set Id -> Action Id
insertKnot is    = Action pre post put
    where is'    = S.elems is
          pre    = isNotEmpty:(map containsId is')   where
                   isNotEmpty = Constraint (\_ -> not $ null is)
                       "Empty knots are forbidden."
          post   = (:[]) . containsId
          put  w = (k, upVO w insKn insOw)
              where k = freeId w
                    insKn = insert k (Knot is)
                    updOw = \nOw ows -> nOw ++ ows
                    insOw = \idToOws -> foldr (flip (insertWith updOw) [k]) idToOws is'

removeById  :: Id -> Action ()
removeById k     = Action pre post remove
    where pre    = [containsId k, hasntOwner k]
          post _ = [  absentId k]
          remove (World vs os) = ((), World vs' os')
              where vs' = M.delete k vs
                    os' = foldr (adjust $ L.delete k) os $ ids' $ vs ! k
                    ids' (Knot ids) = elems ids
                    ids'  _         = []

-- Assistant:

absentId   :: Id -> Constraint
absentId   i = Constraint (not . (member i) . idToVertex) $
    "There mustn't be vertex with id " ++ show i

hasntOwner :: Id -> Constraint
hasntOwner i = Constraint (free . (lookup i) . idToOwners) $
    "There mustn't be knot refers to vertex with id " ++ show i
    where free  Nothing  = True
          free (Just []) = True
          free  _        = False

containsId :: Id -> Constraint
containsId i = Constraint ((member i) . idToVertex) $
    "There must be vertex with id " ++ show i
