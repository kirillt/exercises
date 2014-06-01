module Processor where

import Common
import Money (Money)

import Data.List
import Data.Tree
import Data.Function

type Acc = (Forest Stats, Maybe (Name, Forest Stats))

process :: [Entry] -> Tree Stats
process = join "All" . work
  where
    work :: [Entry] -> Forest Stats
    work =
      raise . map plant .
      sortBy (compare `on` fst) .
      map terminal

    plant :: (Name,Money) -> Tree Stats
    plant (n,m) = Node (Rubric n 1) [Node (Amount m) []]

    raise :: Forest Stats -> Forest Stats
    raise = finish . foldl' step base

    step :: Acc -> Tree Stats -> Acc
    step acc@(trees,curr) tree@(Node (Rubric n _) _) =
      let new   = nonterminal n in
      let fresh = Just (new,[tree])
      in  case curr of
            Nothing -> (trees, fresh)
            Just curr'@(old,xs) ->
              if old /= new then (finish acc, fresh)
                            else (trees, Just (old,xs))

    base :: Acc
    base = ([], Nothing)

    join :: Name -> Forest Stats -> Tree Stats
    join name xs = Node (Rubric name $ length xs) xs

    finish :: Acc -> Forest Stats
    finish (trees, Nothing    ) = trees
    finish (trees, Just (n,xs)) = join n xs : trees

terminal :: Entry -> (Name, Money)
terminal (_,n,m) = (n,m)

nonterminal :: Name -> Name
nonterminal _ = undefined
