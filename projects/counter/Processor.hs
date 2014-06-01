{-# LANGUAGE OverloadedStrings #-}

module Processor where

import Common
import Money (Money(Zero), n, plus)

import Data.List hiding (isInfixOf)
import Data.Tree
import Data.Function

import Data.Text (Text, pack, unpack, strip, toLower, isInfixOf)

type Acc = (Forest Stats, Maybe (Name, Forest Stats))

process :: [Entry] -> Tree Stats
process = join "All" . work
  where
    work :: [Entry] -> Forest Stats
    work =
      raise 20 . map plant 

    plant :: Entry -> Tree Stats
    plant (d,n,m) = Node (Terminal n m d) []

    raise :: Int -> Forest Stats -> Forest Stats
    raise 0 = id
    raise k =
      raise (k - 1) .
      finish . foldl' (step k) base .
      sortBy (compare `on`
        (\(Node x _) -> name x))

    step :: Int -> Acc -> Tree Stats -> Acc
    step k acc@(trees,curr) tree@(Node x _) =
      let new    = nonterminal k (n $ amount x) (name x) in
      let subset = new == name x in
      let single = if subset then  subForest tree     else [tree]  in
      let append = if subset then (subForest tree ++) else (tree:) in
      let fresh = Just (new, single)
      in case curr of
           Nothing -> (trees, fresh)
           Just curr'@(old,xs) ->
             if old /= new then (finish acc, fresh)
                           else (trees, Just (old, append xs))

    base :: Acc
    base = ([], Nothing)

    join :: Name -> Forest Stats -> Tree Stats
    join name xs = Node (Nonterminal name $ total xs) xs

    finish :: Acc -> Forest Stats
    finish (trees, Nothing    ) = trees
    finish (trees, Just (n,xs)) = join n xs : trees

    total :: Forest Stats -> Money
    total = foldl' plus Zero . map (\(Node x _) -> amount x)

nonterminal :: Int -> Double -> Name -> Name
nonterminal k m = rules . strip . toLower . pack
  where
    rules :: Text -> String
    rules n | "salary" `isInfixOf` n = "@salary"
    rules n | "fee"    `isInfixOf` n = "@fee"

    rules n | "sberba" `isInfixOf` n = "@atm"
    rules n | "bank"   `isInfixOf` n = "@atm"
    rules n | "cash"   `isInfixOf` n = "@atm"
    rules n | "moh0"   `isInfixOf` n = "@atm"
    rules n | "vb24"   `isInfixOf` n = "@atm"
    rules n | "vtb"    `isInfixOf` n = "@atm"
    rules n | "atm"    `isInfixOf` n = "@atm"

    rules n | "140817" `isInfixOf` n = "@alexeika"
    rules n | "240817" `isInfixOf` n = "@alexeika"

    rules n | "burger" `isInfixOf` n = "@food"
    rules n | "mcdona" `isInfixOf` n = "@food"
    rules n | "pyater" `isInfixOf` n = "@food"
    rules n | "appeti" `isInfixOf` n = "@food"
    rules n | "verniy" `isInfixOf` n = "@food"
    rules n | "superm" `isInfixOf` n = "@food"
    rules n | "versam" `isInfixOf` n = "@food"
    rules n | "rbucks" `isInfixOf` n = "@food"
    rules n | "chicke" `isInfixOf` n = "@food"
    rules n | "riomag" `isInfixOf` n = "@food"
    rules n | "polush" `isInfixOf` n = "@food"
    rules n | "subway" `isInfixOf` n = "@food"
    rules n | "smart"  `isInfixOf` n = "@food"
    rules n | "chaiy"  `isInfixOf` n = "@food"
    rules n | "chain"  `isInfixOf` n = "@food"
    rules n | "coop"   `isInfixOf` n = "@food"
    rules n | "dixy"   `isInfixOf` n = "@food"
    rules n | "kfc"    `isInfixOf` n = "@food"

    rules n | "tramon" `isInfixOf` n = "@wear"
    rules n | "colins" `isInfixOf` n = "@wear"
    rules n | "armand" `isInfixOf` n = "@wear"

    rules n | "zdorov" `isInfixOf` n = "@drugs"
    rules n | "pharma" `isInfixOf` n = "@drugs"
    rules n | "apteka" `isInfixOf` n = "@drugs"

    rules n | "medser" `isInfixOf` n = "@medicine"
    rules n | "medi"   `isInfixOf` n && not ("wiki" `isInfixOf` n) = "@medicine"
    rules n | "stoma"  `isInfixOf` n = "@medicine"

    rules n | "idsoft" `isInfixOf` n = "@games"
    rules n | "steam"  `isInfixOf` n = "@games"

    rules n | "googl"  `isInfixOf` n = "@soft"
    rules n | "githu"  `isInfixOf` n = "@soft"

    rules n | "stars"  `isInfixOf` n = "@poker"
    rules n | "tilt"   `isInfixOf` n = "@poker"

    rules n | "milan"  `isInfixOf` n = "@italy"
    rules n | "arco"   `isInfixOf` n = "@italy"
    rules n | "riva"   `isInfixOf` n = "@italy"
    rules n | "gard"   `isInfixOf` n = "@italy"
    rules n | "ital"   `isInfixOf` n = "@italy"
    rules n | "dro"    `isInfixOf` n = "@italy"

    rules n | "marsei" `isInfixOf` n = "@france"
    rules n | "cirm"   `isInfixOf` n = "@france"

    rules _ | k > 10 && m > 0 = "@positive"
    rules _ | k > 10 && m < 0 = "@negative"
    rules n = unpack n
