

module Test.World (cases) where

import HReal.World
import HReal.Core.Vertex

import Data.Set  (fromList)
import Data.Map  (singleton, empty, elems, (!))
import Data.List

cases = [       isLeft $ apply zero $ insertKnot  $ fromList []      -- constraint: empty knots are forbidden
        ,       isLeft $ apply zero $ insertKnot  $ fromList [1]     -- constraint: ids must be members of world

        ,       isLeft $ apply zero $ removeById  $ 1                -- constraint: there must be target id
        ,       isLeft $ apply has1 $ removeById  $ 2                -- constraint: there must be target id
        ,       isLeft $ apply dep2 $ removeById  $ 1                -- constraint: target id must have no owners
        , not $ isLeft $ apply has1 $ removeById  $ 1                -- constraint: there must be target id

        , vals (vs $ w $ apply has1 $ removeById 1) == []            -- removing vertex removes it from vertices
        , elems(os $ w $ apply has1 $ removeById 1) == []            -- consistency check: there was bug with selector
        , g 1  (os $ w $ apply dep2 $ removeById 2) == []            -- removing vertex removes it from owners

        , not $ isLeft $ apply zero $ insertValue $ S "any value"    -- there is no constraints for adding
        , not $ isLeft $ apply has1 $ insertValue $ I 1              -- duplicates are available too
        
        , vals (idToVertex has1) == [I 1]                            -- inserting value inserts x and only x
        , vals (idToVertex some) == [I 1, S "2"]                     -- multiple + different types case
    ]
        where
            has1 = w $ apply zero $ insertValue $ I 1
            some = w $ apply has1 $ insertValue $ S "2"
            dep2 = w $ apply has1 $ insertKnot  $ fromList [1]
            vals = (map (\(Single v) -> v)) . elems
            g    = flip (!)
            vs   = idToVertex
            os   = idToOwners
            r (Right (r,_)) = r
            w (Right (_,a)) = a

isLeft  :: Either a b -> Bool
isLeft  (Left  _) = True
isLeft         _  = False
