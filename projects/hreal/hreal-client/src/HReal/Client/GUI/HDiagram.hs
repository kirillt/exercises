{-# OPTIONS_GHC -O -Wall #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module HReal.Client.GUI.HDiagram where

import Prelude   as P
import Data.Map  as M
import Data.Tree as T (Tree (Node), rootLabel)
import Data.Maybe

import HReal.Core.Graph  as G
import HReal.Core.Vertex hiding (value)

import Diagrams.Prelude hiding (start)
import Diagrams.Backend.Cairo.Gtk
import Diagrams.Backend.Cairo (Cairo)
import Diagrams.TwoD.Adjust (adjustSize)
import Diagrams.TwoD.Layout.Tree

type Ids      = Option  (Last  Id)
type CDiagram = QDiagram Cairo R2      -- C means `Cairo`
type HDiagram = CDiagram Ids           -- H means `HReal`
type ADiagram = CDiagram Any           -- A means `Any`

toGtkForm :: Integral a => (a,a) -> HDiagram -> HDiagram
toGtkForm (sizeX, sizeY) diagram = toGtkCoords $ resize diagram
    where
        resize  = transform $ adjustSize newSize oldSize
        newSize = mkSizeSpec (i sizeX) (i sizeY)
        oldSize = size2D diagram
        i = Just . fromIntegral

visualizeMap :: Map Id Vertex -> HDiagram
visualizeMap = vcat . P.map (drawTree . fmap visualize') . toNodesForest
    where
        drawTree = combine . symmLayout' options
        options  = with {
            slWidth  = fromMaybe (0,0) . extentX,
            slHeight = fromMaybe (0,0) . extentY
        }
        visualize' (G.Node  k v)     = visualize  k v
        combine                      = alignT . centerX . combine'
        connect             f t      = (withKey Nothing) $ f ~~ t # lw 2
        combine'   (T.Node (a,p) cs) = a # moveTo p
                                       <> mconcat (P.map  combine'                     cs)
                                       <> mconcat (P.map (connect p . snd . rootLabel) cs)
--TODO: not only trees drawing

visualize  :: Id -> Vertex -> HDiagram
visualize  k (Knot   _) =               withKey (Just k) $ drawKnot
visualize  k (Single v) = withLabel v $ withKey (Just k) $ drawValue v

drawKnot  :: ADiagram
drawKnot  = circle 0.4 # lw 1 # (fc black)

drawValue :: Value -> ADiagram
drawValue (B _) = circle     1.5 # lw 1 # fc olive
drawValue (I _) = eqTriangle 3.5 # lw 1 # fc palegreen
drawValue (D _) = pentagon   2.0 # lw 1 # fc teal
drawValue (S _) = nonagon    1.0 # lw 1 # fc seagreen

withLabel :: Show a => a -> HDiagram -> HDiagram
withLabel = (<>) . (withKey Nothing) . text . tail . tail . show    
         -- tail . tail is a dirty thing to remove first two
         -- symbold of string representation,
         -- they are about value type

withKey   :: Maybe Id    -> ADiagram -> HDiagram
withKey   = (.) value $ (.) Option $ fmap Last
