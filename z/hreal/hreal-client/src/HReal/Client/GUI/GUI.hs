{-# OPTIONS_GHC -O -Wall -fno-warn-missing-signatures -fno-warn-unused-do-bind #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module HReal.Client.GUI.GUI where

import Data.IORef

import Graphics.UI.Gtk hiding (eventSent, eventButton, eventKeyName)
import Graphics.UI.Gtk.Glade
import Graphics.UI.Gtk.Gdk.Events

import Diagrams.Prelude hiding (e)
import Diagrams.Backend.Cairo.Gtk

import HReal.Client.Protocols
import HReal.Client.GUI.HDiagram

runClient world _ = do
    initGUI
    Just xml <- xmlNew "GUI.glade"
    window   <- xmlGetWidget xml castToWindow      "MainWindow"
    area     <- xmlGetWidget xml castToDrawingArea "DrawingArea"

    d        <- newIORef mempty

    window `onDestroy`      mainQuit
    window `onSizeRequest` (return $ Requisition 600 400)
    area   `onButtonPress` \e -> case eventButton e of
        LeftButton  -> do
            d' <- readIORef d
            print $ sample d' $ p2 (eventX e, eventY e)
            return True
        _           ->
            return False
    area   `onExpose`      \_ -> do
        Response (Just m) _ <- interpret world "wrap $ apply $ Action [] (const []) $ \\w -> (undefined, w)"
        d' <- prepareTo area $ visualizeMap $ decodeMap m
        writeIORef d d'
        widgetGetDrawWindow area >>= (flip renderToGtk) d'
        return True
    widgetQueueDraw area
    widgetShowAll window
    mainGUI

prepareTo :: DrawingArea -> HDiagram -> IO HDiagram
prepareTo area diagram = do
    let d = scale 15 diagram
    (rawX, rawY) <- widgetGetSize area
    let ( canvasX,  canvasY) = (i rawX, i rawY) :: (Double,Double)
    let (diagramX, diagramY) = size2D d
    let x = max 0 $ (canvasX - diagramX) / 2
    let y = max 0 $ (canvasY - diagramY) / 2
    let expanded = strutY y
                     ===
         strutX x ||| d ||| strutX x
                     ===
                   strutY y
    return $ toGtkCoords $ expanded
        where i = fromIntegral
