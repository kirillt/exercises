import Data.Colour (blend)

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import Diagrams.Prelude
import Diagrams.Backend.Cairo.Gtk
import Diagrams.Backend.Cairo (Cairo)

import Diagrams.TwoD.Adjust (adjustSize)

main :: IO ()
main = do
    initGUI
    Just xml <- xmlNew "GUI.glade"
    window   <- xmlGetWidget xml castToWindow      "window"
    spin     <- xmlGetWidget xml castToSpinButton  "spinButton"
    area     <- xmlGetWidget xml castToDrawingArea "drawingArea"
    window `onDestroy`      mainQuit
    window `onSizeRequest` (return $ Requisition 200 200)
    bindDrawing spin area pentaflake
    widgetShowAll window
    mainGUI

bindDrawing :: SpinButton -> DrawingArea -> (Int -> Diagram Cairo R2) -> IO ()
bindDrawing spin area drawer = do
    spin `onValueSpinned` (widgetQueueDraw area)
    area `onExpose` \_ -> do
        diagram <- (fmap drawer $ spinButtonGetValueAsInt spin) >>= prepareTo area
        widgetGetDrawWindow area >>= (flip renderToGtk) diagram
        return True
    return ()

prepareTo :: DrawingArea -> Diagram Cairo R2 -> IO (Diagram Cairo R2)
prepareTo area diagram = do
    (canvasX, canvasY) <- widgetGetSize area
    let newSize = mkSizeSpec (i canvasX) (i canvasY)
    let oldSize = size2D diagram
    return $ toGtkCoords $ transform (adjustSize newSize oldSize) diagram
        where i = Just . fromIntegral

pentaflake :: Int -> Diagram Cairo R2
pentaflake 0 = regPoly 5 1 # lw 0
pentaflake n = appends (p' # fc (cs !! (n-1)))
                       (zip  vs (repeat (rotateBy (1/2) p')))
  where vs = take 5 . iterate (rotateBy (1/5))
                    . (if odd n then negateV else id) $ unitY
        cs = iterate (blend 0.1 white) blue
        p' = pentaflake $ n-1
