{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

import Prelude as P

import Network

import HReal.Config
import HReal.Core.Vertex
import HReal.Ifaces.Vertex (decode)

import Data.Colour (blend)

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import Diagrams.Prelude
import Diagrams.Backend.Cairo.Gtk
import Diagrams.Backend.Cairo (Cairo)

import Diagrams.TwoD.Adjust (adjustSize)
import Diagrams.TwoD.Layout.Tree

import Data.Configurator

import Data.Int
import Data.Map as M
import Data.Set as S
import Data.Tree
import Data.Maybe
import Data.IORef
import Data.Colour (blend)

import Graphics.UI.Gtk
import Graphics.UI.Gtk.Glade

import Thrift.Transport
import Thrift.Protocol.Binary
import Thrift.Transport.Handle

import HReal.Ifaces.Ifaces_Types
import HReal.Ifaces.Builder_Client
import HReal.Ifaces.Extractor_Client
import HReal.Ifaces.Vertex (encode)

main :: IO ()
main = do
    -- Main initialization
    (config,   _)   <- autoReload autoConfig [Required "config"]
    Just builder    <- Data.Configurator.lookup config "builder"   :: IO (Maybe (HostName, PortID))
    Just extractor  <- Data.Configurator.lookup config "extractor" :: IO (Maybe (HostName, PortID))
    handleB         <- hOpen builder
    handleE         <- hOpen extractor
    let builder     = (BinaryProtocol handleB, BinaryProtocol handleB)
    let extractor   = (BinaryProtocol handleE, BinaryProtocol handleE)
    -- GUI  initialization
    initGUI
    Just xml <- xmlNew "GUI.glade"
    window   <- xmlGetWidget xml castToWindow      "MainWindow"
    output   <- xmlGetWidget xml castToTextView    "ServerOutput"
    input    <- xmlGetWidget xml castToEntry       "CommandInput"
    area     <- xmlGetWidget xml castToDrawingArea "DrawArea"
    -- Logic
    buffer   <- textViewGetBuffer output
    let interpreter = runCommand builder extractor area buffer
    window `onDestroy`       mainQuit
    input  `onEntryActivate` do
        entryGetText input >>= interpreter
        entrySetText input ""
    widgetShowAll window
    mainGUI


runCommand builder extractor area output source = do
    memory <- newIORef ""
    let write s = do --dirty
            curr <- readIORef memory
            writeIORef memory $ curr ++ s
    let flush = readIORef memory >>= textBufferSetText output
    runCommand' builder extractor area output source write flush

runCommand' builder extractor area output source write flush = do
    execute $ words source
    flush
    where
          execute (c1:c2:remainder) = do
              let command   = unwords [c1,c2]
              let argument  = unwords remainder
              case command of
                  "create value" -> create  (read argument :: Value ) builder   >>= printCreateResponse >> refresh
                  "create knot"  -> create  (read argument :: [Id]  ) builder   >>= printCreateResponse >> refresh
                  "remove id"    -> remove  (read argument ::  Id   ) builder   >>= printRemoveResponse >> refresh
                  "refresh $"    -> refresh
                  otherwise      -> printSuccess Nothing
          execute _ = printSuccess Nothing

          remove   = flip removeVertex
          extract' = flip extract
          refresh  = do
              result@(ExtractResult s (Just r) m) <- extract' "idToVertex" extractor
              printExtractResult result
              area `onExpose` \_ -> do
                  diagram <- prepareTo area $ drawGraph $ M.map (fromJust . decode) r
                  widgetGetDrawWindow area >>= (flip renderToGtk) (diagram :: Diagram Cairo R2)
                  return True
              widgetQueueDraw area

          prepareTo area diagram = do
              (canvasX, canvasY) <- widgetGetSize area
              let i = Just . fromIntegral
              let newSize = mkSizeSpec (i canvasX) (i canvasY)
              let oldSize = size2D diagram
              return $ toGtkCoords $ transform (adjustSize newSize oldSize) diagram

          drawGraph  m = drawGraph' m M.empty $ M.toList m

          drawGraph' m m' (   (k, Single value):other) = drawGraph' m (M.insert k (drawValue value) m') other
          drawGraph' m m' (kn@(k, Knot   ids  ):other) = if any isNothing $ P.map ((flip M.lookup) m') $ S.toList ids
                                                             then drawGraph' m m' $ other ++ [kn]
                                                             else drawGraph' m (M.insert k (merge True $ P.map (m' !) $ S.toList ids) $ deleteAll (S.toList ids) m') other
          drawGraph' _ m'   _ = merge False $ M.elems m'

          merge True  ds = renderTree id (~~)                 $ symmLayout' options $ Node drawKnot $ P.map ((flip Node) []) ds
          merge False ds = renderTree id (const.const mempty) $ symmLayout' options $ Node drawKnot   $ P.map ((flip Node) []) ds
                                        --pointfree yeeeeaah
          options        = with {slWidth = size2D, slHeight = size2D}

          deleteAll   ids m'   = foldr (\k m -> M.delete k m) m' ids

          drawKnot            = circle 0.3 # lw 1 # (fc black) :: Diagram Cairo R2
          drawValue (B value) = circle 1.5 # lw 1 # (fc $ if value then olive else red)
          drawValue (I value) = (text $ show value) <> (eqTriangle 3.5  # lw 1 # fc palegreen)
          drawValue (D value) = (text $ show value) <> (pentagon   2.0  # lw 1 # fc teal     )
          drawValue (S value) = (text $ show value) <> (nonagon    1.0  # lw 1 # fc seagreen )

          splitBy                 n    xs  = reverse $ splitBy' [[]] 0 n xs
          splitBy' (curr:t) i n (x:xs) = if   i == n
                                         then splitBy' ([]      :((reverse curr):t))  0    n (x:xs)
                                         else splitBy' ((x:curr):                t ) (i+1) n    xs
          splitBy' acc      _ _  []    = acc

          printCreateResponse (CreateResponse s r m) = printSuccess s >> printResult r >> printMessage m >> write "\n"
          printRemoveResponse (RemoveResponse s   m) = printSuccess s >>                  printMessage m >> write "\n"
          printExtractResult  (ExtractResult  s r m) = printSuccess s >> printMap    r >> printMessage m >> write "\n"

          printMap (Just m) = do
              write "[Result:"
              mapM_ prettyPrint $ M.toList $ M.map (fromJust . decode) m
              write "]"
          printMap Nothing  = return ()

          prettyPrint (k,v) = write $ "\n\t\t" ++ show k ++ " -> " ++ show v

          printSuccess  Nothing     = write "[Fail] "
          printSuccess (Just False) = write "[Fail] "
          printSuccess (Just True ) = write "[Good] "

          printResult   Nothing     = return ()
          printResult  (Just value) = write $ "[Result: " ++ show value ++ "] "

          printMessage  Nothing     = return ()
          printMessage (Just msg)   = write $ "\n[Server: " ++ show msg ++ "] "

class Creatable a where
    create :: (
        Protocol  pi, Protocol  po,
        Transport ti, Transport to
            ) => a -> (pi ti, po to) -> IO CreateResponse

instance Creatable [Id]     where
    create = create . S.fromList
instance Creatable (Set Id) where
    create = (flip createVertex) . encode . Knot
instance Creatable Value    where
    create = (flip createVertex) . encode . Single
