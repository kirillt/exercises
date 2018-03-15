

module HReal.Ifaces.Vertex (
    decode,
    encode,
    decodeMap,
    encodeMap
) where

import Prelude  hiding (map)
import Data.Map (Map,   map)
import Data.Maybe (fromJust)

import HReal.Ifaces.Ifaces_Types as Ifaces (Vertex (..))
import HReal.Core.Vertex         as Core   (Vertex (..), Value (..), Id)

decodeMap :: Map Id Ifaces.Vertex -> Map Id Core.Vertex
decodeMap = map (fromJust . decode)

encodeMap :: Map Id Core.Vertex -> Map Id Ifaces.Vertex
encodeMap = map encode

decode :: Ifaces.Vertex -> Maybe Core.Vertex
decode (Ifaces.Vertex {f_Vertex_ids         = Just ids'  }) = Just $ Knot     ids'
decode (Ifaces.Vertex {f_Vertex_intValue    = Just int   }) = Just $ Single $ I int
decode (Ifaces.Vertex {f_Vertex_boolValue   = Just bool  }) = Just $ Single $ B bool
decode (Ifaces.Vertex {f_Vertex_doubleValue = Just double}) = Just $ Single $ D double
decode (Ifaces.Vertex {f_Vertex_stringValue = Just string}) = Just $ Single $ S string
decode _ = Nothing

encode :: Core.Vertex -> Ifaces.Vertex
encode (Knot      ids'   ) = new {f_Vertex_ids         = Just ids'  }
encode (Single (I int   )) = new {f_Vertex_intValue    = Just int   }
encode (Single (B bool  )) = new {f_Vertex_boolValue   = Just bool  }
encode (Single (D double)) = new {f_Vertex_doubleValue = Just double}
encode (Single (S string)) = new {f_Vertex_stringValue = Just string}

new :: Ifaces.Vertex
new =  Ifaces.Vertex Nothing Nothing Nothing Nothing Nothing
