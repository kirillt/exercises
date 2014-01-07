{-# OPTIONS_GHC -O -Wall #-}

module HReal.Server.Interpreter where

import HReal.Core.World
import HReal.Core.History
import Language.Haskell.Interpreter as I

type Modification = History -> Either Constraint World

interpret :: String -> IO (Either InterpreterError Modification)
interpret source = runInterpreter $ do
    setImports [ "Prelude"
               , "Data.Int"
               , "Data.Map"
               , "Data.Set"
               , "HReal.Core.Prelude"
               -- somehow HReal.Core.Prelude isn't enough
               -- TODO: find way to fix it
               , "HReal.Core.World"
               , "HReal.Core.Vertex"
               , "HReal.Core.History" 
               , "HReal.Language.Sugar"]
    I.interpret source (as :: Modification)
