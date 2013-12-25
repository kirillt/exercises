import Incrementor
import Incrementor_Iface
import Interfaces_Types
import Thrift.Server

import Data.Int

instance Incrementor_Iface () where
    inc ()  Nothing   = do
        putStrLn "arg is invalid"
        return 0
    inc () (Just arg) = do
        let res = arg + 1
        putStrLn $ (show arg) ++ " + 1 = " ++ (show res)
        return res

main = runBasicServer () process 7911
