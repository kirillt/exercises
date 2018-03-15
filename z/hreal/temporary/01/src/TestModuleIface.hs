module TestModuleIface where

import CommonIfaces

testingFunction :: FilePath -> IO ()
testingFunction path = load' path "testingFunction"
