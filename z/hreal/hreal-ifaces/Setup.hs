import System.Exit
import System.Process
import System.Directory

import Data.List.Split

import Distribution.Simple
import Distribution.PackageDescription (emptyHookedBuildInfo)

main = defaultMainWithHooks $ simpleUserHooks {
    preBuild  = generateCode,
    postBuild = cleanGeneratedCode
}

prefix    = "HReal.Ifaces"

thriftSrc = "thrift"
thriftTmp = "generated"
thriftDst = withoutSlash $ thriftTmp ++ "/" ++ (dirFromPrefix prefix)

dirFromPrefix  = map (\c -> if c == '.' then '/' else c)
withoutSlash s = if (last s) == '/' then (init s) else s

-- converts "Long.Prefix" to "Long\.Prefix"
escapeDots = concat.map (\c -> if c == '.' then '\\':c:[] else c:[])

-- searches for $prompt$name in files and replaces it with $prompt$prefix$name
buildSedCommand dst prefix name prompt = "sed -i 's/" ++ prompt ++ name ++  "/" ++ prompt ++ (escapeDots prefix) ++ "\\." ++ name ++ "/g' " ++ dst ++ "/*"

runCommandAndWait command = do
    process <- runCommand command
    waitForProcess process

appendModulesPrefix dst prefix = do
    putStr $ "Changing generated modules' names with prefix '" ++ prefix ++ "'... "
    dirContent <- getDirectoryContents dst
    let moduleNames = map (\s -> head $ splitOn ['.'] s) $ filter (/=".") $ filter (/="..") dirContent
    mapM (appendModulePrefix dst prefix "import qualified ") moduleNames
    mapM (appendModulePrefix dst prefix "import ") moduleNames
    mapM (appendModulePrefix dst prefix "module ") moduleNames
    -- copy-paste =/
    putStrLn "Done."

appendModulePrefix dst prefix prompt name = do
    let sedCommand = buildSedCommand dst prefix name prompt
    runCommandAndWait sedCommand

runThrift src dst = do
    let filePaths = src ++ "/*.thrift"
    putStr $ "Using thrift files ('" ++ filePaths ++ "') to generate code (destination path is '" ++ dst ++ "')... "
    thrift <- runCommand $ "thrift -gen hs -out " ++ dst ++ " " ++ filePaths
    waitForProcess thrift
    (Just exitCode) <- getProcessExitCode thrift
    if exitCode == ExitSuccess
        then putStrLn "Done."
        else do
            print exitCode
            putStrLn "Maybe, you haven't Thrift installed?"

generateCode _ _ = do
    createDirectoryIfMissing True thriftDst
    runThrift thriftSrc thriftDst
    appendModulesPrefix thriftDst prefix
    return emptyHookedBuildInfo 

cleanGeneratedCode _ _ _ _ = do
    removeDirectoryRecursive thriftTmp
    return ()
