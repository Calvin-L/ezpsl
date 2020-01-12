module Misc where

-- builtin
import Data.List (intercalate)
import System.IO (hPutStr)
import System.Exit (exitWith, ExitCode(ExitFailure))

-- 3rd party
import System.Directory (renamePath)
import System.IO.Temp (withSystemTempFile)
import System.FilePath.Posix (isRelative, joinPath)

join :: String -> [String] -> String
join = intercalate

atomicReplaceFile :: FilePath -> String -> IO ()
atomicReplaceFile filePath newContents = do
  withSystemTempFile "tmp" (\tmpPath handle -> do
    hPutStr handle newContents
    renamePath tmpPath filePath)

relativeTo :: FilePath -> FilePath -> FilePath
relativeTo path directory =
  if isRelative path
    then joinPath [directory, path]
    else path

die :: Int -> String -> IO t
die code message = do
  putStrLn message
  exitWith (ExitFailure code)
