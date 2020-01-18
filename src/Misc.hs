module Misc where

-- builtin
import Data.List (intercalate)
import System.IO (hPutStr)
import System.Exit (exitWith, ExitCode(ExitSuccess, ExitFailure))

-- 3rd party
import System.Directory (renamePath)
import System.IO.Temp (withSystemTempFile)
import System.FilePath.Posix (isRelative, joinPath)


-- | Concatenate a list of strings, putting a copy of the joining string
--   between each one.  This function is exactly equivalent to the
--   absurdly-named standard library function `intercalate`.
join :: String -> [String] -> String
join = intercalate

-- | Atomically replace a file with new contents.  (Pedantic note: the change
--   is not made durable; a subsequent crash can destroy or corrupt the file,
--   even if this procedure returned successfully.)
atomicReplaceFile :: FilePath -> String -> IO ()
atomicReplaceFile filePath newContents = do
  withSystemTempFile "tmp" (\tmpPath handle -> do
    hPutStr handle newContents
    renamePath tmpPath filePath)

-- | Given a path P that should be interpreted relative to some directory D
--   (such as the current working directory), then this function converts P
--   into a path that should be interpreted the same way as D.  For example,
--
--   @
--   "TODO.txt" `relativeTo` "folder"
--   @
--
--   will output "folder/TODO.txt", while
--
--   @
--   "../bin" `relativeTo` "/tmp"
--   @
--
--   will output "/bin" (or something similar).  If P is an absolute path,
--   then this function just returns P.
relativeTo :: FilePath -- ^ The path P
           -> FilePath -- ^ The directory D
           -> FilePath
relativeTo path directory =
  if isRelative path
    then joinPath [directory, path]
    else path

-- | Print the given string, then halt the program with the given exit code.
die :: Int -> String -> IO t
die code message = do
  putStrLn message
  exitWith $ case code of
    0 -> ExitSuccess
    _ -> ExitFailure code

-- | Add copies an element to the front of a list until the list's length is at
--   least the given amount.
pad :: Int -> x -> [x] -> [x]
pad n x l =
  take (n - length l) (repeat x) ++ l
