module Main (main) where

import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Data.List (findIndex, isPrefixOf)
import System.Environment (getArgs)
import System.IO (withFile, IOMode(ReadMode), hGetContents)
import System.FilePath.Posix (takeExtension, takeDirectory)

import Language.EzPSL.Parse (parseModule)
import CompileToTLA (TLACode, ezpsl2tla)
import Misc (join, atomicReplaceFile, relativeTo, die)
import Constants (startOfFileInclude, endOfFileInclude)


data CommandLineOpts = CommandLineOpts {
  showHelp :: Bool,
  inputFile :: Maybe FilePath,
  outputFile :: Maybe FilePath}

parseCommandLineOpts :: [String] -> Either String CommandLineOpts
parseCommandLineOpts = loop defaultOpts
  where
    defaultOpts = CommandLineOpts {
      showHelp = False,
      inputFile = Nothing,
      outputFile = Nothing}

    loop opts [] = Right $ opts
    loop opts ("-h"     : rest) = loop (opts { showHelp = True }) rest
    loop opts ("--help" : rest) = loop (opts { showHelp = True }) rest
    loop opts [f] = Right $ opts { inputFile = Just f }
    loop opts ["--", f] = Right $ opts { inputFile = Just f }
    loop opts ("-o" : out : rest) = loop (opts { outputFile = Just out }) rest
    loop _ (o : _) = Left $ "unexpected option " ++ show o

data SplitResult
  = NoIncludes
  | MultipleIncludes
  | OneInclude String FilePath String

splitTLACode :: String -> SplitResult
splitTLACode code = do
  let ls = lines code
  case [(idx, line) | (idx, line) <- zip [0..] ls, startOfFileInclude `isPrefixOf` line] of
    [] -> NoIncludes
    _ : _ : _ -> MultipleIncludes
    [(idx, m)] -> do
      let fileName = drop (length startOfFileInclude) m
      let rest = drop (idx+1) ls
      let endLine = endOfFileInclude ++ fileName
      case findIndex (== endLine) rest of
        Nothing -> OneInclude (unlines (take (idx+1) ls)) fileName (unlines (endLine : rest))
        Just i -> OneInclude (unlines (take (idx+1) ls)) fileName (unlines (drop i rest))

string2tla :: (MonadFail m) => String -> m TLACode
string2tla s = parseModule s >>= ezpsl2tla

file2tla :: FilePath -> IO TLACode
file2tla fileName = do
  withFile fileName ReadMode (\f -> do
    text <- hGetContents f
    string2tla text)

legalExtensions :: [String]
legalExtensions = ["tla", "ezs"]

badUsage :: String -> String
badUsage message =
  "Incorrect usage: " ++ message ++ ".\n"
  ++ shortUsage ++ "\n"
  ++ "The given FILE must be a .tla or .ezs file."

shortUsage :: String
shortUsage = "Usage: ezpsl [-o OUT] FILE"

fullUsage :: String
fullUsage = join "\n" [
  shortUsage,
  "Options:",
  "  -h,--help    show help and exit without doing anything"]

main :: IO ()
main = do
  args <- getArgs
  case parseCommandLineOpts args of
    Left err -> die 1 (badUsage err)
    Right options -> do

      when (showHelp options) $ do
        die 0 fullUsage

      case inputFile options of
        Nothing -> die 1 (badUsage "No input file provided")
        Just infile -> do
          putStrLn $ "READING " ++ infile
          case takeExtension infile of
            ".tla" -> do
              (originalText, prefix, fileName, suffix) <- withFile infile ReadMode (\f -> do
                text <- hGetContents f
                case splitTLACode text of
                  NoIncludes -> die 0 "No \"\\* #include FILE\" lines were found; doing nothing."
                  MultipleIncludes -> die 2 "Multiple \"\\* #include FILE\" lines were found.  Only one is supported."
                  OneInclude prefix fileName suffix -> return (text, prefix, fileName, suffix)
                )
              let resolvedFileName = fileName `relativeTo` (takeDirectory infile)
              putStrLn $ "READING " ++ resolvedFileName
              compiled <- file2tla resolvedFileName
              let outfile = fromMaybe infile (outputFile options)
              let fullOutput = prefix ++ compiled ++ "\n" ++ suffix
              if fullOutput == originalText
                then putStrLn $ "NO CHANGE"
                else do
                  putStrLn $ "WRITING " ++ outfile
                  atomicReplaceFile outfile fullOutput
            ".ezs" -> do
              compiled <- file2tla infile
              case outputFile options of
                Just outfile -> do
                  putStrLn $ "WRITING " ++ outfile
                  atomicReplaceFile outfile compiled
                Nothing -> do
                  putStrLn "----------"
                  putStrLn compiled
                  putStrLn "----------"
            "" -> die 1 ("Input file has no extension (should be " ++ join " or " legalExtensions ++ ")")
            ext -> die 1 ("Input file has unknown extension " ++ show ext ++ " (should be " ++ join " or " legalExtensions ++ ")")
