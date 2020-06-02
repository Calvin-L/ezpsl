module Main (main) where

import Control.Monad (forM_)
import Data.List (isSuffixOf, isInfixOf)
import Data.Maybe (catMaybes)
import System.Directory (getDirectoryContents)
import System.IO (withFile, IOMode(WriteMode))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (StdStream(NoStream, UseHandle), CreateProcess(..), createProcess, waitForProcess, proc)

import Test.Hspec (hspec, describe, it, shouldBe, shouldReturn, runIO)

import Language.EzPSL.Syntax
import Language.EzPSL.Parse (parseModule, parseExpression)
import CompileToTLA (ezpsl2tla)

main :: IO ()
main = hspec $ do

  describe "Parsing" $ do
    it "allows multiple strings on one line" $ do
      fmap stripLocations (parseExpression "\"hello\" \\o \"goodbye\"") `shouldBe`
        Right (EBinaryOp () Concat (EStr () "hello") (EStr () "goodbye"))
    it "allows multiple strings in a record definition" $ do
      fmap stripLocations (parseExpression "[id |-> \"id\", status |-> \"new\"]") `shouldBe`
        Right (EMkRecord () [("id", EStr () "id"), ("status", EStr () "new")])
    it "has correct associativity for + and *" $ do
      fmap stripLocations (parseExpression "1 + 2 * 3") `shouldBe`
        Right (EBinaryOp () Plus (EInt () 1) (EBinaryOp () Times (EInt () 2) (EInt () 3)))
    it "computes parenthesized expressions first" $ do
      fmap stripLocations (parseExpression "(1 + 2) * 3") `shouldBe`
        Right (EBinaryOp () Times (EBinaryOp () Plus (EInt () 1) (EInt () 2)) (EInt () 3))

  let dir = "tests/inputs/pass" -- relative to project root
  toCheck <- runIO $ do
    allEntries <- getDirectoryContents dir
    return [f | f <- allEntries, ".ezs" `isSuffixOf` f]
  describe ("Testing files in " ++ dir) $ do
    forM_ toCheck (\fileName -> do
      it ("passes " ++ fileName) $ checkFile (dir ++ "/" ++ fileName) `shouldReturn` True)

  let dir = "tests/inputs/fail-assertion" -- relative to project root
  toCheck <- runIO $ do
    allEntries <- getDirectoryContents dir
    return [f | f <- allEntries, ".ezs" `isSuffixOf` f]
  describe ("Testing files in " ++ dir) $ do
    forM_ toCheck (\fileName -> do
      it ("finds assertion violation in " ++ fileName) $ checkFile (dir ++ "/" ++ fileName) `shouldReturn` False)

stripLocations :: Exp t -> Exp ()
stripLocations = fmap (const ())

parseCFGLine :: String -> Maybe String
parseCFGLine ('\\' : '*' : ' ' : 'C' : 'F' : 'G' : ' ' : line) = Just line
parseCFGLine _ = Nothing

checkFile :: FilePath -> IO Bool
checkFile f = do
  ezpslSource <- readFile f
  ezpslAST <- parseModule ezpslSource
  tlaCode <- ezpsl2tla ezpslAST
  withSystemTempDirectory "ezpsl-test" (\dir -> do
    writeFile (dir ++ "/Test.tla") $ unlines [
      "---- MODULE Test ----",
      "EXTENDS Integers, Sequences, TLC",
      tlaCode,
      "====================="]
    writeFile (dir ++ "/Test.cfg") $ unlines $ [
      "CONSTANT _Undefined = Undefined",
      "INIT Init",
      "NEXT Next",
      "SYMMETRY symmetry",
      "INVARIANT NoAssertionFailures"]
      ++ (catMaybes $ map parseCFGLine $ lines ezpslSource)
    withFile (dir ++ "/log") WriteMode (\logHandle -> do
      (_, _, _, tlc2process) <- createProcess (proc "tlc2" ["Test"]) { cwd = Just dir, std_in = NoStream, std_err = UseHandle logHandle, std_out = UseHandle logHandle }
      _ <- waitForProcess tlc2process
      out <- readFile (dir ++ "/log")
      if "No error has been found" `isInfixOf` out
      then return True
      else if "Invariant NoAssertionFailures is violated" `isInfixOf` out
      then return False
      else error $ "unexpected output from TLC: " ++ out))
