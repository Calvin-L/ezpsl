module Main (main) where

import Test.Hspec (hspec, describe, it, shouldBe)

import Language.EzPSL.Syntax
import Language.EzPSL.Parse (parseExpression)

main :: IO ()
main = hspec $ do

  describe "Parsing" $ do
    it "allows multiple strings on one line" $ do
      fmap stripLocations (parseExpression "\"hello\" \\o \"goodbye\"") `shouldBe`
        Right (EBinaryOp () Concat (EStr () "hello") (EStr () "goodbye"))

stripLocations :: Exp t -> Exp ()
stripLocations = fmap (const ())
