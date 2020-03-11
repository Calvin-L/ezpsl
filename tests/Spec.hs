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
    it "has correct associativity for + and *" $ do
      fmap stripLocations (parseExpression "1 + 2 * 3") `shouldBe`
        Right (EBinaryOp () Plus (EInt () 1) (EBinaryOp () Times (EInt () 2) (EInt () 3)))
    it "computes parenthesized expressions first" $ do
      fmap stripLocations (parseExpression "(1 + 2) * 3") `shouldBe`
        Right (EBinaryOp () Times (EBinaryOp () Plus (EInt () 1) (EInt () 2)) (EInt () 3))

stripLocations :: Exp t -> Exp ()
stripLocations = fmap (const ())
