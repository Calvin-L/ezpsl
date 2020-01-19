{
-- Disable some GHC warnings that catch on the generated code (not my fault!)
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Language.EzPSL.Lex (
  Alex,
  runAlex,
  alexError,
  here,
  Token(..),
  nextToken)
  where

import Data.SourceLocation
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
       $white+                         ;
       \\\*.*$                         ;
       $digit+                         { makeToken $ \s -> Integer (read s) }
       \"(\\\\|\\\"|\\t|\\n|\\f|\\r|[^\\])*\" { makeToken $ \s -> String (read s) }

       \<\<                            { justToken LtLt }
       \>\>                            { justToken GtGt }
       \=\>                            { justToken LeftArrow }
       \:\=                            { justToken ColonEquals }
       \=                              { justToken Eq }
       \/\=                            { justToken Ne }
       \<\=                            { justToken Le }
       \>\=                            { justToken Ge }
       \<                              { justToken Lt }
       \>                              { justToken Gt }
       \~                              { justToken Tilde }
       \/\\                            { justToken Wedge }
       \\\/                            { justToken Vee }
       \+                              { justToken Plus }
       \-                              { justToken Minus }
       \*                              { justToken Times }
       \/                              { justToken Divide }
       \%                              { justToken Percent }
       \^                              { justToken Carat }
       \,                              { justToken Comma }
       \(                              { justToken OpenParen }
       \)                              { justToken CloseParen }
       \{                              { justToken OpenBrace }
       \}                              { justToken CloseBrace }
       \[                              { justToken OpenBracket }
       \]                              { justToken CloseBracket }
       \:\>                            { justToken ColonGt }
       \@\@                            { justToken AtAt }
       \:                              { justToken Colon }
       \;                              { justToken SemiColon }
       \.                              { justToken Period }
       \@                              { justToken At }
       \|\-\>                          { justToken PipeDashGt }
       \\[$alpha]*                     { makeToken $ \s -> SlashOperator (tail s) }

       self                            { justToken Self }
       UNION                           { justToken Union }
       SUBSET                          { justToken Subset }
       CHOOSE                          { justToken Choose }
       IF                              { justToken IF }
       THEN                            { justToken THEN }
       ELSE                            { justToken ELSE }

       var                             { justToken Var }
       proc                            { justToken Proc }
       skip                            { justToken Skip }
       either                          { justToken Either }
       or                              { justToken Or }
       while                           { justToken While }
       await                           { justToken Await }
       assert                          { justToken Assert }
       if                              { justToken If }
       else                            { justToken Else }
       yield                           { justToken Yield }
       call                            { justToken Call }
       return                          { justToken Return }

       [$alpha][$alpha $digit \_]*     { makeToken $ \s -> Identifier s }

{

data Token
  = Identifier String
  | Integer Integer
  | String String
  -- Operators
  | Eq | Ne | Lt | Le | Gt | Ge
  | Tilde | Wedge | Vee | LeftArrow
  | Plus | Minus | Times | Divide | Percent | Carat
  | ColonEquals | ColonGt | AtAt
  | PipeDashGt
  | SlashOperator String
  -- Other symbols
  | LtLt | GtGt
  | Comma | Colon | SemiColon | Period | At
  | OpenParen | CloseParen
  | OpenBrace | CloseBrace
  | OpenBracket | CloseBracket
  -- Keywords
  | Self
  | Union | Subset
  | IF | THEN | ELSE
  | Choose
  | Var | Proc
  | Skip
  | Either | Or
  | While
  | Await
  | Assert
  | If | Else
  | Yield
  | Call
  | Return
  -- | End-of-file token for the parser to use
  | EOF
  deriving (Eq, Show)

makeToken :: (String -> Token) -> AlexInput -> Int -> Alex Token
makeToken f (_, _, _, s) len = return $ f (take len s)

justToken :: Token -> AlexInput -> Int -> Alex Token
justToken t _ _ = return t

here :: Alex SourceLocation
here = do
  (AlexPn _ l c, _, _, _) <- alexGetInput
  return $ SourceLocation { line = l, column = c }

-- | Required by the Alex monad wrapper.  (Not mentioned in the docs, tho...)
alexEOF :: Alex Token
alexEOF = return EOF

nextToken :: Alex Token
nextToken = alexMonadScan

}
