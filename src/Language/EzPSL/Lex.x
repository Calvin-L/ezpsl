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

import qualified Data.SourceLocation as Loc
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
       $white+                         ;
       \\\*.*$                         ;
       $digit+                         { makeToken $ \s -> Integer (read s) }
       \"(\\\\|\\\"|\\t|\\n|\\f|\\r|[^\\\"])*\" { makeToken $ \s -> String (read s) }

       \<\<                            { justToken LtLt }
       \>\>                            { justToken GtGt }
       \<\-                            { justToken LtDash }
       \=\>                            { justToken LeftArrow }
       \:\=                            { justToken ColonEquals }
       \=\=                            { justToken EqEq }
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
       DOMAIN                          { justToken Domain }
       UNION                           { justToken Union }
       SUBSET                          { justToken Subset }
       CHOOSE                          { justToken Choose }
       IF                              { justToken IF }
       THEN                            { justToken THEN }
       ELSE                            { justToken ELSE }
       LET                             { justToken LET }
       IN                              { justToken IN }

       var                             { justToken Var }
       proc                            { justToken Proc }
       skip                            { justToken Skip }
       pick                            { justToken Pick }
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
  | Eq | Ne | Lt | Le | Gt | Ge | EqEq
  | Tilde | Wedge | Vee | LeftArrow
  | Plus | Minus | Times | Divide | Percent | Carat
  | ColonEquals | ColonGt | AtAt
  | PipeDashGt
  | SlashOperator String
  -- Other symbols
  | LtDash
  | LtLt | GtGt
  | Comma | Colon | SemiColon | Period | At
  | OpenParen | CloseParen
  | OpenBrace | CloseBrace
  | OpenBracket | CloseBracket
  -- Keywords
  | Self
  | Domain | Union | Subset
  | IF | THEN | ELSE
  | LET | IN
  | Choose
  | Var | Proc
  | Skip
  | Pick
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

getLocation :: AlexInput -> Loc.SourceLocation
getLocation (AlexPn _ l c, _, _, _) = Loc.SourceLocation { Loc.line = l, Loc.column = c }

makeToken :: (String -> Token) -> AlexInput -> Int -> Alex (Token, Loc.SourceLocation)
makeToken f inp@(_, _, _, s) len = return (f (take len s), getLocation inp)

justToken :: Token -> AlexInput -> Int -> Alex (Token, Loc.SourceLocation)
justToken t inp _ = return (t, getLocation inp)

here :: Alex Loc.SourceLocation
here = do
  inp <- alexGetInput
  return $ getLocation inp

-- | Required by the Alex monad wrapper.  (Not mentioned in the docs, tho...)
alexEOF :: Alex (Token, Loc.SourceLocation)
alexEOF = do
  pos <- here
  return (EOF, pos)

nextToken :: Alex (Token, Loc.SourceLocation)
nextToken = alexMonadScan

}
