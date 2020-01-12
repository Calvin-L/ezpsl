{
module Language.EzPSL.Parse (parse) where

import Data.SourceLocation (SourceLocation, line, column)
import Language.EzPSL.Syntax
import qualified Language.EzPSL.Lex as Lex
}

%name doParse Program
%tokentype { Lex.Token }
%monad { Lex.Alex }
%error { parseError }
%lexer { (Lex.nextToken >>=) } { Lex.EOF }

%token
    var         { Lex.Identifier $$ }
    int         { Lex.Integer $$ }
    str         { Lex.String $$ }

    '/\\'       { Lex.Wedge }
    '\\/'       { Lex.Vee }
    '->'        { Lex.LeftArrow }
    '='         { Lex.Eq }
    '/='        { Lex.Ne }
    '<'         { Lex.Lt }
    '<='        { Lex.Le }
    '>'         { Lex.Gt }
    '>='        { Lex.Ge }
    '+'         { Lex.Plus }
    '-'         { Lex.Minus }
    '*'         { Lex.Times }
    '/'         { Lex.Divide }
    '~'         { Lex.Tilde }
    '('         { Lex.OpenParen }
    ')'         { Lex.CloseParen }
    '['         { Lex.OpenBracket }
    ']'         { Lex.CloseBracket }
    '{'         { Lex.OpenBrace }
    '}'         { Lex.CloseBrace }
    ':'         { Lex.Colon }
    ';'         { Lex.SemiColon }
    ','         { Lex.Comma }
    '.'         { Lex.Period }
    '%'         { Lex.Percent }
    '^'         { Lex.Carat }
    ':='        { Lex.ColonEquals }
    '@'         { Lex.At }
    '|->'       { Lex.PipeDashGt }

    'self'      { Lex.Self }
    'var'       { Lex.Var }
    'proc'      { Lex.Proc }
    'skip'      { Lex.Skip }
    'either'    { Lex.Either }
    'or'        { Lex.Or }
    'while'     { Lex.While }
    'await'     { Lex.Await }
    'assert'    { Lex.Assert }
    'if'        { Lex.If }
    'else'      { Lex.Else }
    'yield'     { Lex.Yield }
    'call'      { Lex.Call }
    'return'    { Lex.Return }

%left 'exists' 'forall' ','
%left 'then' 'else'
%right '->'
%left '\\/'
%left '/\\'
%left '=' '/=' '<' '>' '>=' '<='
%left '+' '-'
%left '*' '/' '%'
%left '^'
%left '~'
%left '['
%left '.'

%%

Program :: { Module SourceLocation }
  : VarDecls Procedures {% withPosition (\pos -> Module pos $1 $2) }

VarDecls :: { [VarDecl SourceLocation] }
  : { [] }
  | VarDecl VarDecls { $1 : $2 }

VarDecl :: { VarDecl SourceLocation }
  : 'var' var '=' Exp ';' {% withPosition (\pos -> VarDecl pos $2 $4) }

Exp :: { Exp SourceLocation }
  : int             {% withPosition (\pos -> EInt pos $1) }
  | str             {% withPosition (\pos -> EStr pos $1) }
  | var             {% withPosition (\pos -> EVar pos $1) }
  | 'self'          {% withPosition EThreadID }
  | Exp '<'   Exp   {% withPosition (\pos -> EBinaryOp pos Lt $1 $3) }
  | Exp '>'   Exp   {% withPosition (\pos -> EBinaryOp pos Gt $1 $3) }
  | Exp '<='  Exp   {% withPosition (\pos -> EBinaryOp pos Le $1 $3) }
  | Exp '>='  Exp   {% withPosition (\pos -> EBinaryOp pos Ge $1 $3) }
  | Exp '='   Exp   {% withPosition (\pos -> EBinaryOp pos Eq $1 $3) }
  | Exp '/='  Exp   {% withPosition (\pos -> EBinaryOp pos Ne $1 $3) }
  | Exp '+'   Exp   {% withPosition (\pos -> EBinaryOp pos Plus $1 $3) }
  | Exp '-'   Exp   {% withPosition (\pos -> EBinaryOp pos Minus $1 $3) }
  | Exp '*'   Exp   {% withPosition (\pos -> EBinaryOp pos Times $1 $3) }
  | Exp '/'   Exp   {% withPosition (\pos -> EBinaryOp pos Divide $1 $3) }
  | Exp '%'   Exp   {% withPosition (\pos -> EBinaryOp pos Mod $1 $3) }
  | Exp '^'   Exp   {% withPosition (\pos -> EBinaryOp pos Exp $1 $3) }
  | Exp '/\\' Exp   {% withPosition (\pos -> EBinaryOp pos And $1 $3) }
  | Exp '\\/' Exp   {% withPosition (\pos -> EBinaryOp pos Or $1 $3) }
  | Exp '->'  Exp   {% withPosition (\pos -> EBinaryOp pos Implies $1 $3) }
  | '~' Exp         {% withPosition (\pos -> EUnaryOp pos Not $2)}
  | Exp '.' var     {% withPosition (\pos -> EGetField pos $1 $3)}
  | Exp '[' Exp ']' {% withPosition (\pos -> EIndex pos $1 $3)}
  | '[' Fields ']'  {% withPosition (\pos -> EMkRecord pos $2) }
  | '(' Exp ')'     {  $2 }

ExpList :: { [Exp SourceLocation] }
  :          { [] }
  | ExpList1 { $1 }

ExpList1 :: { [Exp SourceLocation] }
  : Exp              { [$1] }
  | Exp ',' ExpList1 { $1 : $3 }

Fields :: { [(FieldName, Exp SourceLocation)] }
  :         { [] }
  | Fields1 { $1 }

Fields1 :: { [(FieldName, Exp SourceLocation)] }
  : Field             { [$1] }
  | Field ',' Fields1 { $1 : $3 }

Field :: { (FieldName, Exp SourceLocation) }
  : var '|->' Exp { ($1, $3) }

Procedures :: { [Procedure SourceLocation] }
  : { [] }
  | Procedure Procedures { $1 : $2 }

Procedure :: { Procedure SourceLocation }
  : Annotations 'proc' var '(' Params ')' '{' VarDecls MaybeStm '}' {% withPosition (\pos -> Procedure pos $1 $3 $5 $8 $9) }

Annotations :: { [Annotation] }
  :                        { [] }
  | Annotation Annotations { $1 : $2 }

Annotation :: { Annotation }
  : '@' var {% case $2 of {
    "entry" -> withPosition (const EntryPoint);
    a -> reportError $ "Illegal annotation " ++ show a ++ "; the only legal choice is \"@entry\"" } }

Params :: { [Id] }
  : { [] }
  | Params1 { $1 }

Params1 :: { [Id] }
  : var             { [$1] }
  | var ',' Params1 { $1 : $3 }

LValue :: { LValue SourceLocation }
  : var                {% withPosition (\pos -> LVar pos $1) }
  | LValue '[' Exp ']' {% withPosition (\pos -> LIndex pos $1 $3) }
  | LValue '.' var     {% withPosition (\pos -> LField pos $1 $3) }

Stm :: { Stm SourceLocation }
  : BasicStm     {  $1 }
  | BasicStm Stm {% withPosition (\pos -> Seq pos $1 $2) }

BasicStm :: { Stm SourceLocation }
  : LValue ':=' Exp ';'                        {% withPosition (\pos -> Assign pos $1 $3) }
  | 'if' '(' Exp ')' Block ElseClauses         {% withPosition (\pos -> If pos $3 $5 $6) }
  | 'either' Block OrClauses1                  {% withPosition (\pos -> Either pos ($2 : $3)) }
  | 'await' Exp ';'                            {% withPosition (\pos -> Await pos $2) }
  | 'assert' Exp ';'                           {% withPosition (\pos -> Assert pos $2) }
  | 'skip' ';'                                 {% withPosition Skip }
  | 'yield' ';'                                {% withPosition Yield }
  | 'call' var '(' ExpList ')' ';'             {% withPosition (\pos -> Call pos $2 $4) }
  | LValue ':=' 'call' var '(' ExpList ')' ';' {% withPosition (\pos -> CallAndSaveReturnValue pos $1 $4 $6) }
  | 'return' ';'                               {% withPosition (\pos -> Return pos Nothing) }
  | 'return' Exp ';'                           {% withPosition (\pos -> Return pos (Just $2)) }
  | 'while' '(' Exp ')' Block                  {% withPosition (\pos -> While pos $3 $5) }

MaybeStm :: { Stm SourceLocation }
  :     {% withPosition Skip }
  | Stm {  $1 }

Block :: { Stm SourceLocation }
  : '{' MaybeStm '}' { $2 }

OrClauses1 :: { [Stm SourceLocation] }
  : OrClause            { [$1] }
  | OrClause OrClauses1 { $1 : $2 }

OrClause :: { Stm SourceLocation }
  : 'or' Block { $2 }

ElseClauses :: { Stm SourceLocation }
  :                                           {% withPosition Skip }
  | 'else' Block                              { $2 }
  | 'else' 'if' '(' Exp ')' Block ElseClauses {% withPosition (\pos -> If pos $4 $6 $7) }

{

withPosition :: (SourceLocation -> t) -> Lex.Alex t
withPosition f = do
  pos <- Lex.here
  return $ f pos

reportError :: String -> Lex.Alex a
reportError msg = do
  pos <- Lex.here
  Lex.alexError $ "Parse error at line " ++ (show $ line pos) ++ ", column " ++ (show $ column pos) ++ ": " ++ msg

parseError :: Lex.Token -> Lex.Alex a
parseError token = reportError $ "unexpected " ++ show token

parse :: String -> Either String (Module SourceLocation)
parse s = Lex.runAlex s doParse

}
