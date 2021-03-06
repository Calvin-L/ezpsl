{
module Language.EzPSL.Parse (parseModule, parseExpression) where

import qualified Data.Map as M

import Data.Annotated (getAnnotation)
import Data.SourceLocation (SourceLocation, line, column)
import Language.EzPSL.Syntax
import qualified Language.EzPSL.Lex as Lex
import Misc (join)
}

%name doParseModule Program
%name doParseExpression Exp
%tokentype { (Lex.Token, SourceLocation) }
%monad { Lex.Alex }
%error { parseError }
%lexer { (Lex.nextToken >>=) } { (Lex.EOF, _) }

%token
    var           { (Lex.Identifier _, _) }
    int           { (Lex.Integer _, _) }
    str           { (Lex.String _, _) }

    '<<'          { (Lex.LtLt, _) }
    '>>'          { (Lex.GtGt, _) }
    '/\\'         { (Lex.Wedge, _) }
    '\\/'         { (Lex.Vee, _) }
    '<-'          { (Lex.LtDash, _) }
    '=>'          { (Lex.LeftArrow, _) }
    '='           { (Lex.Eq, _) }
    '/='          { (Lex.Ne, _) }
    '<'           { (Lex.Lt, _) }
    '<='          { (Lex.Le, _) }
    '>'           { (Lex.Gt, _) }
    '>='          { (Lex.Ge, _) }
    '=='          { (Lex.EqEq, _) }
    '+'           { (Lex.Plus, _) }
    '-'           { (Lex.Minus, _) }
    '*'           { (Lex.Times, _) }
    '/'           { (Lex.Divide, _) }
    '~'           { (Lex.Tilde, _) }
    '('           { (Lex.OpenParen, _) }
    ')'           { (Lex.CloseParen, _) }
    '['           { (Lex.OpenBracket, _) }
    ']'           { (Lex.CloseBracket, _) }
    '{'           { (Lex.OpenBrace, _) }
    '}'           { (Lex.CloseBrace, _) }
    ':'           { (Lex.Colon, _) }
    ';'           { (Lex.SemiColon, _) }
    ','           { (Lex.Comma, _) }
    '.'           { (Lex.Period, _) }
    '%'           { (Lex.Percent, _) }
    '^'           { (Lex.Carat, _) }
    ':='          { (Lex.ColonEquals, _) }
    '@'           { (Lex.At, _) }
    '|->'         { (Lex.PipeDashGt, _) }
    '\\o'         { (Lex.SlashOperator "o", _) }
    '\\in'        { (Lex.SlashOperator "in", _) }
    '\\notin'     { (Lex.SlashOperator "notin", _) }
    '\\subseteq'  { (Lex.SlashOperator "subseteq", _) }
    '\\union'     { (Lex.SlashOperator "union", _) }
    '\\intersect' { (Lex.SlashOperator "intersect", _) }
    '\\'          { (Lex.SlashOperator "", _) }
    ':>'          { (Lex.ColonGt, _) }
    '@@'          { (Lex.AtAt, _) }
    '\\E'         { (Lex.SlashOperator "E", _) }
    '\\A'         { (Lex.SlashOperator "A", _) }

    'self'        { (Lex.Self, _) }
    'DOMAIN'      { (Lex.Domain, _) }
    'UNION'       { (Lex.Union, _) }
    'SUBSET'      { (Lex.Subset, _) }
    'CHOOSE'      { (Lex.Choose, _) }
    'IF'          { (Lex.IF, _) }
    'THEN'        { (Lex.THEN, _) }
    'ELSE'        { (Lex.ELSE, _) }
    'LET'         { (Lex.LET, _) }
    'IN'          { (Lex.IN, _) }

    'var'         { (Lex.Var, _) }
    'proc'        { (Lex.Proc, _) }
    'pick'        { (Lex.Pick, _) }
    'skip'        { (Lex.Skip, _) }
    'either'      { (Lex.Either, _) }
    'or'          { (Lex.Or, _) }
    'while'       { (Lex.While, _) }
    'await'       { (Lex.Await, _) }
    'assert'      { (Lex.Assert, _) }
    'if'          { (Lex.If, _) }
    'else'        { (Lex.Else, _) }
    'yield'       { (Lex.Yield, _) }
    'call'        { (Lex.Call, _) }
    'return'      { (Lex.Return, _) }

%left ':' '<-' 'IN'
%left '\\E' '\\A' ','
%left 'THEN' 'ELSE'
%right '=>'
%left '\\/'
%left '/\\'
%left '=' '/=' '<' '>' '>=' '<='
%left '\\in' '\\notin'
%left '\\subseteq'
%left '@@'
%left ':>'
%left '\\union' '\\intersect' '\\'
%left '+' '-'
%left '*' '/' '%'
%left '^'
%left '\\o'
%left '~' '-' 'UNION' 'SUBSET' 'DOMAIN'
%left '['
%left '.'

%%

Program :: { Module SourceLocation }
  : VarDecls Procedures {% withPosition (\pos -> Module pos $1 $2) }

VarDecls :: { [VarDecl SourceLocation] }
  : { [] }
  | VarDecl VarDecls { $1 : $2 }

VarDecl :: { VarDecl SourceLocation }
  : 'var' Var ':=' Exp ';' { VarDecl (tokenLocation $1) (fst $2) $4 }
  | 'var' Var NondeterministicAssignOperator Exp ';' { VarDeclNondeterministic (tokenLocation $1) (fst $2) $3 $4 }

Var :: { (Id, SourceLocation) }
  : var { case $1 of { (Lex.Identifier x, loc) -> (x, loc); _ -> error "impossible" } }

Int :: { (Integer, SourceLocation) }
  : int { case $1 of { (Lex.Integer x, loc) -> (x, loc); _ -> error "impossible" } }

StringLiteral :: { (String, SourceLocation) }
  : str { case $1 of { (Lex.String x, loc) -> (x, loc); _ -> error "impossible" } }

Exp :: { Exp SourceLocation }
  : Int                              { EInt (snd $1) (fst $1) }
  | StringLiteral                    { EStr (snd $1) (fst $1) }
  | Var MaybeArgs                    { case $2 of { Nothing -> EVar (snd $1) (fst $1); Just args -> ECall (snd $1) (fst $1) args } }
  | 'self'                           { EThreadID (tokenLocation $1) }
  | Exp '<'   Exp                    { EBinaryOp (tokenLocation $2) Lt $1 $3 }
  | Exp '>'   Exp                    { EBinaryOp (tokenLocation $2) Gt $1 $3 }
  | Exp '<='  Exp                    { EBinaryOp (tokenLocation $2) Le $1 $3 }
  | Exp '>='  Exp                    { EBinaryOp (tokenLocation $2) Ge $1 $3 }
  | Exp '='   Exp                    { EBinaryOp (tokenLocation $2) Eq $1 $3 }
  | Exp '/='  Exp                    { EBinaryOp (tokenLocation $2) Ne $1 $3 }
  | Exp '+'   Exp                    { EBinaryOp (tokenLocation $2) Plus $1 $3 }
  | Exp '-'   Exp                    { EBinaryOp (tokenLocation $2) Minus $1 $3 }
  | Exp '*'   Exp                    { EBinaryOp (tokenLocation $2) Times $1 $3 }
  | Exp '/'   Exp                    { EBinaryOp (tokenLocation $2) Divide $1 $3 }
  | Exp '%'   Exp                    { EBinaryOp (tokenLocation $2) Mod $1 $3 }
  | Exp '^'   Exp                    { EBinaryOp (tokenLocation $2) Exp $1 $3 }
  | Exp '/\\' Exp                    { EBinaryOp (tokenLocation $2) And $1 $3 }
  | Exp '\\/' Exp                    { EBinaryOp (tokenLocation $2) Or $1 $3 }
  | Exp '=>'  Exp                    { EBinaryOp (tokenLocation $2) Implies $1 $3 }
  | Exp '\\o'  Exp                   { EBinaryOp (tokenLocation $2) Concat $1 $3 }
  | Exp '\\in'  Exp                  { EBinaryOp (tokenLocation $2) In $1 $3 }
  | Exp '\\notin' Exp                { EUnaryOp (tokenLocation $2) Not (EBinaryOp (tokenLocation $2) In $1 $3) }
  | Exp '\\subseteq'  Exp            { EBinaryOp (tokenLocation $2) Subset $1 $3 }
  | Exp '\\union'  Exp               { EBinaryOp (tokenLocation $2) Union $1 $3 }
  | Exp '\\intersect'  Exp           { EBinaryOp (tokenLocation $2) Intersection $1 $3 }
  | Exp '\\'  Exp                    { EBinaryOp (tokenLocation $2) SetDifference $1 $3 }
  | Exp ':>'  Exp                    { EBinaryOp (tokenLocation $2) SingletonMapping $1 $3 }
  | Exp '@@'  Exp                    { EBinaryOp (tokenLocation $2) LeftBiasedMapUnion $1 $3 }
  | '~' Exp                          { EUnaryOp (tokenLocation $1) Not $2 }
  | '-' Exp                          { EUnaryOp (tokenLocation $1) Negate $2 }
  | 'DOMAIN' Exp                     { EUnaryOp (tokenLocation $1) Domain $2 }
  | 'UNION' Exp                      { EUnaryOp (tokenLocation $1) UnionAll $2 }
  | 'SUBSET' Exp                     { EUnaryOp (tokenLocation $1) AllSubsets $2 }
  | Exp '.' Var                      { EGetField (tokenLocation $2) $1 (fst $3) }
  | Exp '[' Exp ']'                  { EIndex (tokenLocation $2) $1 $3 }
  | '{' ExpList '}'                  { EMkSet (tokenLocation $1) $2 }
  | '{' Exp ':' SetCmpClauses1 '}'   { ESetComprehension (tokenLocation $1) $2 $4 }
  | '<<' ExpList '>>'                { EMkTuple (tokenLocation $1) $2 }
  | '[' Fields ']'                   { EMkRecord (tokenLocation $1) $2 }
  | '[' Var '\\in' Exp '|->' Exp ']' { EMkFunc (tokenLocation $1) (fst $2) $4 $6 }
  | '\\E'    Var '\\in' Exp ':' Exp  { EQuant (tokenLocation $1) Exists (fst $2) $4 $6 }
  | '\\A'    Var '\\in' Exp ':' Exp  { EQuant (tokenLocation $1) Forall (fst $2) $4 $6 }
  | 'CHOOSE' Var '\\in' Exp ':' Exp  { EQuant (tokenLocation $1) Choose (fst $2) $4 $6 }
  | 'LET' Var '==' Exp 'IN' Exp      { EQuant (tokenLocation $1) LetIn  (fst $2) $4 $6 }
  | 'IF' Exp 'THEN' Exp 'ELSE' Exp   { ECond (tokenLocation $1) $2 $4 $6 }
  | '(' Exp ')'                      { $2 }

MaybeArgs :: { Maybe [Exp SourceLocation] }
  :      { Nothing }
  | Args { Just $1 }

Args :: { [Exp SourceLocation] }
  : '(' ExpList ')' { $2 }

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
  : Var '|->' Exp { (fst $1, $3) }

SetCmpClauses1 :: { [SetComprehensionClause SourceLocation] }
  : SetCmpClause                    { [$1] }
  | SetCmpClause ',' SetCmpClauses1 { $1 : $3 }

SetCmpClause :: { SetComprehensionClause SourceLocation }
  : Var '<-' Exp { SCMember (tokenLocation $2) (fst $1) $3 }
  | Exp          { SCFilter (getAnnotation $1) $1 }

Procedures :: { [Procedure SourceLocation] }
  : { [] }
  | Procedure Procedures { $1 : $2 }

Procedure :: { Procedure SourceLocation }
  : Annotations 'proc' Var '(' Params ')' '{' VarDecls MaybeStm '}' { Procedure (tokenLocation $2) $1 (fst $3) $5 $8 $9 }

Annotations :: { [Annotation] }
  :                        { [] }
  | Annotation Annotations { $1 : $2 }

Annotation :: { Annotation }
  : '@' Var {% case M.lookup (fst $2) annotationsByName of {
    Just a -> return a;
    Nothing -> reportError (snd $2) $ "Illegal annotation " ++ show (fst $2) ++ "; all supported annotations: " ++ join ", " ['@' : a | a <- M.keys annotationsByName] } }

Params :: { [Id] }
  : { [] }
  | Params1 { $1 }

Params1 :: { [Id] }
  : Var             { [fst $1] }
  | Var ',' Params1 { fst $1 : $3 }

NondeterministicAssignOperator :: { NondeterministicAssignOperator }
  : '\\in'       { MemberOf }
  | '\\subseteq' { SubsetOf }

LValue :: { LValue SourceLocation }
  : Var                { LVar (snd $1) (fst $1) }
  | LValue '[' Exp ']' { LIndex (tokenLocation $2) $1 $3 }
  | LValue '.' Var     { LField (tokenLocation $2) $1 (fst $3) }

Stm :: { Stm SourceLocation }
  : BasicStm     {  $1 }
  | BasicStm Stm { Seq (getAnnotation $1) $1 $2 }

BasicStm :: { Stm SourceLocation }
  : LValue ':=' Exp ';'                        { Assign (tokenLocation $2) $1 $3 }
  | 'if' '(' Exp ')' Block ElseClauses         { If (tokenLocation $1) $3 $5 $6 }
  | 'either' Block OrClauses1                  { Either (tokenLocation $1) ($2 : $3) }
  | 'await' Exp ';'                            { Await (tokenLocation $1) $2 }
  | 'assert' Exp ';'                           { Assert (tokenLocation $1) $2 }
  | 'skip' ';'                                 { Skip (tokenLocation $1) }
  | 'yield' ';'                                { Yield (tokenLocation $1) }
  | 'call' Var Args ';'                        { Call (tokenLocation $1) (fst $2) $3 }
  | LValue ':=' 'call' Var Args ';'            { CallAndSaveReturnValue (tokenLocation $2) $1 (fst $4) $5 }
  | 'pick' LValue NondeterministicAssignOperator Exp MaybePredicate ';' { NondeterministicAssign (tokenLocation $1) $2 $3 $4 $5 }
  | 'return' ';'                               { Return (tokenLocation $1) Nothing }
  | 'return' Exp ';'                           { Return (tokenLocation $1) (Just $2) }
  | 'while' '(' Exp ')' Block                  { While (tokenLocation $1) $3 $5 }

MaybePredicate :: { Exp SourceLocation }
  :         {% withPosition (\loc -> EBool loc True) }
  | ':' Exp {  $2 }

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
  | 'else' 'if' '(' Exp ')' Block ElseClauses { If (tokenLocation $2) $4 $6 $7 }

{

annotationsByName :: M.Map String Annotation
annotationsByName = M.fromList [
  ("entry", EntryPoint),
  ("can_restart", CanRestart)]

tokenLocation :: (Lex.Token, SourceLocation) -> SourceLocation
tokenLocation = snd

withPosition :: (SourceLocation -> t) -> Lex.Alex t
withPosition f = do
  pos <- Lex.here
  return $ f pos

reportError :: SourceLocation -> String -> Lex.Alex a
reportError pos msg = do
  Lex.alexError $ "Parse error at line " ++ (show $ line pos) ++ ", column " ++ (show $ column pos) ++ ": " ++ msg

parseError :: (Lex.Token, SourceLocation) -> Lex.Alex a
parseError (Lex.EqEq, pos) = reportError pos $ "unexpected == (reminder: use = for equality comparison, not ==)"
parseError (token, pos) = reportError pos $ "unexpected " ++ show token

parseModule :: (MonadFail m) => String -> m (Module SourceLocation)
parseModule s =
  case Lex.runAlex s doParseModule of
    Left err -> fail err
    Right out -> return out

parseExpression :: String -> Either String (Exp SourceLocation)
parseExpression s = Lex.runAlex s doParseExpression

}
