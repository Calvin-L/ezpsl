module CompileToTLA (TLACode, ezpsl2tla) where

import Data.Maybe (catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char (isAlpha)

import Data.Annotated (Annotated, getAnnotation)
import Data.SourceLocation (SourceLocation(SourceLocation), line, column)
import Language.EzPSL.Syntax
import Names (NamesOp, runNamesOp, freshName)
import Constants (pcVar, framesVar, retVar, actorVar, selfConstant, undefinedConstant)
import Misc (join, pad)


ezpsl2tla :: Module SourceLocation -> Either String TLACode
ezpsl2tla m@(Module _ vars procs) = do
  let env = mkEnv m
  let entryProcedureNames = S.toList (namesOfEntryProcedures procs)
  case entryProcedureNames of
    [] -> Left "The program contains no entry points.  Annotate at least one procedure with \"@entry\"."
    _ -> do
      initialValues <- mapM (\(VarDecl _ v e) -> exp2tla (M.empty) e) vars
      let {(bigCfg, procedureEntryLabels, transitions) = runNamesOp $ do
        cfgsAndLabels <- mapM (toCfg env) procs
        let bigCfg = M.unions $ map fst cfgsAndLabels
        transitions <- mapM (uncurry convertTransition) (M.toList bigCfg)
        return (bigCfg, map snd cfgsAndLabels, transitions)}
      let pidSets = [p ++ "_calls" | p <- entryProcedureNames]
      let allVars = pcVar : framesVar : retVar : actorVar : [v | VarDecl _ v _ <- vars]
      return $ join "\n" $ [
        "CONSTANTS " ++ join ", " (undefinedConstant : pidSets),
        "VARIABLES " ++ join ", " allVars,
        "vars == <<" ++ join ", " allVars ++ ">>",
        "symmetry == UNION {" ++ join ", " ["Permutations(" ++ p ++ ")" | p <- pidSets] ++ "}",
        "Init =="]
        ++ ["  /\\ " ++ pcVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ "_calls |-> <<" ++ show (entryLabel p) ++ ">>]" | p <- entryProcedureNames]]
        ++ ["  /\\ " ++ framesVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ " |-> << <<>> >>]" | p <- pidSets]]
        ++ ["  /\\ " ++ retVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ " |-> " ++ undefinedConstant ++ "]" | p <- pidSets]]
        ++ ["  /\\ " ++ actorVar ++ " = " ++ undefinedConstant]
        ++ ["  /\\ " ++ v ++ " = " ++ init | (VarDecl _ v _, init) <- zip vars initialValues]
        ++ transitions
        ++ ["_halt(" ++ selfConstant ++ ") ==",
            "  /\\ " ++ pcVar ++ "[" ++ selfConstant ++ "] = <<>>",
            "  /\\ " ++ actorVar ++ " = " ++ selfConstant ++ "",
            "  /\\ " ++ actorVar ++ "' = _Undefined",
            "  /\\ " ++ retVar ++ "' = [" ++ retVar ++ " EXCEPT ![" ++ selfConstant ++ "] = _Undefined]",
            "  /\\ UNCHANGED " ++ framesVar,
            "  /\\ UNCHANGED " ++ pcVar]
        ++ ["  /\\ UNCHANGED " ++ v | VarDecl _ v _ <- vars]
        ++ ["\\* `_finished` prevents TLC from reporting deadlock when all processes finish normally"]
        ++ ["_finished ==",
            "  /\\ \\A " ++ selfConstant ++ " \\in UNION {" ++ join ", " pidSets ++ "}: " ++ pcVar ++ "[" ++ selfConstant ++ "] = <<>>",
            "  /\\ UNCHANGED <<" ++ join ", " allVars ++ ">>"]
        ++ ["Next ==", "  \\E _pid \\in UNION {" ++ join ", " pidSets ++ "}:"]
        ++ ["    \\/ " ++ label ++ "(_pid)" | (label, _) <- M.toList bigCfg]
        ++ ["    \\/ _halt(_pid)"]
        ++ ["    \\/ _finished"]

namesOfEntryProcedures :: [Procedure a] -> S.Set Id
namesOfEntryProcedures = (S.fromList) . catMaybes . (map asEntryPoint)
  where
    asEntryPoint :: Procedure a -> Maybe Id
    asEntryPoint p
      | EntryPoint `elem` (procedureAnnotations p) = Just (procedureName p)
      | otherwise = Nothing

type TLACode = String

data Kind
  = KPerProcessVar
  | KProcedureLocalVar
  | KGlobalVar
  | KProcedure [Id]
  deriving (Eq)

type KEnv = M.Map Id Kind
type Env = M.Map Id TLACode

errorAt :: (Monad m, Annotated loc) => loc SourceLocation -> String -> m t
errorAt e message = do
  let loc = getAnnotation e
  fail $ "At line " ++ show (line loc) ++ ", column " ++ show (column loc) ++ ": " ++ message

compileBinaryOp :: BinaryOp -> TLACode -> TLACode -> TLACode
compileBinaryOp Plus               e1 e2 = e1 ++ " + "          ++ e2
compileBinaryOp Minus              e1 e2 = e1 ++ " - "          ++ e2
compileBinaryOp Times              e1 e2 = e1 ++ " * "          ++ e2
compileBinaryOp Divide             e1 e2 = e1 ++ " \\div "      ++ e2
compileBinaryOp Mod                e1 e2 = e1 ++ " % "          ++ e2
compileBinaryOp Exp                e1 e2 = e1 ++ " ^ "          ++ e2
compileBinaryOp Or                 e1 e2 = e1 ++ " \\/ "        ++ e2
compileBinaryOp And                e1 e2 = e1 ++ " /\\ "        ++ e2
compileBinaryOp Implies            e1 e2 = e1 ++ " => "         ++ e2
compileBinaryOp Eq                 e1 e2 = e1 ++ " = "          ++ e2
compileBinaryOp Ne                 e1 e2 = e1 ++ " /= "         ++ e2
compileBinaryOp Gt                 e1 e2 = e1 ++ " > "          ++ e2
compileBinaryOp Ge                 e1 e2 = e1 ++ " >= "         ++ e2
compileBinaryOp Lt                 e1 e2 = e1 ++ " < "          ++ e2
compileBinaryOp Le                 e1 e2 = e1 ++ " <= "         ++ e2
compileBinaryOp Concat             e1 e2 = e1 ++ " \\o "        ++ e2
compileBinaryOp In                 e1 e2 = e1 ++ " \\in "       ++ e2
compileBinaryOp Subset             e1 e2 = e1 ++ " \\subseteq " ++ e2
compileBinaryOp Union              e1 e2 = e1 ++ " \\union "    ++ e2
compileBinaryOp Intersection       e1 e2 = e1 ++ " \\intersect" ++ e2
compileBinaryOp SetDifference      e1 e2 = e1 ++ " \\ "         ++ e2
compileBinaryOp SingletonMapping   e1 e2 = e1 ++ " :> "         ++ e2
compileBinaryOp LeftBiasedMapUnion e1 e2 = e1 ++ " @@ "         ++ e2

transformBottomUp :: (Monad m, Show a) => (Exp a -> m (Exp a)) -> Exp a -> m (Exp a)
transformBottomUp f e@(EInt _ _) = f e
transformBottomUp f e@(EStr _ _) = f e
transformBottomUp f e@(EVar _ _) = f e
transformBottomUp f e@(EThreadID _) = f e
transformBottomUp f (EUnaryOp loc op e) = do
  e' <- transformBottomUp f e
  f (EUnaryOp loc op e')
transformBottomUp f (EBinaryOp loc op e1 e2) = do
  e1' <- transformBottomUp f e1
  e2' <- transformBottomUp f e2
  f (EBinaryOp loc op e1' e2')
transformBottomUp f (EIndex loc e1 e2) = do
  e1' <- transformBottomUp f e1
  e2' <- transformBottomUp f e2
  f (EIndex loc e1' e2')
transformBottomUp f (EGetField loc e field) = do
  e' <- transformBottomUp f e
  f (EGetField loc e' field)
transformBottomUp f (ECall loc func args) = do
  args' <- mapM (transformBottomUp f) args
  f (ECall loc func args')
transformBottomUp f (EMkTuple loc args) = do
  args' <- mapM (transformBottomUp f) args
  f (EMkTuple loc args')
transformBottomUp f (EMkSet loc args) = do
  args' <- mapM (transformBottomUp f) args
  f (EMkSet loc args')
transformBottomUp f (EMkRecord loc fields) = do
  fields' <- mapM (\(fieldName, e) -> do
    e' <- transformBottomUp f e
    return (fieldName, e')) fields
  f (EMkRecord loc fields')
transformBottomUp f (ECond loc cond thenCase elseCase) = do
  cond' <- transformBottomUp f cond
  thenCase' <- transformBottomUp f thenCase
  elseCase' <- transformBottomUp f elseCase
  f (ECond loc cond' thenCase' elseCase')
transformBottomUp f (EMkFunc loc param domain range) = do
  domain' <- transformBottomUp f domain
  range' <- transformBottomUp f range
  f (EMkFunc loc param domain' range')
transformBottomUp f (EExcept loc func inputValueToOverride newOutputValue) = do
  func' <- transformBottomUp f func
  inputValueToOverride' <- transformBottomUp f inputValueToOverride
  newOutputValue' <- transformBottomUp f newOutputValue
  f (EExcept loc func inputValueToOverride newOutputValue)
transformBottomUp f (EQuant loc q arg domain predicate) = do
  domain' <- transformBottomUp f domain
  predicate' <- transformBottomUp f predicate
  f (EQuant loc q arg domain' predicate')

fixReads :: (Monad m) => KEnv -> Exp SourceLocation -> m (Exp SourceLocation)
fixReads kenv =
  transformBottomUp (\e ->
    case e of
      EVar a v ->
        case M.lookup v kenv of
          Just KPerProcessVar -> do
            return $ EIndex a e (EThreadID a)
          Just KProcedureLocalVar -> do
            let myFrames = EIndex a (EVar a framesVar) (EThreadID a)
            return $ EGetField a (EIndex a myFrames (ECall a "Len" [myFrames])) v
          _ -> return e
      _ -> return e)

exp2tla :: (Monad m) => Env -> Exp SourceLocation -> m TLACode
exp2tla _ (EInt _ i) = return (show i)
exp2tla _ (EStr _ s) = return (show s)
exp2tla env e@(EVar _ v) =
  case M.lookup v env of
    Nothing -> return v
    Just v' -> return v'
exp2tla env (EThreadID _) =
  return selfConstant
exp2tla env (EMkSet _ es) = do
  es' <- mapM (exp2tla env) es
  return $ "{" ++ join ", " es' ++ "}"
exp2tla env (EMkTuple _ es) = do
  es' <- mapM (exp2tla env) es
  return $ "<<" ++ join ", " es' ++ ">>"
exp2tla env (EMkRecord loc []) = do
  exp2tla env (EMkTuple loc [])
exp2tla env (EMkRecord loc fields) = do
  fields' <- mapM (\(fieldName, fieldValue) -> do
    fieldValue' <- exp2tla env fieldValue
    return (fieldName, fieldValue')) fields
  return $ "[" ++ join ", " [fieldName ++ " |-> " ++ fieldValue | (fieldName, fieldValue) <- fields'] ++ "]"
exp2tla env (EUnaryOp _ op e) = do
  e' <- exp2tla env e
  case op of
    Not -> return $ "~" ++ e'
    Negate -> return $ "-" ++ e'
    UnionAll -> return $ "(UNION " ++ e' ++ ")"
    AllSubsets -> return $ "(SUBSET " ++ e' ++ ")"
exp2tla env (EBinaryOp _ op e1 e2) = do
  e1' <- exp2tla env e1
  e2' <- exp2tla env e2
  return $ "(" ++ compileBinaryOp op e1' e2' ++ ")"
exp2tla env (ECall _ f es) = do
  es' <- mapM (exp2tla env) es
  return $ f ++ "(" ++ join ", " es' ++ ")"
exp2tla env (EIndex _ e1 e2) = do
  e1' <- exp2tla env e1
  e2' <- exp2tla env e2
  return $ e1' ++ "[" ++ e2' ++ "]"
exp2tla env (ECond _ cond thenCase elseCase) = do
  cond' <- exp2tla env cond
  thenCase' <- exp2tla env thenCase
  elseCase' <- exp2tla env elseCase
  return $ "(IF " ++ cond' ++ " THEN " ++ thenCase' ++ " ELSE " ++ elseCase' ++ ")"
exp2tla env (EExcept _ e i override) = do
  e' <- exp2tla env e
  i' <- exp2tla env i
  override' <- exp2tla env override
  return $ "[" ++ e' ++ " EXCEPT ![" ++ i' ++ "] = " ++ override' ++ "]"
exp2tla env (EGetField _ e f) = do
  e' <- exp2tla env e
  return $ if f /= "" && all isAlpha f
    then e' ++ "." ++ f
    else e' ++ "[" ++ show f ++ "]"
exp2tla env (EMkFunc _ arg domain range) = do
  domain' <- exp2tla env domain
  range' <- exp2tla (M.insert arg arg env) range
  return $ "[" ++ arg ++ " \\in " ++ domain' ++ " |-> " ++ range' ++ "]"
exp2tla env (EQuant _ q arg set predicate) = do
  let {q' = case q of
    Exists -> "\\E"
    Forall -> "\\A"
    Choose -> "CHOOSE"}
  set' <- exp2tla env set
  predicate' <- exp2tla (M.insert arg arg env) predicate
  return $ "(" ++ q' ++ " " ++ arg ++ " \\in " ++ set' ++ ": " ++ predicate' ++ ")"

data SimpleInstr a
  = SimpleAwait (Exp a)
  | SimpleAssignDet Id (Exp a)
  | SimpleAssignNonDet Id (Exp a)
  | Done
  deriving (Show)

type Label = String
type CFGNode a = (KEnv, [SimpleInstr a])
type CFG a = M.Map Label (CFGNode a)

noLocation :: SourceLocation
noLocation = SourceLocation 0 0

pop :: Integer -> Exp a -> Exp a
pop n e =
  let a = getAnnotation e in
  ECall a "SubSeq" [e, EInt a 1, EBinaryOp a Minus (ECall a "Len" [e]) (EInt a n)]

replaceTop :: Exp a -> Exp a -> Exp a
replaceTop stack newTop =
  let a = getAnnotation stack in
  EBinaryOp a Concat (pop 1 stack) (EMkTuple a [newTop])

sequenceStms :: [Stm SourceLocation] -> Stm SourceLocation
sequenceStms [] = Skip noLocation
sequenceStms [s] = s
sequenceStms (s : rest) = Seq (getAnnotation s) s (sequenceStms rest)

entryLabel :: Id -> Label
entryLabel procName = '_' : procName

toCfg :: KEnv -> Procedure SourceLocation -> NamesOp (CFG SourceLocation, Label)
toCfg env proc =
  let loc = procedureSyntaxAnnotation proc in f (Just (entryLabel (procedureName proc))) Nothing $ [Assign loc (LVar loc v) e | VarDecl loc v e <- procedureLocals proc] ++ [procedureBody proc, Return loc Nothing]
  where
    localNames proc = [v | VarDecl _ v _ <- procedureLocals proc]

    innerEnv :: KEnv
    innerEnv = M.union (M.fromList [(param, KProcedureLocalVar) | param <- procedureParameters proc ++ localNames proc]) env

    labelFor :: SourceLocation -> NamesOp Label
    labelFor loc = freshName ("_line_" ++ pad 5 '0' (show (line loc)))

    pickLabelIfNoneChosen :: Maybe Label -> SourceLocation -> NamesOp Label
    pickLabelIfNoneChosen (Just l) _ = return l
    pickLabelIfNoneChosen Nothing loc = labelFor loc

    f :: Maybe Label -> Maybe Label -> [Stm SourceLocation] -> NamesOp (CFG SourceLocation, Label)
    f here next [] = f here next [Return noLocation Nothing]
    f here next (Seq _ a b : k) = f here next (a : b : k)
    f here next (Skip _ : k) = f here next k
    f here _ (Return loc maybeRet : _) = do
      label <- pickLabelIfNoneChosen here loc
      ret <- case maybeRet of
        Just e -> fixReads innerEnv e
        Nothing -> return (EVar loc undefinedConstant)
      return (M.singleton label (innerEnv,
        SimpleAwait (EBinaryOp loc Gt (ECall loc "Len" [myPc]) (EInt loc 0))
        : SimpleAwait (EBinaryOp loc Eq (EIndex loc myPc (ECall loc "Len" [myPc])) (EStr loc label))
        : SimpleAwait (EBinaryOp loc Or (EBinaryOp loc Eq (EVar loc actorVar) (EVar loc undefinedConstant)) (EBinaryOp loc Eq (EVar loc actorVar) (EThreadID loc)))
        : SimpleAssignDet actorVar (EThreadID loc)
        : setMy SimpleAssignDet retVar ret
        : setMy SimpleAssignDet framesVar (pop 1 (EIndex loc (EVar loc framesVar) (EThreadID loc)))
        : setPc SimpleAssignDet (ECall loc "SubSeq" [myPc, EInt loc 1, EBinaryOp loc Minus (ECall loc "Len" [myPc]) (EInt loc 1)])
        : [Done]), label)
    f here next (CallAndSaveReturnValue loc lval procName args : k) = do
      f here next $ Call loc procName args : Assign loc lval (EVar loc retVar) : k
    f here next (Yield _ : rest@(Await _ _ : _)) = do
      -- "await" has an implicit yield, so we can eliminate redundant yields
      f here next rest
    f here next (s : k) = do
      let loc = getAnnotation s
      label <- pickLabelIfNoneChosen here loc
      (nextCfg, nextLabel) <- f Nothing next k
      (rest, body) <- core nextLabel s
      return (M.insert label (innerEnv,
        SimpleAwait (EBinaryOp loc Gt (ECall loc "Len" [myPc]) (EInt loc 0))
        : SimpleAwait (EBinaryOp loc Eq (EIndex loc myPc (ECall loc "Len" [myPc])) (EStr loc label))
        : SimpleAwait (EBinaryOp loc Or (EBinaryOp loc Eq (EVar loc actorVar) (EVar loc undefinedConstant)) (EBinaryOp loc Eq (EVar loc actorVar) (EThreadID loc)))
        : SimpleAssignDet actorVar (EThreadID loc)
        : body) (M.union rest nextCfg), label)

    rec :: Label -> Stm SourceLocation -> NamesOp (CFG SourceLocation, Label)
    rec next s = f Nothing (Just next) [s]

    myPc = EIndex noLocation (EVar noLocation pcVar) (EThreadID noLocation)
    setMy f var val = f var (EExcept noLocation (EVar noLocation var) (EThreadID noLocation) val)
    setPc f = setMy f pcVar
    clearActor loc = SimpleAssignDet actorVar (EVar loc undefinedConstant)

    goto :: Label -> SimpleInstr SourceLocation
    goto l = setPc SimpleAssignDet (replaceTop myPc (EStr noLocation l))

    core :: Label -> Stm SourceLocation -> NamesOp (CFG SourceLocation, [SimpleInstr SourceLocation])
    core next s@(Seq _ _ _) = errorAt s $ "internal bug: sequence case is supposed to be handled elsewhere"
    core next s@(Return _ _) = errorAt s $ "internal bug: return case is supposed to be handled elsewhere"
    core next s@(CallAndSaveReturnValue _ _ _ _) = errorAt s $ "internal bug: call-and-return case is supposed to be handled elsewhere"
    core next (Skip _) = do
      return (M.empty, [goto next])
    core next (Assert loc _) = do
      -- TODO: collect assertion failure conditions
      core next (Skip loc)
    core next (Yield loc) = do
      return (M.empty, [clearActor loc, goto next])
    core next (Either loc stms) = do
      stms' <- mapM (rec next) stms
      let cfgs = map fst stms'
      let labels = map snd stms'
      return (M.unions cfgs, [setPc SimpleAssignNonDet (EMkSet loc [replaceTop myPc (EStr loc label) | label <- labels]), Done])
    core next s@(Assign loc lval e) = do
      e' <- fixReads innerEnv e
      (v, v') <- asSimpleAssignment innerEnv lval e'
      return (M.empty, [SimpleAssignDet v v', goto next])
    core next (Await loc e) = do
      mid <- labelFor loc
      e' <- fixReads innerEnv e
      return (M.singleton mid (innerEnv, [SimpleAwait e', goto next]), [clearActor loc, goto mid])
    core next (If loc cond thenBranch elseBranch) = do
      cond' <- fixReads innerEnv cond
      (thenCfg, thenEntry) <- rec next thenBranch
      (elseCfg, elseEntry) <- rec next elseBranch
      return (M.union thenCfg elseCfg, [setPc SimpleAssignDet (replaceTop myPc (ECond loc cond' (EStr loc thenEntry) (EStr loc elseEntry)))])
    core next (While loc cond body) = do
      cond' <- fixReads innerEnv cond
      (bodyCfg, bodyEntry) <- rec next body
      return (bodyCfg, [setPc SimpleAssignDet (replaceTop myPc (ECond loc cond' (EStr loc bodyEntry) (EStr loc next)))])
    core next s@(Call loc procName args) = do
      case M.lookup procName innerEnv of
        Just (KProcedure paramNames) | length paramNames /= length args -> do
          errorAt s $ "Incorrect number of arguments for call to " ++ show procName ++ " (expects " ++ show (length paramNames) ++ ", got " ++ show (length args) ++ ")"
        Just (KProcedure paramNames) -> do
          args' <- mapM (fixReads innerEnv) args
          myFrames <- fixReads innerEnv (EVar noLocation framesVar)
          return (M.empty, [
            setMy SimpleAssignDet framesVar (EBinaryOp noLocation Concat myFrames (EMkTuple loc [EMkRecord noLocation (zip paramNames args')])),
            setPc SimpleAssignDet (EBinaryOp noLocation Concat (replaceTop myPc (EStr noLocation next)) (EMkTuple noLocation [EStr noLocation (entryLabel procName)]))])
        Just _ -> errorAt s $ "Cannot call variable " ++ show procName
        Nothing -> errorAt s $ "There is no procedure named " ++ show procName

lval2exp :: LValue a -> Exp a
lval2exp (LVar a v) = EVar a v
lval2exp (LIndex a lval i) = EIndex a (lval2exp lval) i
lval2exp (LField a lval f) = EGetField a (lval2exp lval) f

asSimpleAssignment :: (Monad m) => KEnv -> LValue SourceLocation -> Exp SourceLocation -> m (Id, Exp SourceLocation)
asSimpleAssignment env lval@(LVar a v) e =
  case M.lookup v env of
    Just KGlobalVar -> return (v, e)
    Just KPerProcessVar -> return (v, EExcept a (EVar a v) (EVar a selfConstant) e)
    Just KProcedureLocalVar -> asSimpleAssignment env (LField a (LIndex a (LVar a framesVar) (ECall a "Len" [EVar a framesVar])) v) e
    _ -> errorAt e $ "Cannot assign to " ++ show lval
asSimpleAssignment env (LIndex a lval i) e = do
  lval' <- fixReads env (lval2exp lval)
  i' <- fixReads env i
  asSimpleAssignment env lval (EBinaryOp a LeftBiasedMapUnion (EBinaryOp a SingletonMapping i' e) lval')
asSimpleAssignment env (LField a lval f) e =
  asSimpleAssignment env (LIndex a lval (EStr a f)) e

increaseIndent :: String -> String
increaseIndent s = ' ' : ' ' : s

convertTransition :: String -> CFGNode SourceLocation -> NamesOp TLACode
convertTransition name (kenv, instrs) = do
  res <- steps (increaseIndent "") (S.empty) (initialEnv kenv) instrs
  return $ join "\n" $ [name ++ "(" ++ selfConstant ++ ") =="] ++ res
  where
    steps :: String -> S.Set Id -> Env -> [SimpleInstr SourceLocation] -> NamesOp [TLACode]
    steps indent changed env [] = return $
      [indent ++ "/\\ " ++ v ++ "' = " ++ v' | (v, v') <- M.toList env, v `S.member` changed] ++
      [indent ++ "/\\ UNCHANGED " ++ v | (v, _) <- M.toList env, not (v `S.member` changed)]
    steps indent changed env (SimpleAwait e : rest) = do
      e' <- exp2tla env e
      rest' <- steps indent changed env rest
      return $ (indent ++ "/\\ " ++ e') : rest'
    steps indent changed env (SimpleAssignDet v e : rest) = do
      tmp <- freshName "_tmp"
      rest <- steps (increaseIndent indent) (S.insert v changed) (M.insert v tmp env) rest
      e' <- exp2tla env e
      return $ (indent ++ "/\\ LET " ++ tmp ++ " == " ++ e' ++ " IN") : rest
    steps indent changed env (SimpleAssignNonDet v e : rest) = do
      set <- exp2tla env e
      tmp <- freshName "_tmp"
      rest' <- steps (increaseIndent indent) changed env (SimpleAssignDet v (EVar (getAnnotation e) tmp) : rest)
      return $ (indent ++ "/\\ \\E " ++ tmp ++ " \\in " ++ set ++ ":") : rest'
    steps indent changed env (Done : _) = do
      steps indent changed env []

    initialEnv :: KEnv -> Env
    initialEnv = M.fromList . catMaybes . map helper . M.toList
      where
        helper (v, kind) =
          case kind of
            KGlobalVar -> Just (v, v)
            KPerProcessVar -> Just (v, v)
            _ -> Nothing

mkEnv :: Module SourceLocation -> KEnv
mkEnv (Module _ vars procs) = do
  M.unions [
    M.singleton pcVar KPerProcessVar,
    M.singleton framesVar KPerProcessVar,
    M.singleton retVar KPerProcessVar,
    M.singleton actorVar KGlobalVar,
    M.fromList [(v, KGlobalVar) | VarDecl _ v _ <- vars],
    M.fromList [(procedureName p, KProcedure (procedureParameters p)) | p <- procs]]
