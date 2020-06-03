module CompileToTLA (TLACode, ezpsl2tla) where

import Data.Maybe (catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char (isAlpha)

import Data.Annotated (Annotated, getAnnotation)
import Data.SourceLocation (SourceLocation(SourceLocation), line, column)
import Language.EzPSL.Syntax
import Language.EzPSL.Transform (transformBottomUp)
import Names (NamesOp, runNamesOp, freshName)
import Constants (pcVar, framesVar, retVar, actorVar, selfConstant, undefinedConstant)
import Misc (join, pad)


ezpsl2tla :: (MonadFail m) => Module SourceLocation -> m TLACode
ezpsl2tla m@(Module _ vars procs) = do
  let env = mkEnv m
  let entryProcedureNames = S.toList (namesOfEntryProcedures procs)
  case entryProcedureNames of
    [] -> fail "The program contains no entry points.  Annotate at least one procedure with \"@entry\"."
    _ -> do
      initialValues <- mapM (\(VarDecl _ _ e) -> exp2tla (M.empty) e) vars
      (bigCfg, procedureEntryLabels, transitions, assertions) <- runNamesOp $ do
        compiled <- mapM (toCfg env) procs
        let (cfgs, asserts, labels) = unzip3 compiled
        let bigCfg = M.unions cfgs
        transitions <- mapM (uncurry convertTransition) (M.toList bigCfg)
        return (bigCfg, labels, transitions, concat asserts)
      let pidSets = [p ++ "_calls" | p <- entryProcedureNames]
      let allVars = pcVar : framesVar : retVar : actorVar : [v | VarDecl _ v _ <- vars]
      assertionConditions <- mapM (\(Assertion label kenv e) -> do
        e' <- fixReads kenv (EBinaryOp noLocation Implies (EBinaryOp noLocation And (EBinaryOp noLocation Ne (EVar noLocation pcVar) (EMkTuple noLocation [])) (EBinaryOp noLocation Eq (peek $ EVar noLocation pcVar) (EStr noLocation label))) e)
        exp2tla (initialEnv kenv) e') assertions
      return $ join "\n" $ [
        "CONSTANTS " ++ join ", " (undefinedConstant : pidSets),
        "VARIABLES " ++ join ", " allVars,
        "vars == <<" ++ join ", " allVars ++ ">>",
        "symmetry == UNION {" ++ join ", " ["Permutations(" ++ p ++ ")" | p <- pidSets] ++ "}",
        "Init =="]
        ++ ["  /\\ " ++ pcVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ "_calls |-> <<" ++ show pEntry ++ ">>]" | (p, pEntry) <- zip entryProcedureNames procedureEntryLabels]]
        ++ ["  /\\ " ++ framesVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ " |-> << <<>> >>]" | p <- pidSets]]
        ++ ["  /\\ " ++ retVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ " |-> " ++ undefinedConstant ++ "]" | p <- pidSets]]
        ++ ["  /\\ " ++ actorVar ++ " = " ++ undefinedConstant]
        ++ ["  /\\ " ++ v ++ " = " ++ initValue | (VarDecl _ v _, initValue) <- zip vars initialValues]
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
        ++ case assertionConditions of
          [] -> ["NoAssertionFailures == TRUE"]
          _ -> ["NoAssertionFailures == \\A " ++ selfConstant ++ " \\in UNION {" ++ join ", " pidSets ++ "}:"]
            ++ ["    /\\ " ++ e | e <- assertionConditions]

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

errorAt :: (MonadFail m, Annotated loc) => loc SourceLocation -> String -> m t
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

fixReads :: (MonadFail m) => KEnv -> Exp SourceLocation -> m (Exp SourceLocation)
fixReads kenv =
  transformBottomUp (\e ->
    case e of
      ECall _ f _ ->
        case M.lookup f kenv of
          Just (KProcedure _) -> do
            errorAt e $ "Illegal call to " ++ show f ++ "; procedure calls must be in `call` statements."
          _ -> return e
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
exp2tla env (EVar _ v) =
  case M.lookup v env of
    Nothing -> return v
    Just v' -> return v'
exp2tla _ (EThreadID _) =
  return selfConstant
exp2tla env (EMkSet _ es) = do
  es' <- mapM (exp2tla env) es
  return $ "{" ++ join ", " es' ++ "}"
exp2tla outerEnv (ESetComprehension loc e clauses) = loop outerEnv clauses
  where
    loop env [] = exp2tla env (EMkSet loc [e])
    loop env (SCFilter _ p : rest) = do
      p' <- exp2tla env p
      rest' <- loop env rest
      return $ "(IF " ++ p' ++ " THEN " ++ rest' ++ " ELSE {})"
    loop env (SCMember _ x set : rest) = do
      set' <- exp2tla env set
      rest' <- loop (M.insert x x env) rest
      return $ "(UNION {" ++ rest' ++ " : " ++ x ++ " \\in " ++ set' ++ "})"
exp2tla env (EMkTuple _ es) = do
  es' <- mapM (exp2tla env) es
  return $ "<<" ++ join ", " es' ++ ">>"
exp2tla env (EMkRecord loc []) = do
  exp2tla env (EMkTuple loc [])
exp2tla env (EMkRecord _ fields) = do
  fields' <- mapM (\(fieldName, fieldValue) -> do
    fieldValue' <- exp2tla env fieldValue
    return (fieldName, fieldValue')) fields
  return $ "[" ++ join ", " [fieldName ++ " |-> " ++ fieldValue | (fieldName, fieldValue) <- fields'] ++ "]"
exp2tla env (EUnaryOp _ op e) = do
  e' <- exp2tla env e
  case op of
    Not -> return $ "~" ++ e'
    Negate -> return $ "-" ++ e'
    Domain -> return $ "(DOMAIN " ++ e' ++ ")"
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

peek :: Exp a -> Exp a
peek e =
  let a = getAnnotation e in
  EIndex a e (ECall a "Len" [e])

replaceTop :: Exp a -> Exp a -> Exp a
replaceTop stack newTop =
  let a = getAnnotation stack in
  EBinaryOp a Concat (pop 1 stack) (EMkTuple a [newTop])

entryLabel :: Id -> Label
entryLabel procName = '_' : procName

-- | Details about an assertion: when a process is at the given label, it is
--   asserting the given expression.
data Assertion a = Assertion Label KEnv (Exp a)

-- | Convert a procedure into a CFG, collecting all assertions along the way.
--   The returned label is the procedure entry point.
toCfg :: KEnv -> Procedure SourceLocation -> NamesOp (CFG SourceLocation, [Assertion SourceLocation], Label)
toCfg env proc =
  blockToCfg (Just (entryLabel (procedureName proc))) Nothing $ [Assign loc (LVar loc v) e | VarDecl loc v e <- procedureLocals proc] ++ [procedureBody proc, Return (procedureSyntaxAnnotation proc) Nothing]
  where
    localNames = [v | VarDecl _ v _ <- procedureLocals proc]

    innerEnv :: KEnv
    innerEnv = M.union (M.fromList [(param, KProcedureLocalVar) | param <- procedureParameters proc ++ localNames]) env

    labelFor :: SourceLocation -> NamesOp Label
    labelFor loc = freshName ("_line_" ++ pad 5 '0' (show (line loc)))

    pickLabelIfNoneChosen :: Maybe Label -> SourceLocation -> NamesOp Label
    pickLabelIfNoneChosen (Just l) _ = return l
    pickLabelIfNoneChosen Nothing loc = labelFor loc

    -- | Common instructions that wait for
    --    1. the PC to be correct
    --    2. the actor to be correct
    commonPrefix :: SourceLocation -> Label -> [SimpleInstr SourceLocation]
    commonPrefix a label = [
      SimpleAwait (EBinaryOp a Gt (ECall a "Len" [myPc]) (EInt a 0)),
      SimpleAwait (EBinaryOp a Eq (EIndex a myPc (ECall a "Len" [myPc])) (EStr a label)),
      SimpleAwait (EBinaryOp a Or (EBinaryOp a Eq (EVar a actorVar) (EVar a undefinedConstant)) (EBinaryOp a Eq (EVar a actorVar) (EThreadID a))),
      SimpleAssignDet actorVar (EThreadID a)]

    blockToCfg :: Maybe Label -> Maybe Label -> [Stm SourceLocation] -> NamesOp (CFG SourceLocation, [Assertion SourceLocation], Label)
    blockToCfg here Nothing [] = do
      -- no `next` label: return from this call
      blockToCfg here Nothing [Return noLocation Nothing]
    blockToCfg _ (Just next) [] = do
      -- nothing to do, but there is a `next` label: goto next
      return (M.empty, [], next)
    blockToCfg here next (Seq _ a b : k) = do
      blockToCfg here next (a : b : k)
    blockToCfg here next (Skip _ : k) = blockToCfg here next k
    blockToCfg here _ (Return loc maybeRet : _) = do
      label <- pickLabelIfNoneChosen here loc
      ret <- case maybeRet of
        Just e -> fixReads innerEnv e
        Nothing -> return (EVar loc undefinedConstant)
      return (M.singleton label (innerEnv,
          commonPrefix loc label ++ [
          setMy SimpleAssignDet retVar ret,
          setMy SimpleAssignDet framesVar (pop 1 (EIndex loc (EVar loc framesVar) (EThreadID loc))),
          setPc (ECall loc "SubSeq" [myPc, EInt loc 1, EBinaryOp loc Minus (ECall loc "Len" [myPc]) (EInt loc 1)])]),
        [],
        label)
    blockToCfg here next (CallAndSaveReturnValue loc lval procName args : k) = do
      blockToCfg here next $ Call loc procName args : Assign loc lval (EVar loc retVar) : k
    blockToCfg here next (Yield _ : rest@(Await _ _ : _)) = do
      -- "await" has an implicit yield, so we can eliminate redundant yields
      blockToCfg here next rest
    blockToCfg here next (s : k) = do
      let loc = getAnnotation s
      label <- pickLabelIfNoneChosen here loc
      (nextCfg, assertions2, nextLabel) <- blockToCfg Nothing next k
      (rest, assertions1, body) <- stmToCfg label nextLabel s
      return (M.insert label (innerEnv, commonPrefix loc label ++ body) (M.union rest nextCfg), assertions1 ++ assertions2, label)

    rec :: Label -> Stm SourceLocation -> NamesOp (CFG SourceLocation, [Assertion SourceLocation], Label)
    rec next s = blockToCfg Nothing (Just next) [s]

    myPc = EIndex noLocation (EVar noLocation pcVar) (EThreadID noLocation)
    setMy f var val = f var (EExcept noLocation (EVar noLocation var) (EThreadID noLocation) val)
    setPc = setMy SimpleAssignDet pcVar
    clearActor loc = SimpleAssignDet actorVar (EVar loc undefinedConstant)

    goto :: Label -> SimpleInstr SourceLocation
    goto l = setPc (replaceTop myPc (EStr noLocation l))

    stmToCfg :: Label -> Label -> Stm SourceLocation -> NamesOp (CFG SourceLocation, [Assertion SourceLocation], [SimpleInstr SourceLocation])
    stmToCfg _ _ s@(Seq _ _ _) = errorAt s $ "internal bug: sequence case is supposed to be handled elsewhere"
    stmToCfg _ _ s@(Return _ _) = errorAt s $ "internal bug: return case is supposed to be handled elsewhere"
    stmToCfg _ _ s@(CallAndSaveReturnValue _ _ _ _) = errorAt s $ "internal bug: call-and-return case is supposed to be handled elsewhere"
    stmToCfg _ _ s@(Skip _) = errorAt s $ "internal bug: skip case is supposed to be handled elsewhere"
    stmToCfg here next (Assert _ e) = do
      return (M.empty, [Assertion here innerEnv e], [goto next])
    stmToCfg _ next (Yield loc) = do
      return (M.empty, [], [clearActor loc, goto next])
    stmToCfg _ next (Either loc stms) = do
      newPc <- freshName "_newPc"
      stms' <- mapM (rec next) stms
      let (cfgs, assertions, labels) = unzip3 stms'
      return (M.unions cfgs, concat assertions, [SimpleAssignNonDet newPc (EMkSet loc [replaceTop myPc (EStr loc label) | label <- labels]), setPc (EVar loc newPc)])
    stmToCfg _ next (Assign _ lval e) = do
      e' <- fixReads innerEnv e
      (v, v') <- asSimpleAssignment innerEnv lval e'
      return (M.empty, [], [SimpleAssignDet v v', goto next])
    stmToCfg _ next (NondeterministicAssign loc lval set predicate) = do
      x <- freshName "_choice"
      set' <- fixReads innerEnv set
      (v, v') <- asSimpleAssignment innerEnv lval (EVar loc x)
      predicate' <- fixReads innerEnv predicate
      return (M.empty, [], [SimpleAssignNonDet x set', SimpleAssignDet v v', SimpleAwait predicate', goto next])
    stmToCfg _ next (Await loc e) = do
      mid <- labelFor loc
      e' <- fixReads innerEnv e
      return (M.singleton mid (innerEnv, commonPrefix loc mid ++ [SimpleAwait e', goto next]), [], [clearActor loc, goto mid])
    stmToCfg _ next (If loc cond thenBranch elseBranch) = do
      cond' <- fixReads innerEnv cond
      (thenCfg, a1, thenEntry) <- rec next thenBranch
      (elseCfg, a2, elseEntry) <- rec next elseBranch
      return (M.union thenCfg elseCfg, a1 ++ a2, [setPc (replaceTop myPc (ECond loc cond' (EStr loc thenEntry) (EStr loc elseEntry)))])
    stmToCfg here next (While loc cond body) = do
      cond' <- fixReads innerEnv cond
      (bodyCfg, assertions, bodyEntry) <- rec here body
      return (bodyCfg, assertions, [setPc (replaceTop myPc (ECond loc cond' (EStr loc bodyEntry) (EStr loc next)))])
    stmToCfg _ next s@(Call loc procName args) = do
      case M.lookup procName innerEnv of
        Just (KProcedure paramNames) | length paramNames /= length args -> do
          errorAt s $ "Incorrect number of arguments for call to " ++ show procName ++ " (expects " ++ show (length paramNames) ++ ", got " ++ show (length args) ++ ")"
        Just (KProcedure paramNames) -> do
          args' <- mapM (fixReads innerEnv) args
          myFrames <- fixReads innerEnv (EVar noLocation framesVar)
          return (M.empty, [], [
            setMy SimpleAssignDet framesVar (EBinaryOp noLocation Concat myFrames (EMkTuple loc [EMkRecord noLocation (zip paramNames args')])),
            setPc (EBinaryOp noLocation Concat (replaceTop myPc (EStr noLocation next)) (EMkTuple noLocation [EStr noLocation (entryLabel procName)]))])
        Just _ -> errorAt s $ "Cannot call variable " ++ show procName
        Nothing -> errorAt s $ "There is no procedure named " ++ show procName

lval2exp :: LValue a -> Exp a
lval2exp (LVar a v) = EVar a v
lval2exp (LIndex a lval i) = EIndex a (lval2exp lval) i
lval2exp (LField a lval f) = EGetField a (lval2exp lval) f

asSimpleAssignment :: (MonadFail m) => KEnv -> LValue SourceLocation -> Exp SourceLocation -> m (Id, Exp SourceLocation)
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
      [indent ++ "/\\ " ++ v ++ "' = " ++ v' | (v, v') <- M.toList env, v `M.member` kenv,      v `S.member` changed] ++
      [indent ++ "/\\ UNCHANGED " ++ v       | (v, _ ) <- M.toList env, v `M.member` kenv, not (v `S.member` changed)]
    steps indent changed env (SimpleAwait e : rest) = do
      e' <- exp2tla env e
      rest' <- steps indent changed env rest
      return $ (indent ++ "/\\ " ++ e') : rest'
    steps indent changed env (SimpleAssignDet v e : rest) = do
      tmp <- freshName "_tmp"
      rest' <- steps (increaseIndent indent) (S.insert v changed) (M.insert v tmp env) rest
      e' <- exp2tla env e
      return $ (indent ++ "/\\ LET " ++ tmp ++ " == " ++ e' ++ " IN") : rest'
    steps indent changed env (SimpleAssignNonDet v e : rest) = do
      set <- exp2tla env e
      tmp <- freshName "_tmp"
      rest' <- steps (increaseIndent indent) changed env (SimpleAssignDet v (EVar (getAnnotation e) tmp) : rest)
      return $ (indent ++ "/\\ \\E " ++ tmp ++ " \\in " ++ set ++ ":") : rest'

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
