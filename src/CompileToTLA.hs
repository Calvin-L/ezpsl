module CompileToTLA (TLACode, ezpsl2tla) where

import Data.Maybe (catMaybes, fromJust)
import Data.List (sortOn)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char (isAlpha)

import Data.Annotated (Annotated, getAnnotation)
import Data.SourceLocation (SourceLocation(SourceLocation), line, column)
import Language.EzPSL.Syntax
import Language.EzPSL.Transform (transformBottomUp)
import Names (NamesOp, runNamesOp, freshName)
import Constants (pcVar, framesVar, globalsScratchVar, retVar, actorVar, initialPc, selfConstant, undefinedConstant)
import Misc (join, pad)


ezpsl2tla :: (MonadFail m) => Module SourceLocation -> m TLACode
ezpsl2tla m@(Module _ vars procs) = do
  let env = mkEnv m
  let entryProcedures = sortOn procedureName $ findEntryProcedures procs
  let pidSets = [procedureName p ++ "_calls" | p <- entryProcedures]
  case entryProcedures of
    [] -> fail "The program contains no entry points.  Annotate at least one procedure with \"@entry\"."
    _ -> do
      initialValues <- mapM createTLAVariableInitialization vars
      (allTransitions, compiledTransitions, assertions) <- runNamesOp $ do
        compiled <- mapM (procToTransitions env) procs
        let (transitionSets, asserts, labels) = unzip3 compiled
        let procedureEntryLabels = M.fromList [(procedureName p, entryPoint) | (p, entryPoint) <- zip procs labels]
        let procForId procName = fromJust $ M.lookup procName procedureEntryLabels
        let allTransitions = haltTransition env : [beginTransition env p pset pEntry | (pset, p) <- zip pidSets entryProcedures, let pEntry = fromJust $ M.lookup (procedureName p) procedureEntryLabels] ++ concatMap (\tn -> tn procForId) transitionSets
        convertedTransitions <- mapM (convertTransition env) allTransitions
        return (allTransitions, convertedTransitions, concat asserts)
      let allVars = pcVar : framesVar : globalsScratchVar : retVar : actorVar : [variableBeingDeclared decl | decl <- vars]
      assertionConditions <- mapM (\(Assertion label kenv e) -> do
        e' <- fixReads kenv (EBinaryOp noLocation Implies (EBinaryOp noLocation And (EBinaryOp noLocation Ne (EVar noLocation pcVar) (EMkTuple noLocation [])) (EBinaryOp noLocation Eq (peek $ EVar noLocation pcVar) (EStr noLocation label))) e)
        exp2tla (initialEnv kenv) e') assertions
      return $ join "\n" $ [
        "CONSTANTS " ++ join ", " (undefinedConstant : pidSets),
        "VARIABLES " ++ join ", " allVars,
        "vars == <<" ++ join ", " allVars ++ ">>",
        "symmetry == UNION {" ++ join ", " ["Permutations(" ++ p ++ ")" | p <- pidSets] ++ "}",
        "Init =="]
        ++ ["  /\\ " ++ pcVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ pset ++ " |-> <<\"" ++ initialPc ++ "\">>]" | pset <- pidSets]]
        ++ ["  /\\ " ++ framesVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ " |-> << <<>> >>]" | p <- pidSets]]
        ++ ["  /\\ " ++ globalsScratchVar ++ " = " ++ undefinedConstant]
        ++ ["  /\\ " ++ retVar ++ " = " ++ join " @@ " ["[_pid \\in " ++ p ++ " |-> " ++ undefinedConstant ++ "]" | p <- pidSets]]
        ++ ["  /\\ " ++ actorVar ++ " = " ++ undefinedConstant]
        ++ ["  /\\ " ++ initExp | initExp <- initialValues]
        ++ compiledTransitions
        ++ ["  /\\ UNCHANGED " ++ variableBeingDeclared decl | decl <- vars]
        ++ ["\\* `_finished` prevents TLC from reporting deadlock when all processes finish normally"]
        ++ ["_finished ==",
            "  /\\ \\A " ++ selfConstant ++ " \\in UNION {" ++ join ", " pidSets ++ "}: " ++ pcVar ++ "[" ++ selfConstant ++ "] = <<>>",
            "  /\\ UNCHANGED <<" ++ join ", " allVars ++ ">>"]
        ++ ["Next ==", "  \\E _pid \\in UNION {" ++ join ", " pidSets ++ "}:"]
        ++ ["    \\/ " ++ name ++ "(_pid)" | (name, _) <- allTransitions]
        ++ ["    \\/ _halt(_pid)"]
        ++ ["    \\/ _begin_" ++ procedureName proc ++ "(_pid)" | proc <- entryProcedures]
        ++ ["    \\/ _finished"]
        ++ case assertionConditions of
          [] -> ["NoAssertionFailures == TRUE"]
          _ -> ["NoAssertionFailures == \\A " ++ selfConstant ++ " \\in UNION {" ++ join ", " pidSets ++ "}:"]
            ++ ["    /\\ (" ++ actorVar ++ " = " ++ selfConstant ++ ") => (" ++ e ++ ")" | e <- assertionConditions]

createTLAVariableInitialization :: (Monad m) => VarDecl SourceLocation -> m TLACode
createTLAVariableInitialization (VarDecl _ v e) = do
  e' <- exp2tla (M.empty) e
  return $ v ++ " = (" ++ e' ++ ")"
createTLAVariableInitialization (VarDeclNondeterministic _ v e) = do
  e' <- exp2tla (M.empty) e
  return $ v ++ " \\in (" ++ e' ++ ")"

beginTransition :: KEnv -> Procedure SourceLocation -> Id -> PCLabel -> NamedTransition SourceLocation
beginTransition kenv p pset entry = ("_begin_" ++ procedureName p, [
  SimpleAwait $ EBinaryOp noLocation Eq (EVar noLocation actorVar) (EVar noLocation undefinedConstant),
  SimpleAssignDet actorVar $ EThreadID noLocation,
  SimpleAwait $ EBinaryOp noLocation In (EThreadID noLocation) (EVar noLocation pset),
  SimpleAwait $ EBinaryOp noLocation Gt (ECall noLocation "Len" [myPc]) (EInt noLocation 0),
  SimpleAwait $ EBinaryOp noLocation Eq (EIndex noLocation myPc (ECall noLocation "Len" [myPc])) (EStr noLocation initialPc),
  goto entry]
  ++ importGlobals noLocation kenv)

haltTransition :: KEnv -> NamedTransition SourceLocation
haltTransition kenv = ("_halt", [
  SimpleAwait $ EBinaryOp noLocation Eq (EVar noLocation actorVar) (EThreadID noLocation),
  SimpleAwait $ EBinaryOp noLocation Eq (readProcessLocal noLocation pcVar) (EMkTuple noLocation []),
  SimpleAssignDet actorVar $ EVar noLocation undefinedConstant,
  SimpleAssignDet retVar $ EExcept noLocation (EVar noLocation retVar) (EThreadID noLocation) (EVar noLocation undefinedConstant),
  SimpleAssignDet framesVar $ EExcept noLocation (EVar noLocation framesVar) (EThreadID noLocation) (EMkRecord noLocation [])]
  ++ exportGlobals noLocation kenv)

findEntryProcedures :: [Procedure a] -> [Procedure a]
findEntryProcedures = filter isEntryPoint
  where
    isEntryPoint :: Procedure a -> Bool
    isEntryPoint p = EntryPoint `elem` (procedureAnnotations p)

type TLACode = String

data Kind
  = KPerProcessVar
  | KProcedureLocalVar
  | KUserDefinedGlobalVar
  | KInternalGlobalVar
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
  transformBottomUp (\bound e ->
    case e of
      ECall _ f _ ->
        case M.lookup f kenv of
          Just (KProcedure _) -> do
            errorAt e $ "Illegal call to " ++ show f ++ "; procedure calls must be in `call` statements."
          _ -> return e
      EVar a v | not (v `elem` bound) ->
        case M.lookup v kenv of
          Just KUserDefinedGlobalVar -> do
            return $ EIndex a (EVar a globalsScratchVar) (EStr a v)
          Just KPerProcessVar -> do
            return $ EIndex a e (EThreadID a)
          Just KProcedureLocalVar -> do
            let myFrames = EIndex a (EVar a framesVar) (EThreadID a)
            return $ EGetField a (EIndex a myFrames (ECall a "Len" [myFrames])) v
          _ -> return e
      _ -> return e)

exp2tla :: (Monad m) => Env -> Exp SourceLocation -> m TLACode
exp2tla _ (EInt _ i) = return (show i)
exp2tla _ (EBool _ b) = return (if b then "TRUE" else "FALSE")
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
exp2tla env (EQuant _ q arg val body) = do
  let {(q', sep1, sep2) = case q of
    Exists -> ("\\E ",    " \\in ", ": ")
    Forall -> ("\\A ",    " \\in ", ": ")
    Choose -> ("CHOOSE ", " \\in ", ": ")
    LetIn  -> ("LET ",    " == ",   " IN ")}
  val' <- exp2tla env val
  body' <- exp2tla (M.insert arg arg env) body
  return $ "(" ++ concat [q', arg, sep1, val', sep2, body'] ++ ")"

data SimpleInstr a
  = SimpleAwait (Exp a)
  | SimpleAssignDet Id (Exp a)
  | SimpleAssignNonDet Id (Exp a)
  deriving (Show)

-- | A program counter label.
type PCLabel = String

type TransitionName = Id

-- | An atomic transition, expressed as a list of instructions with a unique
--   name.
type NamedTransition a = (TransitionName, [SimpleInstr a])

-- | A set of possible transitions that implement some kind of sequential
--   logic.  The transitions are "incomplete" in the sense that they do not
--   know how to jump into procedures nor what to do after the sequential logic
--   has completed, and must be supplied with that information.
type IncompleteTransitionSet a = (Id -> PCLabel) -> [SimpleInstr a] -> [NamedTransition a]

singleIncompleteTransition :: TransitionName -> ((Id -> PCLabel) -> [SimpleInstr a] -> [SimpleInstr a]) -> IncompleteTransitionSet a
singleIncompleteTransition name instrs = \procs k -> [(name, instrs procs k)]

unionTransitionSets :: [IncompleteTransitionSet a] -> IncompleteTransitionSet a
unionTransitionSets l = \procs k -> concatMap (\ts -> ts procs k) l

-- andThen :: SequenceableTransitionSet a -> SequenceableTransitionSet a -> SequenceableTransitionSet a
-- andThen (aEntry, a) (bEntry, b) = (aEntry, \k ->
--   let b' = b k in
--   let a' = a bEntry in
--   a' ++ b')

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

-- | Details about an assertion: when a process is at the given label, it is
--   asserting the given expression.
data Assertion a = Assertion PCLabel KEnv (Exp a)

doReturn :: SourceLocation -> [SimpleInstr SourceLocation]
doReturn a = [
  setMy SimpleAssignDet framesVar (pop 1 (EIndex a (EVar a framesVar) (EThreadID a))),
  setPc (ECall a "SubSeq" [myPc, EInt a 1, EBinaryOp a Minus (ECall a "Len" [myPc]) (EInt a 1)])]

importGlobals :: SourceLocation -> KEnv -> [SimpleInstr SourceLocation]
importGlobals loc kenv =
  let globals = [name | (name, KUserDefinedGlobalVar) <- M.toList kenv] in
  [SimpleAssignDet globalsScratchVar $ EMkRecord loc [(name, EVar loc name) | name <- globals]]

exportGlobals :: SourceLocation -> KEnv -> [SimpleInstr SourceLocation]
exportGlobals loc kenv =
  let globals = [name | (name, KUserDefinedGlobalVar) <- M.toList kenv] in
  [SimpleAssignDet name $ EIndex loc (EVar loc globalsScratchVar) (EStr noLocation name) | name <- globals] ++
  [SimpleAssignDet globalsScratchVar (EVar loc undefinedConstant)]

varDeclAsAssignment :: VarDecl a -> Stm a
varDeclAsAssignment (VarDecl loc v e) = Assign loc (LVar loc v) e
varDeclAsAssignment (VarDeclNondeterministic loc v e) = NondeterministicAssign loc (LVar loc v) e (EBool loc True)

variableBeingDeclared :: VarDecl a -> Id
variableBeingDeclared (VarDecl _ v _) = v
variableBeingDeclared (VarDeclNondeterministic _ v _) = v

-- | Convert a procedure into a CFG, collecting all assertions along the way.
--   The returned label is the procedure entry point.
procToTransitions :: KEnv -> Procedure SourceLocation -> NamesOp ((Id -> PCLabel) -> [NamedTransition SourceLocation], [Assertion SourceLocation], PCLabel)
procToTransitions env proc = do
  (entry, incomplete, assertions) <- stmToTransitions (procedureName proc) innerEnv $ foldr (Seq noLocation) (procedureBody proc) (map varDeclAsAssignment $ procedureLocals proc)
  let implicitReturn = doReturn noLocation
  let {transitions procs = incomplete procs implicitReturn}
  return (transitions, assertions, entry)

  where
    localNames :: [Id]
    localNames = [variableBeingDeclared decl | decl <- procedureLocals proc]

    innerEnv :: KEnv
    innerEnv = M.union (M.fromList [(param, KProcedureLocalVar) | param <- procedureParameters proc ++ localNames]) env

labelFor :: ProcedureName -> SourceLocation -> String -> NamesOp PCLabel
labelFor pname loc stmDescription =
  freshName ('_' : pname ++ "_line" ++ pad 5 '0' (show (line loc)) ++ '_' : stmDescription)

awaitAtPc :: SourceLocation -> PCLabel -> [SimpleInstr SourceLocation]
awaitAtPc a label = [
  SimpleAwait (EBinaryOp a Gt (ECall a "Len" [myPc]) (EInt a 0)),
  SimpleAwait (EBinaryOp a Eq (EIndex a myPc (ECall a "Len" [myPc])) (EStr a label))]

noActor :: a -> Exp a
noActor a = EBinaryOp a Eq (EVar a actorVar) (EVar a undefinedConstant)

-- | Common instructions on every statement transition that wait for
--    1. the PC to be correct
--    2. the actor to be correct
commonPrefix :: SourceLocation -> PCLabel -> [SimpleInstr SourceLocation]
commonPrefix a label = awaitAtPc a label ++ [
  SimpleAwait (EBinaryOp a Eq (EVar a actorVar) (EThreadID a))]

readProcessLocal :: a -> Id -> Exp a
readProcessLocal a x = EIndex a (EVar a x) (EThreadID a)

-- NOT correct, hard to get right
-- writeProcessLocalNonDet :: a -> Id -> Exp a -> SimpleInstr a
-- writeProcessLocalNonDet a x val = SimpleAssignNonDet x (EExcept a (EVar a x) (EThreadID a) val)

myPc :: Exp SourceLocation
myPc = readProcessLocal noLocation pcVar

setMy :: (Id -> Exp SourceLocation -> SimpleInstr SourceLocation) -> Id -> Exp SourceLocation ->  SimpleInstr SourceLocation
setMy f var val = f var (EExcept noLocation (EVar noLocation var) (EThreadID noLocation) val)

setPc :: Exp SourceLocation -> SimpleInstr SourceLocation
setPc = setMy SimpleAssignDet pcVar

gotoDynamic :: Exp SourceLocation -> SimpleInstr SourceLocation
gotoDynamic l = setPc (replaceTop myPc l)

goto :: PCLabel -> SimpleInstr SourceLocation
goto l = gotoDynamic (EStr noLocation l)

clearActor :: a -> SimpleInstr a
clearActor a = SimpleAssignDet actorVar (EVar a undefinedConstant)

mkStatementTransition :: SourceLocation
                      -> PCLabel
                      -> ([SimpleInstr SourceLocation] -> [SimpleInstr SourceLocation])
                      -> IncompleteTransitionSet SourceLocation
mkStatementTransition loc label instrs =
  singleIncompleteTransition label (\_ next ->
    commonPrefix loc label ++ instrs next)

stmToTransitions :: ProcedureName -> KEnv -> Stm SourceLocation -> NamesOp (PCLabel, IncompleteTransitionSet SourceLocation, [Assertion SourceLocation])
stmToTransitions pname kenv (Seq _ a b) = do
  (aLabel, aTransitions, aAssertions) <- stmToTransitions pname kenv a
  (bLabel, bTransitions, bAssertions) <- stmToTransitions pname kenv b
  return (aLabel, \procs k -> aTransitions procs [goto bLabel] ++ bTransitions procs k, aAssertions ++ bAssertions)
stmToTransitions pname _ (Skip loc) = do
  label <- labelFor pname loc "skip"
  return (label, mkStatementTransition loc label id, [])
stmToTransitions pname kenv (Assert loc e) = do
  label <- labelFor pname loc "assert"
  return (label, mkStatementTransition loc label id, [Assertion label kenv e])
stmToTransitions pname kenv (Yield loc) = do
  stmToTransitions pname kenv (Await loc $ EBool loc True)
stmToTransitions pname kenv (Await loc e) = do
  labelYield <- labelFor pname loc "yield"
  -- NOTE: "await" is the one statement where global variables should not be
  -- read from `globalsScratchVar`.  Since the globals have not been "imported"
  -- for the acting process, they have to be read as true globals.
  e' <- fixReads (M.map userDefinedGlobalsAsRegularGlobals kenv) e
  labelResume <- labelFor pname loc "yield_resume"
  let a = mkStatementTransition loc labelYield (const $ exportGlobals loc kenv ++ [clearActor loc, goto labelResume])
  let b = singleIncompleteTransition labelResume (\_ k -> awaitAtPc loc labelResume ++ [SimpleAwait e', SimpleAwait (noActor loc), SimpleAssignDet actorVar (EThreadID loc)] ++ importGlobals loc kenv ++ k)
  return (labelYield, unionTransitionSets [a, b], [])
  where
    userDefinedGlobalsAsRegularGlobals :: Kind -> Kind
    userDefinedGlobalsAsRegularGlobals KUserDefinedGlobalVar = KInternalGlobalVar
    userDefinedGlobalsAsRegularGlobals k = k
stmToTransitions pname kenv (Either loc stms) = do
  label <- labelFor pname loc "pick_either_branch"
  x <- freshName "_newPc"
  stms' <- mapM (stmToTransitions pname kenv) stms
  let (successorLabels, incompleteTransitions, assertions) = unzip3 stms'
  let {instrs = [
    SimpleAssignNonDet x (EMkSet loc [EStr loc successorLabel | successorLabel <- successorLabels]),
    gotoDynamic (EVar loc x)]}
  return (label, unionTransitionSets (mkStatementTransition loc label (const instrs) : incompleteTransitions), concat assertions)
stmToTransitions pname kenv (Assign loc lval e) = do
  stmToTransitions pname kenv (NondeterministicAssign loc lval (EMkSet loc [e]) (EBool loc True))
stmToTransitions pname kenv (NondeterministicAssign loc lval set predicate) = do
  x <- freshName "_choice"
  label <- labelFor pname loc "pick"
  set' <- fixReads kenv set
  predicate' <- fixReads kenv predicate
  (v, v') <- asSimpleAssignment kenv lval (EVar loc x)
  return (label, mkStatementTransition loc label ([SimpleAssignNonDet x set', SimpleAssignDet v v', SimpleAwait predicate']++), [])
stmToTransitions pname kenv (If loc cond thenBranch elseBranch) = do
  label <- labelFor pname loc "if_branch"
  cond' <- fixReads kenv cond
  (thenEntry, thenTransitions, thenAssertions) <- stmToTransitions pname kenv thenBranch
  (elseEntry, elseTransitions, elseAssertions) <- stmToTransitions pname kenv elseBranch
  let instrs = [setPc (replaceTop myPc (ECond loc cond' (EStr loc thenEntry) (EStr loc elseEntry)))]
  return (label, unionTransitionSets [mkStatementTransition loc label (const instrs), thenTransitions, elseTransitions], thenAssertions ++ elseAssertions)
stmToTransitions pname kenv (While loc cond body) = do
  label <- labelFor pname loc "test_loop_condition"
  cond' <- fixReads kenv cond
  (bodyEntry, bodyTransitions, bodyAssertions) <- stmToTransitions pname kenv body
  exitLabel <- labelFor pname loc "exit_loop"
  let instrs = [setPc (replaceTop myPc (ECond loc cond' (EStr loc bodyEntry) (EStr loc exitLabel)))]
  return (label, unionTransitionSets [
    mkStatementTransition loc label (const instrs),
    \procs _ -> bodyTransitions procs [goto label],
    mkStatementTransition loc exitLabel id
    ], bodyAssertions)
stmToTransitions pname kenv s@(Call loc procName args) = do
  callToTransitions pname kenv s loc procName args (const $ return [])
stmToTransitions pname kenv s@(CallAndSaveReturnValue loc outLVal procName args) = do
  callToTransitions pname kenv s loc procName args (\ret -> do
    (v, v') <- asSimpleAssignment kenv outLVal ret
    return [SimpleAssignDet v v'])
stmToTransitions pname kenv (Return loc maybeRet) = do
  label <- labelFor pname loc "return"
  ret <- case maybeRet of
    Just e -> fixReads kenv e
    Nothing -> return (EVar loc undefinedConstant)
  let {instrs = [setMy SimpleAssignDet retVar ret] ++ doReturn loc}
  return (label, mkStatementTransition loc label (const instrs), [])

callToTransitions :: ProcedureName
                  -> KEnv
                  -> Stm SourceLocation
                  -> SourceLocation
                  -> Id
                  -> [Exp SourceLocation]
                  -> (Exp SourceLocation -> NamesOp [SimpleInstr SourceLocation])
                  -> NamesOp (PCLabel, IncompleteTransitionSet SourceLocation, [Assertion SourceLocation])
callToTransitions pname kenv s loc procName args useReturnValue = do
  case M.lookup procName kenv of
    Just (KProcedure paramNames) | length paramNames /= length args -> do
      errorAt s $ "Incorrect number of arguments for call to " ++ show procName ++ " (expects " ++ show (length paramNames) ++ ", got " ++ show (length args) ++ ")"
    Just (KProcedure paramNames) -> do
      label <- labelFor pname loc $ "call_" ++ procName
      next <- labelFor pname loc $ "return_from_" ++ procName
      args' <- mapM (fixReads kenv) args
      myFrames <- fixReads kenv (EVar noLocation framesVar)
      myRet <- fixReads kenv (EVar loc retVar)
      useReturnValue' <- useReturnValue myRet
      let {instrs procs = [
        setMy SimpleAssignDet framesVar (EBinaryOp noLocation Concat myFrames (EMkTuple loc [EMkRecord noLocation (zip paramNames args')])),
        setPc (EBinaryOp noLocation Concat (replaceTop myPc (EStr noLocation next)) (EMkTuple noLocation [EStr noLocation (procs procName)]))]}
      return (label, unionTransitionSets [
        singleIncompleteTransition label (\procs _ -> commonPrefix loc label ++ instrs procs),
        mkStatementTransition loc next (useReturnValue'++)
        ], [])
    Just _ -> errorAt s $ "Cannot call variable " ++ show procName
    Nothing -> errorAt s $ "There is no procedure named " ++ show procName

lval2exp :: LValue a -> Exp a
lval2exp (LVar a v) = EVar a v
lval2exp (LIndex a lval i) = EIndex a (lval2exp lval) i
lval2exp (LField a lval f) = EGetField a (lval2exp lval) f

asSimpleAssignment :: (MonadFail m) => KEnv -> LValue SourceLocation -> Exp SourceLocation -> m (Id, Exp SourceLocation)
asSimpleAssignment env lval@(LVar a v) e =
  case M.lookup v env of
    Just KInternalGlobalVar -> return (v, e)
    Just KUserDefinedGlobalVar -> return (globalsScratchVar, EExcept a (EVar a globalsScratchVar) (EStr a v) e)
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

convertTransition :: KEnv -> NamedTransition SourceLocation -> NamesOp TLACode
convertTransition kenv (name, instrs) = do
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
        KInternalGlobalVar -> Just (v, v)
        KUserDefinedGlobalVar -> Just (v, v)
        KPerProcessVar -> Just (v, v)
        _ -> Nothing

mkEnv :: Module SourceLocation -> KEnv
mkEnv (Module _ vars procs) = do
  M.unions [
    M.singleton pcVar KPerProcessVar,
    M.singleton framesVar KPerProcessVar,
    M.singleton globalsScratchVar KInternalGlobalVar,
    M.singleton retVar KPerProcessVar,
    M.singleton actorVar KInternalGlobalVar,
    M.fromList [(variableBeingDeclared decl, KUserDefinedGlobalVar) | decl <- vars],
    M.fromList [(procedureName p, KProcedure (procedureParameters p)) | p <- procs]]
