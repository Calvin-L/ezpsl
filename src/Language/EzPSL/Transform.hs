module Language.EzPSL.Transform (transformBottomUp) where

import Language.EzPSL.Syntax


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
transformBottomUp f (ESetComprehension loc e clauses) = do
  e' <- transformBottomUp f e
  clauses' <- mapM transformClause clauses
  f (ESetComprehension loc e' clauses')
  where
    transformClause (SCMember clauseLoc x set) = do
      set' <- transformBottomUp f set
      return (SCMember clauseLoc x set')
    transformClause (SCFilter clauseLoc p) = do
      p' <- transformBottomUp f p
      return (SCFilter clauseLoc p')
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
  f (EExcept loc func' inputValueToOverride' newOutputValue')
transformBottomUp f (EQuant loc q arg domain predicate) = do
  domain' <- transformBottomUp f domain
  predicate' <- transformBottomUp f predicate
  f (EQuant loc q arg domain' predicate')
