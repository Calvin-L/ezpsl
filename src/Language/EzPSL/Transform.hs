module Language.EzPSL.Transform (transformBottomUp) where

import Control.Monad (foldM)

import Language.EzPSL.Syntax

-- | Transform an expression bottom-up.  The given rewrite function may be
--   monadic, and it is given (1) the list of in-scope bound variables and (2)
--   the expression to rewrite.  The list of bound variables is in reverse
--   order of introduction; more recently-bound variables are at the head of
--   the list.  If the same name is bound more than once, it will appear more
--   than once in the list.
transformBottomUp :: (Monad m, Show a) => ([Id] -> Exp a -> m (Exp a)) -> Exp a -> m (Exp a)
transformBottomUp f = helper []
  where
    helper boundVars e@(EBool _ _) = f boundVars e
    helper boundVars e@(EInt _ _) = f boundVars e
    helper boundVars e@(EStr _ _) = f boundVars e
    helper boundVars e@(EVar _ _) = f boundVars e
    helper boundVars e@(EThreadID _) = f boundVars e
    helper boundVars (EUnaryOp loc op e) = do
      e' <- helper boundVars e
      f boundVars (EUnaryOp loc op e')
    helper boundVars (EBinaryOp loc op e1 e2) = do
      e1' <- helper boundVars e1
      e2' <- helper boundVars e2
      f boundVars (EBinaryOp loc op e1' e2')
    helper boundVars (EIndex loc e1 e2) = do
      e1' <- helper boundVars e1
      e2' <- helper boundVars e2
      f boundVars (EIndex loc e1' e2')
    helper boundVars (EGetField loc e field) = do
      e' <- helper boundVars e
      f boundVars (EGetField loc e' field)
    helper boundVars (ECall loc func args) = do
      args' <- mapM (helper boundVars) args
      f boundVars (ECall loc func args')
    helper boundVars (EMkTuple loc args) = do
      args' <- mapM (helper boundVars) args
      f boundVars (EMkTuple loc args')
    helper boundVars (EMkSet loc args) = do
      args' <- mapM (helper boundVars) args
      f boundVars (EMkSet loc args')
    helper boundVars (ESetComprehension loc e clauses) = do
      -- NOTE: foldM visits elements left-to-right, and `transformClause`
      -- prepends the last-visited object last.  Thus, the transformed clauses
      -- are returned in reverse order, and the bound variables are in the
      -- order we want (i.e. most-recently-bound first).
      (clauses', bound') <- foldM transformClause ([], boundVars) clauses
      e' <- helper bound' e
      f boundVars (ESetComprehension loc e' (reverse clauses'))
      where
        transformClause (clauses', b) (SCMember clauseLoc x set) = do
          set' <- helper b set
          return (SCMember clauseLoc x set' : clauses', x : b)
        transformClause (clauses', b) (SCFilter clauseLoc p) = do
          p' <- helper b p
          return (SCFilter clauseLoc p' : clauses', b)
    helper boundVars (EMkRecord loc fields) = do
      fields' <- mapM (\(fieldName, e) -> do
        e' <- helper boundVars e
        return (fieldName, e')) fields
      f boundVars (EMkRecord loc fields')
    helper boundVars (ECond loc cond thenCase elseCase) = do
      cond' <- helper boundVars cond
      thenCase' <- helper boundVars thenCase
      elseCase' <- helper boundVars elseCase
      f boundVars (ECond loc cond' thenCase' elseCase')
    helper boundVars (EMkFunc loc param domain range) = do
      domain' <- helper boundVars domain
      range' <- helper (param : boundVars) range
      f boundVars (EMkFunc loc param domain' range')
    helper boundVars (EExcept loc func inputValueToOverride newOutputValue) = do
      func' <- helper boundVars func
      inputValueToOverride' <- helper boundVars inputValueToOverride
      newOutputValue' <- helper boundVars newOutputValue
      f boundVars (EExcept loc func' inputValueToOverride' newOutputValue')
    helper boundVars (EQuant loc q arg domain predicate) = do
      domain' <- helper boundVars domain
      predicate' <- helper (arg : boundVars) predicate
      f boundVars (EQuant loc q arg domain' predicate')
