{-# LANGUAGE DeriveFunctor #-}

module Language.EzPSL.Syntax where

import Data.Annotated

type Id = String
type FieldName = String

data UnaryOp
  = Not | Negate | UnionAll | AllSubsets
  deriving (Eq, Ord, Show)

data BinaryOp
  -- comparisons
  = Eq | Ne | Gt | Ge | Lt | Le
  -- booleans
  | And | Or | Implies
  -- integers
  | Plus | Minus | Times | Divide | Mod | Exp
  -- sequences and strings
  | Concat
  -- sets
  | In | Subset | Union | Intersection | SetDifference
  -- functions (aka maps)
  | SingletonMapping | LeftBiasedMapUnion
  deriving (Eq, Ord, Show)

data Quantifier
  = Forall | Exists | Choose
  deriving (Eq, Ord, Show)

data Exp a
  = EVar      a Id
  | EInt      a Integer
  | EStr      a String
  | EThreadID a
  | EUnaryOp  a UnaryOp (Exp a)
  | EBinaryOp a BinaryOp (Exp a) (Exp a)
  | ECall     a Id [Exp a]
  | EMkFunc   a Id (Exp a) (Exp a)
  | EIndex    a (Exp a) (Exp a)
  | EExcept   a (Exp a) (Exp a) (Exp a) -- ^ [e EXCEPT ![i] = newval]
  | EMkRecord a [(FieldName, Exp a)]
  | EGetField a (Exp a) FieldName
  | EMkSet    a [Exp a]
  | EMkTuple  a [Exp a]
  | ECond     a (Exp a) (Exp a) (Exp a)
  | EQuant    a Quantifier Id (Exp a) (Exp a)
  deriving (Eq, Ord, Show, Functor)

data LValue a
  = LVar   a Id
  | LIndex a (LValue a) (Exp a)
  | LField a (LValue a) FieldName
  deriving (Eq, Ord, Show, Functor)

data Stm a
  = Skip   a
  | Assign a (LValue a) (Exp a)
  | NondeterministicAssign a (LValue a) (Exp a) (Exp a)
  | If     a (Exp a) (Stm a) (Stm a)
  | Either a [Stm a]
  | While  a (Exp a) (Stm a)
  | Await  a (Exp a)
  | Assert a (Exp a)
  | Yield  a
  | Call   a Id [Exp a]
  | CallAndSaveReturnValue a (LValue a) Id [Exp a]
  | Return a (Maybe (Exp a))
  | Seq    a (Stm a) (Stm a)
  deriving (Eq, Ord, Show, Functor)

data Annotation
  = EntryPoint
  deriving (Eq, Ord, Show)

data Procedure a
  = Procedure {
    procedureSyntaxAnnotation :: a,
    procedureAnnotations :: [Annotation],
    procedureName :: Id,
    procedureParameters :: [Id],
    procedureLocals :: [VarDecl a],
    procedureBody :: Stm a }
  deriving (Eq, Ord, Show, Functor)

data VarDecl a
  = VarDecl a Id (Exp a)
  deriving (Eq, Ord, Show, Functor)

data Module a
  = Module a [VarDecl a] [Procedure a]
  deriving (Eq, Ord, Show, Functor)

instance Annotated Exp where
  getAnnotation (EVar      a _)       = a
  getAnnotation (EInt      a _)       = a
  getAnnotation (EStr      a _)       = a
  getAnnotation (EThreadID a)         = a
  getAnnotation (EUnaryOp  a _ _)     = a
  getAnnotation (EBinaryOp a _ _ _)   = a
  getAnnotation (ECall     a _ _)     = a
  getAnnotation (EMkFunc   a _ _ _)   = a
  getAnnotation (EIndex    a _ _)     = a
  getAnnotation (EExcept   a _ _ _)   = a
  getAnnotation (EMkRecord a _)       = a
  getAnnotation (EGetField a _ _)     = a
  getAnnotation (EMkSet    a _)       = a
  getAnnotation (EMkTuple  a _)       = a
  getAnnotation (ECond     a _ _ _)   = a
  getAnnotation (EQuant    a _ _ _ _) = a

instance Annotated Stm where
  getAnnotation (Skip   a)       = a
  getAnnotation (Assign a _ _)   = a
  getAnnotation (NondeterministicAssign a _ _ _) = a
  getAnnotation (If     a _ _ _) = a
  getAnnotation (Either a _)     = a
  getAnnotation (While  a _ _)   = a
  getAnnotation (Await  a _)     = a
  getAnnotation (Assert a _)     = a
  getAnnotation (Yield  a)       = a
  getAnnotation (Call   a _ _)   = a
  getAnnotation (CallAndSaveReturnValue a _ _ _) = a
  getAnnotation (Return a _)     = a
  getAnnotation (Seq    a _ _)   = a
