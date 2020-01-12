module Data.Annotated where

class Functor t => Annotated t where
  getAnnotation :: t a -> a
