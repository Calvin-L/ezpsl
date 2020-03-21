module Names (NamesOp, runNamesOp, freshName) where

import Control.Monad (liftM, ap)
import qualified Data.Map as M

type NamesState = M.Map String Int
newtype NamesOp t = NamesOp (NamesState -> Either String (NamesState, t))

instance Functor NamesOp where
  fmap = liftM

instance Applicative NamesOp where
  pure x = NamesOp $ \st -> Right (st, x)
  (<*>) = ap

instance Monad NamesOp where
  return = pure
  (>>=) (NamesOp op) f = NamesOp $ \st ->
    case op st of
      Left err -> Left err
      Right (st', val) ->
        let NamesOp f' = f val in
        f' st'

instance MonadFail NamesOp where
  fail = NamesOp . const . Left

get :: NamesOp NamesState
get = NamesOp $ \st -> Right (st, st)

put :: NamesState -> NamesOp ()
put st = NamesOp $ const $ Right (st, ())

findName :: String -> (String -> Bool) -> String
findName x predicate
  | predicate x = x
  | otherwise = loop 0
    where
      loop :: Integer -> String
      loop i =
        let x' = x ++ "_" ++ show i in
        if predicate x'
          then x'
          else loop (i+1)

freshName :: String -> NamesOp String
freshName hint = do
  m <- get
  case M.lookup hint m of
    Nothing -> do
      put (M.insert hint 1 m)
      return hint
    Just count -> do
      put (M.insert hint (count + 1) m)
      return $ hint ++ "_" ++ show count

runNamesOp :: (MonadFail m) => NamesOp t -> m t
runNamesOp (NamesOp op) =
  case op $ M.empty of
    Left err -> fail err
    Right (_, out) -> return out
