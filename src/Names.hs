module Names (NamesOp, runNamesOp, freshName) where

import qualified Data.Map as M
import Control.Monad.State (State, get, put, evalState)

type NamesState = M.Map String Int
type NamesOp t = State NamesState t

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

runNamesOp :: NamesOp t -> t
runNamesOp op = evalState op (M.empty)
