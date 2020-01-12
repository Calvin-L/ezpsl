module Data.SourceLocation (
  SourceLocation(SourceLocation, line, column)
  ) where

-- | A type for representing locations in a souce file.
data SourceLocation = SourceLocation {
  line :: Int,
  column :: Int}
  deriving (Eq, Ord, Show)
