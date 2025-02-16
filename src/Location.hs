module Location where

data Position = Pos
  { row :: Int,
    col :: Int
  }
  deriving (Eq, Show)

data Location = Location
  { filename :: FilePath,
    start :: Position,
    end :: Position
  }
  deriving (Eq)
