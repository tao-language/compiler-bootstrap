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

instance Show Location where
  show :: Location -> String
  show (Location filename start _) =
    filename ++ ":" ++ show start.row ++ ":" ++ show start.col
