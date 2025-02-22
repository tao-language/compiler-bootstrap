module Location where

data Position = Pos
  { row :: Int,
    col :: Int
  }
  deriving (Eq)

instance Show Position where
  show :: Position -> String
  show p = show p.row ++ ":" ++ show p.col

data Range = Range
  { start :: Position,
    end :: Position
  }
  deriving (Eq)

instance Show Range where
  show :: Range -> String
  show r = show r.start ++ ".." ++ show r.end

data Location = Location
  { filename :: FilePath,
    range :: Range
  }
  deriving (Eq)

instance Show Location where
  show :: Location -> String
  show l = l.filename ++ ":" ++ show l.range

prev :: Int -> Position -> Position
prev n pos = pos {col = pos.col - n}
