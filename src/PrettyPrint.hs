module PrettyPrint where

-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

type Layout = [Segment]

data Segment
  = NewLine
  | Text String
  | Indent String Layout
  | Or Layout Layout
  deriving (Eq, Show)

pretty :: Int -> Layout -> String
pretty width = render width 0 ""

-- Common
join :: Layout -> [Layout] -> Layout
join _ [] = []
join _ [x] = x
join y (x : xs) = x ++ y ++ join y xs

-- Helper functions
render :: Int -> Int -> String -> Layout -> String
render _ _ _ [] = ""
render w _ i (NewLine : y) = "\n" ++ i ++ render w (length i) i y
render w k i (Text s : y) = s ++ render w (k + length s) i y
render w k i (Indent j x : y) = render w k (i ++ j) x ++ render w k i y
render w k i (Or x _ : y) | fits (w - k) (x ++ y) = render w k i (x ++ y)
render w k i (Or _ x : y) = render w k i (x ++ y)

fits :: Int -> Layout -> Bool
fits w _ | w < 0 = False
fits _ [] = True
fits _ (NewLine : _) = True
fits w (Text s : y) = fits (w - length s) y
fits w (Indent _ x : y) = fits w (x ++ y)
fits w (Or x _ : y) = fits w (x ++ y)
