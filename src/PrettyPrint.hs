module PrettyPrint where

-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

type Layout = [Segment]

data Segment
  = NewLine
  | Text String
  | Indent Layout
  | Or Layout Layout
  deriving (Eq, Show)

pretty :: Int -> String -> Layout -> String
pretty width indent = render (width, 0) (indent, "")

-- Common
join :: Layout -> [Layout] -> Layout
join _ [] = []
join _ [x] = x
join y (x : xs) = x ++ y ++ join y xs

-- Helper functions
render :: (Int, Int) -> (String, String) -> Layout -> String
render _ _ [] = ""
render (w, _) (i, j) (NewLine : y) = "\n" ++ j ++ render (w, length j) (i, j) y
render (w, k) (i, j) (Text s : y) = s ++ render (w, k + length s) (i, j) y
render (w, k) (i, j) (Indent x : y) = render (w, k) (i, j ++ i) x ++ render (w, k) (i, j) y
render (w, k) (i, j) (Or x _ : y) | fits (w - k) (x ++ y) = render (w, k) (i, j) (x ++ y)
render (w, k) (i, j) (Or _ x : y) = render (w, k) (i, j) (x ++ y)

fits :: Int -> Layout -> Bool
fits w _ | w < 0 = False
fits _ [] = True
fits _ (NewLine : _) = True
fits w (Text s : y) = fits (w - length s) y
fits w (Indent x : y) = fits w (x ++ y)
fits w (Or x _ : y) = fits w (x ++ y)
