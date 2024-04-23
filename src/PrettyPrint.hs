module PrettyPrint where

-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

type Layout = [Segment]

data Segment
  = Text String
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
render (w, _) (i, j) (Text ('\n' : s) : y) = "\n" ++ j ++ render (w, length j) (i, j) (Text s : y)
render (w, k) (i, j) (Text (c : s) : y) = c : render (w, k + 1) (i, j) (Text s : y)
render (w, k) (i, j) (Text "" : y) = render (w, k) (i, j) y
render (w, k) (i, j) (Indent x : y) = render (w, k) (i, j ++ i) x ++ render (w, k) (i, j) y
render (w, k) (i, j) (Or x _ : y) | fits (w - k) (x ++ y) = render (w, k) (i, j) (x ++ y)
render (w, k) (i, j) (Or _ x : y) = render (w, k) (i, j) (x ++ y)

fits :: Int -> Layout -> Bool
fits w _ | w < 0 = False
fits _ [] = True
fits _ (Text ('\n' : _) : _) = True
fits w (Text (_ : s) : y) = fits (w - 1) (Text s : y)
fits w (Text "" : y) = fits w y
fits w (Indent x : y) = fits w (x ++ y)
fits w (Or x _ : y) = fits w (x ++ y)
