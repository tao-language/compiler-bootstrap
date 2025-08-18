module PrettyPrint where

-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

type Layout = [Segment]

data Segment
  = Text String
  | NewLine
  | Indent Layout
  | Or Layout Layout
  deriving (Eq, Show)

pretty :: Int -> (String, String) -> Layout -> String
pretty width (indent, startIndent) = render (width, 0) (indent, startIndent)

-- Common
join :: Layout -> [Layout] -> Layout
join _ [] = []
join _ [x] = x
join delim (x : xs) = x ++ delim ++ join delim xs

joinPrefix :: String -> [Layout] -> Layout
joinPrefix delim = joinPrefix' (delim, delim)

joinPrefix' :: (String, String) -> [Layout] -> Layout
joinPrefix' (delim1, delim2) xs = do
  let alt1 = join [Text delim1] xs
  let alt2 = join [NewLine, Text delim2] xs
  [Or alt1 alt2]

joinSuffix :: String -> [Layout] -> Layout
joinSuffix delim = joinSuffix' (delim, delim)

joinSuffix' :: (String, String) -> [Layout] -> Layout
joinSuffix' (delim1, delim2) xs = do
  let alt1 = join [Text delim1] xs
  let alt2 = join [Text delim2, NewLine] xs
  [Or alt1 alt2]

-- Helper functions
render :: (Int, Int) -> (String, String) -> Layout -> String
-- w: width (constant)
-- k: current width (variable)
-- i: indent (constant)
-- j: current indent (variable)
render _ _ [] = ""
render (w, _) (i, j) (NewLine : NewLine : y) = "\n" ++ render (w, length j) (i, j) (NewLine : y)
render (w, _) (i, j) (NewLine : y) = "\n" ++ j ++ render (w, length j) (i, j) y
render (w, k) (i, j) (Text (c : s) : y) = c : render (w, k + 1) (i, j) (Text s : y)
render (w, k) (i, j) (Text "" : y) = render (w, k) (i, j) y
render (w, k) (i, j) (Indent x : y) = render (w, k) (i, j ++ i) x ++ render (w, k) (i, j) y
render (w, k) (i, j) (Or x _ : y) | fits (w - k) (x ++ y) = render (w, k) (i, j) (x ++ y)
render (w, k) (i, j) (Or _ x : y) = render (w, k) (i, j) (x ++ y)

fits :: Int -> Layout -> Bool
fits w _ | w < 0 = False
fits _ [] = True
fits _ (NewLine : _) = True
fits w (Text (_ : s) : y) = fits (w - 1) (Text s : y)
fits w (Text "" : y) = fits w y
fits w (Indent x : y) = fits w (x ++ y)
fits w (Or x y : z) = fits w (x ++ y) || fits w (y ++ z)

isMultiLine :: Layout -> Bool
isMultiLine [] = False
isMultiLine (NewLine : _) = True
isMultiLine (Text _ : b) = isMultiLine b
isMultiLine (Indent a : b) = isMultiLine (a ++ b)
isMultiLine (Or a b : c) = isMultiLine (a ++ b ++ c)

isSingleLine :: Layout -> Bool
isSingleLine = not . isMultiLine
