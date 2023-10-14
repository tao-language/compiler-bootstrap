module PrettyPrint where

-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

type Doc = [Segment]

data Segment
  = NewLine
  | Text !String
  | IfBreak !Doc !Doc
  | Indent !String !Doc
  deriving (Eq, Show)

pretty :: Int -> Doc -> String
pretty width = render width 0 ""

render :: Int -> Int -> String -> Doc -> String
render _ _ _ [] = ""
render w _ i (NewLine : y) = "\n" ++ i ++ render w (length i) i y
render w k i (Text s : y) = s ++ render w (k + length s) i y
render w k i (IfBreak _ x : y) | fits (w - k) (x ++ y) = render w k i (x ++ y)
render w k i (IfBreak x _ : y) = render w k i (x ++ y)
render w k i (Indent _ x : y) | fits (w - k) (x ++ y) = render w k i (x ++ y)
render w k i (Indent j x : y) = render w k (i ++ j) x ++ render w k i (vertical y)

fits :: Int -> Doc -> Bool
fits w _ | w < 0 = False
fits _ [] = True
fits _ (NewLine : _) = True
fits w (Text s : y) = fits (w - length s) y
fits w (IfBreak _ x : y) = fits w (x ++ y)
fits w (Indent _ x : y) = fits w (x ++ y)

vertical :: Doc -> Doc
vertical [] = []
vertical (NewLine : y) = NewLine : vertical y
vertical (Text s : y) = Text s : vertical y
vertical (IfBreak x _ : y) = x ++ vertical y
vertical (Indent i x : y) = Indent i x : vertical y

-- Syntax sugar
join :: Doc -> [Doc] -> Doc
join _ [] = []
join _ [x] = x
join y (x : xs) = x ++ y ++ join y xs

group :: Doc -> Segment
group = Indent ""

break' :: Segment
break' = IfBreak [NewLine] []

space :: Segment
space = IfBreak [NewLine] [Text " "]

trailing :: Doc -> Segment
trailing x = IfBreak [group x, NewLine] []
