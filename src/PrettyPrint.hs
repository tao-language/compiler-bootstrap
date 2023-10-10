module PrettyPrint where

-- https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf

type Doc = [Segment]

data Segment
  = Text !String
  | HardBreak
  | SoftBreak !String
  | Indent !String !Doc
  deriving (Eq)

render :: Int -> Int -> String -> Doc -> String
render _ _ _ [] = ""
render w k i (Text s : doc) = s ++ render w (k + length s) i doc
render w k i (HardBreak : doc) = '\n' : i ++ render w k i doc
render w k i (SoftBreak s : doc) | fits (w - k) (Text s : doc) = render w k i (Text s : doc)
render w k i (SoftBreak _ : doc) = render w k i (HardBreak : doc)
render w k i (Indent j x : doc) = render w k (i ++ j) x ++ render w k i doc

fits :: Int -> Doc -> Bool
fits w _ | w < 0 = False
fits w [] = True
fits w (Text s : doc) = fits (w - length s) doc
fits w (HardBreak : doc) = True
fits w (SoftBreak s : doc) = True
fits w (Indent i x : doc) = fits w x

join :: Doc -> [Doc] -> Doc
join _ [] = []
join _ [x] = x
join y (x : xs) = x ++ y ++ join y xs
