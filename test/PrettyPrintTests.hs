module PrettyPrintTests where

import Debug.Trace
import PrettyPrint
import Test.Hspec

data Tree = Node !String ![Tree]

run :: SpecWith ()
run = describe "--==☯ Pretty print ☯==--" $ do
  it "☯ Binary tree" $ do
    let tree =
          Node
            "aaa"
            [ Node
                "bbbbb"
                [ Node "ccc" [],
                  Node "dd" []
                ],
              Node "eee" [],
              Node
                "ffff"
                [ Node "gg" [],
                  Node "hhh" [],
                  Node "ii" []
                ]
            ]

    let pretty :: Tree -> Doc
        pretty (Node s []) = [Text s]
        pretty (Node s ts) =
          [ Text s,
            Text " [",
            Indent "  " (SoftBreak "" : join [Text ",", SoftBreak " "] (map pretty ts)),
            SoftBreak "",
            Text "]"
          ]

    let w = 15
    Debug.Trace.traceM ('\n' : render w 0 "" (pretty tree))
    render w 0 "" (pretty tree) `shouldBe` ""
    True `shouldBe` True
