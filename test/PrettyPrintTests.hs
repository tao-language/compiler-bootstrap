module PrettyPrintTests where

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

    let layout :: Tree -> Layout
        layout (Node s []) = [Text s]
        layout (Node s ts) =
          [ Text s,
            Text " [",
            Or
              (join [Text ", "] items)
              [Indent "  " (NewLine : join [Text ",", NewLine] items), Text ",", NewLine],
            Text "]"
          ]
          where
            items = map layout ts

    pretty 19 (layout tree) `shouldBe` "aaa [\n  bbbbb [ccc, dd],\n  eee,\n  ffff [\n    gg,\n    hhh,\n    ii,\n  ],\n]"
