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

    let layout :: Tree -> Doc
        layout (Node s []) = [Text s]
        layout (Node s ts) =
          [ Text s,
            Text " [",
            group
              [ Indent "  " (break' : join [Text ",", space] items),
                trailing [Text ","]
              ],
            Text "]"
          ]
          where
            items = map layout ts

    pretty 18 (layout tree) `shouldBe` "aaa [\n  bbbbb [ccc, dd],\n  eee,\n  ffff [\n    gg, hhh, ii,\n  ],\n]"
