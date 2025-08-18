module PrettyPrintTests where

import Data.List (intercalate)
import PrettyPrint
import Test.Hspec

data Tree = Node !String ![Tree]

run :: SpecWith ()
run = describe "--==☯ Pretty print ☯==--" $ do
  -- Start with one level of indentation to see how newlines render.
  let render' width = render (width, 0) ("  ", "  ")

  it "☯ pretty.join" $ do
    let layout = join [Text ","] [[Text "a"], [Text "bb"], [Text "ccc"]]
    render' 0 layout `shouldBe` "a,bb,ccc"

  it "☯ pretty.joinPrefix" $ do
    let layout = joinPrefix ", " [[Text "a"], [Text "bb"], [Text "ccc"]]
    render' 10 layout `shouldBe` "a, bb, ccc"
    render' 9 layout `shouldBe` (intercalate "\n") ["a", "  , bb", "  , ccc"]

  it "☯ pretty.joinSuffix" $ do
    let layout = joinSuffix' (", ", ",") [[Text "a"], [Text "bb"], [Text "ccc"]]
    render' 10 layout `shouldBe` "a, bb, ccc"
    render' 9 layout `shouldBe` (intercalate "\n") ["a,", "  bb,", "  ccc"]

  it "☯ pretty.fromRight" $ do
    let ab = Or [Text "(a, b)"] [Text "( a,", NewLine, Text "b )"]
    let cd = Or [Text "(c, d)"] [Text "( c,", NewLine, Text "d )"]
    let layout = [ab, Text " -> ", cd]
    render' 16 layout `shouldBe` "(a, b) -> (c, d)"
    render' 15 layout `shouldBe` "(a, b) -> ( c,\n  d )"

  it "☯ pretty.binary-tree" $ do
    -- Example from paper:
    --   https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf
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
              [Indent (NewLine : join [Text ",", NewLine] items), Text ",", NewLine],
            Text
              "]"
          ]
          where
            items = map layout ts

    let expected =
          [ "aaa [bbbbb [ccc, dd], eee, ffff [",
            "  gg,",
            "  hhh,",
            "  ii,",
            "]]"
          ]
    pretty 40 ("  ", "") (layout tree) `shouldBe` intercalate "\n" expected

    let expected =
          [ "aaa [bbbbb [",
            "  ccc,",
            "  dd,",
            "], eee, ffff [gg, hhh, ii]]"
          ]
    pretty 30 ("  ", "") (layout tree) `shouldBe` intercalate "\n" expected

    let expected =
          [ "aaa [bbbbb [",
            "  ccc,",
            "  dd,",
            "], eee, ffff [",
            "  gg,",
            "  hhh,",
            "  ii,",
            "]]"
          ]
    pretty 20 ("  ", "") (layout tree) `shouldBe` intercalate "\n" expected

    let expected =
          [ "aaa [",
            "  bbbbb [",
            "    ccc,",
            "    dd,",
            "  ],",
            "  eee,",
            "  ffff [",
            "    gg,",
            "    hhh,",
            "    ii,",
            "  ],",
            "]"
          ]
    pretty 10 ("  ", "") (layout tree) `shouldBe` intercalate "\n" expected
