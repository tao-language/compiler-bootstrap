{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module CheckTests where

import Check
import Core (Error (..))
import qualified Core as C
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Check ☯==--" $ do
  it "☯ checkTypesExpr" $ do
    True `shouldBe` True

  it "☯ checkTypesStmt" $ do
    True `shouldBe` True

  it "☯ checkTypesFile" $ do
    True `shouldBe` True

  it "☯ checkTypes" $ do
    True `shouldBe` True
