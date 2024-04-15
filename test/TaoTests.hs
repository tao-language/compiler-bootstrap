{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NoFieldSelectors #-}

module TaoTests where

import Core
import qualified Parser as P
import Tao
import Test.Hspec

run :: SpecWith ()
run = describe "--==☯ Tao ☯==--" $ do
  it "☯ TODO'" $ do
    True `shouldBe` True
