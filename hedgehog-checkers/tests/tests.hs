{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Applicative
import           Data.Either.Validation
import           Data.Functor (void)
import           Data.Monoid (Sum(..))

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Hedgehog.Checkers

genValidation :: Gen a -> Gen b -> Gen (Validation a b)
genValidation ga gb = do
  a <- ga
  b <- gb
  Gen.choice [return $ Failure a, return $ Success b]

validationAlternative :: Property
validationAlternative = property $ do
  let genSumInt = Sum <$> Gen.int (Range.linear 0 maxBound)
      genVal = genValidation genSumInt genSumInt
  alternative genVal

genInt :: Gen Int
genInt = Gen.int (Range.linear 0 maxBound)

genEither' :: Gen a -> Gen b -> Gen (Either a b)
genEither' ga gb = do
  a <- ga
  b <- gb
  Gen.choice [return $ Left a, return $ Right b]

genEither :: Gen (Either Int Int)
genEither = genEither' genInt genInt

eitherAlt :: Property
eitherAlt = property $ do
  alt genEither
  altLeftDistributive genEither genInt genInt
  altRightDistributive (genEither' genInt) genEither genInt genInt

eitherBifunctor :: Property
eitherBifunctor = property $ do
  bifunctor genEither genInt genInt genInt

eitherFunctor :: Property
eitherFunctor = property $ do
  functor genEither

eitherApplicative :: Property
eitherApplicative = property $ do
  applicative genEither genInt genInt genInt

eitherSemigroup :: Property
eitherSemigroup = property $ do
  semigroup genEither

genMaybe' :: Gen a -> Gen (Maybe a)
genMaybe' ga = do
  a <- ga
  -- I need to bias this to Just
  Gen.choice [return $ Nothing, return $ Just a]

genMaybe :: Gen (Maybe (Sum Int))
genMaybe = genMaybe' (Sum <$> genInt)

maybeMonoid :: Property
maybeMonoid = property $ do
  monoid genMaybe

main :: IO ()
main = do
  void $
    checkParallel $
      Group "Data.Either" [ ("Alt", eitherAlt)
                          , ("Bifunctor", eitherBifunctor)
                          , ("Functor", eitherFunctor)
                          , ("Semigroup", eitherSemigroup)
                          , ("Applicative", eitherApplicative)
                          ]
  void $
    checkParallel $
      Group "Data.Maybe" [ ("Monoid", maybeMonoid)
                         ]
