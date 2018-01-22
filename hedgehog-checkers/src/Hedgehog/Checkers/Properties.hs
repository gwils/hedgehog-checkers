
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Hedgehog.Checkers.Properties
  (
  -- | Laws
    identity
  , leftIdentity
  , rightIdentity
  , associativity
  , leftDistributive
  , rightDistributive
  , commutativity
  , reflexive
  , transitive
  , symmetric
  , antiSymmetric
  ) where

import Hedgehog

import Hedgehog.Checkers.Ugly.Function.Hack


leftIdentity :: (Eq a, Show a)
             => (a -> a -> a)
             -> a
             -> Gen a
             -> PropertyT IO ()
leftIdentity f i gen = do
  x <- forAll gen
  f i x === x

rightIdentity :: (Eq a, Show a)
              => (a -> a -> a)
              -> a
              -> Gen a
              -> PropertyT IO ()
rightIdentity f i gen = do
  x <- forAll gen
  f x i === x

identity :: (Eq a, Show a)
         => (a -> a -> a)
         -> a
         -> Gen a
         -> PropertyT IO ()
identity f i gen = do
  leftIdentity f i gen
  rightIdentity f i gen

associativity :: (Eq a, Show a)
              => (a -> a -> a)
              -> Gen a
              -> PropertyT IO ()
associativity f gen = do
  x <- forAll gen
  y <- forAll gen
  z <- forAll gen
  f x (f y z) === f (f x y) z

commutativity :: (Eq b, Show a, Show b)
              => (a -> a -> b)
              -> Gen a
              -> PropertyT IO ()
commutativity f gena = do
  a <- forAll gena
  a' <- forAll gena
  f a a' === f a' a

reflexive :: (Show a)
          => (a -> a -> Bool)
          -> Gen a
          -> PropertyT IO ()
reflexive rel gena = do
  a <- forAll gena
  assert $ rel a a

transitive :: (Show a)
           => (a -> a -> Bool)
           -> Gen a
           -> (a -> Gen a)
           -> PropertyT IO ()
transitive rel gena genf = do
  a <- forAll gena
  b <- forAll (genf a)
  c <- forAll (genf b)
  ((rel a b) && (rel b c)) === (rel a c)

symmetric :: (Show a)
          => (a -> a -> Bool)
          -> Gen a
          -> (a -> Gen a)
          -> PropertyT IO ()
symmetric rel gena genf = do
  a <- forAll gena
  b <- forAll (genf a)
  (rel a b) === (rel b a)

-- need classify and cover
-- isTotalOrder :: (Arbitrary a,Show a,Ord a) => a -> a -> Property
-- isTotalOrder x y =
--     classify (x > y)  "less than" $
--     classify (x == y) "equals" $
--     classify (x < y)  "greater than" $
--     x < y || x == y || x > y

leftDistributive :: ( Ord a
                    , Eq (f b)
                    , Show (f a)
                    , Show (f b)
                    )
                 => (forall p q. (p -> q) -> f p -> f q) -> (forall z. f z -> f z -> f z) -> Gen (f a) -> Gen a -> Gen b -> PropertyT IO ()
leftDistributive x y genFa genA genB = do
  f <- ordFuncWtf genA genB
  a <- forAll genFa
  b <- forAll genFa
  (f `x` (a `y` b)) === ((f `x` a) `y` (f `x` b))

rightDistributive :: ( Ord a
                     , Eq (f b)
                     , Show (f a)
                     , Show (f b)
                     )
                  => (forall z. f z -> f z -> f z) -> (forall p q. f (p -> q) -> f p -> f q) -> (Gen (a -> b) -> Gen (f (a -> b))) -> Gen (f a) -> Gen a -> Gen b -> PropertyT IO ()
rightDistributive x y f genFa genA genB = do
  let func = funcForAllWtf (f (ordFuncWtf' genA genB))
  a <- func
  b <- func
  c <- forAll genFa
  ((a `x` b) `y` c) === ((a `y` c) `x` (b `y` c))

antiSymmetric :: (Eq a, Show a)
              => (a -> a -> Bool)
              -> Gen a
              -> (a -> Gen a)
              -> PropertyT IO ()
antiSymmetric rel gena genf = do
  a <- forAll gena
  b <- forAll (genf a)
  ((rel a b) && (rel b a)) === (a == b)
