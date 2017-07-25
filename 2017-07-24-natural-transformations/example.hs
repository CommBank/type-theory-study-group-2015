{-# LANGUAGE Rank2Types #-}
-- A rank 2 function is one taking a polymorphic function as an
-- argument, like classify below they are not a feature of Haskell's
-- default type system, so they need to be explicitly enabled


import Data.List

-- This function takes a polymorphic function of type [a]->[a] and
-- returns its classifying "signature"

classify :: (forall a. [a] -> [a]) -> Int -> [Int]
classify f n = f [0..(n-1)]

-- This takes a signature and reconstructs the corresponding
-- polymorphic function Note this does not work correctly on infinite
-- lists, since the call to length never returns. To fix this, one
-- needs to change the type of the signature from Int -> [Int] to
-- something more sophisticated

declassify :: (Int -> [Int]) -> [a] -> [a]
declassify g ls = map (ls !!) (g (length ls)) 


-- Here is the more sophisticated version. We represent a possibly
-- infinite natural number as a possibly infinite list of ()'s.

type Nat = [()]

zero :: Nat
zero =  []

succNat :: Nat -> Nat
succNat = (():)

-- this is the Nat version of \n -> [0..(n-1)] (which also works for the infinite natural number)

genericList :: Nat -> [Nat]
genericList n = genericList' n zero where
  genericList' [] _ = []
  genericList' (_:xs) m = m : (genericList' xs (succNat m))

-- this is the Nat version of length (which also works for infinite lists)

lengthNat :: [a] -> Nat
lengthNat = map (\_ -> ())

-- this is the Nat version of !!

takeNat :: [a] -> Nat -> a
takeNat = flip (foldl (\f _ -> f . tail) head)

-- These functions should now work on infinite lists just as well as
-- ordinary ones. Hopefully it should now be the case that
-- declassify2 . classify2 = id, though it still won't be the case
-- that classify2 . declassify2 = id (why not?)

classify2 :: (forall a. [a] -> [a]) -> Nat -> [Nat]
classify2 f n = f (genericList n)

declassify2 :: (Nat -> [Nat]) -> [a] -> [a]
declassify2 g ls = map (takeNat ls) (g (lengthNat ls))

-- Exercise: try doing something similar for the type forall a. Tree a -> [a],
-- where Data Tree a = Empty | Node a (Tree a) (Tree a). The role of
-- Nat will be taken by Tree ().
