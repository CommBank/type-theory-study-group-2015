{-# LANGUAGE Rank2Types #-}

import Data.List
import Data.Monoid

-- The Monoid typeclass involves a type m equipped with an element
-- mempty :: m and a function mappend :: m -> m -> m, subject to the
-- conditions (not actually imposable in Haskell) that mappend mzero =
-- id = (flip mappend) mzero and that (mappend (mappend x y) z) =
-- (mappend x (mappend y z)). There is a derived operation mconcat ::
-- [m] -> m given by mconcat = foldl mappend mzero

-- I claim that in this case, polymorphic functions of type forall a.
-- Monoid a => a -> a -> a are classified by lists of Booleans. The
-- below indicates how this is supposed to work.

classify :: (forall a. Monoid a => a -> a -> a) -> [Bool]
classify f = f [False] [True]

declassify :: Monoid a => [Bool] -> a -> a -> a
declassify ls a b = mconcat (map (\x -> if x then b else a) ls)

-- Exercise: figure out why this is true. This will involve: firstly,
-- the category Monoid of Haskell types equipped with instantiations
-- of Monoid (figure out what the morphisms are); and secondly, the
-- functors F,G: Monoid --> Hask which take a monoid m to (i) the
-- underlying type of m and (ii) the product type m x m.

-- First figure out why it is reasonable to identify polymorphic
-- functions of type forall a. Monoid a => a -> a -> a with natural
-- transformations G ==> F.

-- Then figure out why [Bool] is the generic instance of a monoid
-- equipped with a pair of elements. Then by copying the kind of
-- argument we saw in the talk, explain the classification result
-- above.

-- Bonus exercise: figure out what [Bool] should really be replaced by
-- to take account of the fact that Haskell can't actually force the
-- monoid axioms to hold.
