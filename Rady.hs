{-# LANGUAGE GADTs, MultiParamTypeClasses, FlexibleInstances, TypeApplications, DataKinds, ScopedTypeVariables, TypeFamilies, UndecidableInstances, AllowAmbiguousTypes #-}
module Rady (
    Canonical,
    Unitary,
    Pass,
    UnitLike,
    PairCan,
    Can,
    can,
    pass,
    anything,
    eq,
    opt,
    Shape(..),
    parse,
    lparse,
    generate,
    pattern,
    Pattern(..),
    deriv,
    group,
    alt,
    vanish,
    interleave,
    accept,
    rejected
    ) where

import Data.Void
import Control.Monad (guard)

type family And (a :: Bool) (b :: Bool) :: Bool where
    And True True = True
    And _    _    = False

-- |Closed type family describing what a canonical type is.
type family Canonical a :: Bool where
    Canonical ((),a) = False
    Canonical (a,()) = False
    Canonical (a,b) = And (Canonical a) (Canonical b)
    Canonical (Either a b) = And (Canonical a) (Canonical b)
    Canonical (Maybe a) = Canonical a
    Canonical [a] = Canonical a
    Canonical (Pass _) = False
    Canonical _ = True

-- |Closed type family describing what is considered unitary.
type family Unitary a :: Bool where
    Unitary ()    = True
    Unitary (a,b) = And (Unitary a) (Unitary b)
    Unitary a     = False

newtype Pass a = Pass { unPass :: a }

-- |Corresponding type class for the 'Unitary' type class.
class UnitLike a where unit :: a
instance UnitLike () where unit = ()
instance (UnitLike a, UnitLike b) => UnitLike (a,b) where unit = (unit, unit)

-- |Canonicalization relation, 'b' is a canonical version of the 'a'.
class Can a b where
    trim :: a -> b
    fill :: b -> a

-- |The PairCan removes an unitary item from a pair.
class PairCan (k::Bool) (j::Bool) a b c where
    trimPairs :: (a,b) -> c
    fillPairs :: c -> (a,b)

instance (UnitLike (a,b)) => PairCan 'True 'True a b () where
    trimPairs (_,_) = ()
    fillPairs () = unit

instance (UnitLike a, Can b c) => PairCan 'True 'False a b c where
    trimPairs (_,a) = trim a
    fillPairs a = (unit, fill a)

instance (Can a c, UnitLike b) => PairCan 'False 'True a b c where
    trimPairs (a,_) = trim a
    fillPairs a = (fill a, unit)

instance (Can a c, Can b d) => PairCan 'False 'False a b (c,d) where
    trimPairs (a,b) = (trim a, trim b)
    fillPairs (a,b) = (fill a, fill b)

instance (Canonical (a,b) ~ False, PairCan (Unitary a) (Unitary b) a b c) => Can (a,b) c where
    trim = trimPairs @(Unitary a) @(Unitary b)
    fill = fillPairs @(Unitary a) @(Unitary b)

instance (Canonical (Either a b) ~ False, Can a c, Can b d) => Can (Either a b) (Either c d) where
    trim (Left x) = Left (trim x)
    trim (Right x) = Right (trim x)
    fill (Left x) = Left (fill x)
    fill (Right x) = Right (fill x)

instance (Canonical a ~ False, Can a b) => Can (Maybe a) (Maybe b) where
    trim = fmap trim
    fill = fmap fill

instance (Canonical a ~ False, Can a b) => Can [a] [b] where
    trim = fmap trim
    fill = fmap fill

instance Can (Pass a) a where
    trim = unPass
    fill = Pass

instance (Canonical a ~ True) => Can a a where
    trim = id
    fill = id

-- |Trim the corresponding type.
can :: Can a b => Shape x a -> Shape x b
can = Iso trim fill

-- |The `can` trims away the 'Pass' but disregards the 'x'.
pass :: Shape a x -> Shape a (Pass x)
pass = Iso Pass unPass

-- |Match any item, corresponds to '.'
anything :: Shape x x
anything = Match pure id

-- |Match any item that is equal to pattern, matches to 'a'.
eq :: Eq a => a -> Shape a ()
eq x = Match (guard . (==) x) (const x)

-- |Match optional item, corresponds to 'a?'
opt :: Shape x a -> Shape x (Maybe a)
opt = let fromEither (Left ()) = Nothing
          fromEither (Right a) = Just a
          toEither Nothing = Left ()
          toEither (Just a) = Right a
      in Iso fromEither toEither . Alt Empty

-- |Base shapes, first argument refers to the input alphabet.
--  Second argument is corresponding type.
data Shape x y where
    Reject     :: Shape x Void
    Empty      :: Shape x ()
    Match      :: (x -> Maybe y) -> (y -> x) -> Shape x y
    Group      :: Shape x a -> Shape x b -> Shape x (a,b)
    Alt        :: Shape x a -> Shape x b -> Shape x (Either a b)
    Star       :: Shape x a -> Shape x [a]
    Interleave :: Shape x a -> Shape x b -> Shape x (a,b)
    -- |The 'Iso' allows to customize the corresponding type.
    --  The input functions should be isomorphisms.
    Iso        :: (a -> b) -> (b -> a) -> Shape x a -> Shape x b

-- |parse and generate form an isomorphism,
--  given that the regular language presented by the Shape is unambiguous.

-- |Match on the input list and construct a derivation.
parse :: Shape x y -> [x] -> Maybe y
parse shape xs = accept (foldl deriv (pattern shape) xs)

-- |Variation of a parser that skips elements
-- |if they are rejected by the parser.
lparse :: Shape x y -> [x] -> Maybe y
lparse shape xs = accept (foldl lderiv (pattern shape) xs)
    where lderiv pat x = let pat' = deriv pat x
                         in if rejected pat' then pat else pat'

-- |Generate a matching sequence from a value of a corresponding type.
generate :: Shape x a -> a -> [x]
generate Reject a = absurd a
generate (Empty) _ = []
generate (Match _ f) x = [f x]
generate (Group f g) (x,y) = generate f x ++ generate g y
generate (Alt f g) (Left x) = generate f x
generate (Alt f g) (Right y) = generate g y
generate (Star f) xs = concat (map (generate f) xs)
generate (Interleave f g) (x,y) = generate f x ++ generate g y
generate (Iso k f z) x = generate z (f x)

-- |Converts the representation into a "pattern" that
--  can produce Brzozowski derivatives.
pattern :: Shape x a -> Pattern x a
pattern Reject = PReject
pattern (Empty) = PAccept ()
pattern (Match f _) = PMatch f
pattern (Group f g) = PGroup (,) (pattern f) (pattern g)
pattern (Alt f g) = PAlt id (pattern f) (pattern g)
pattern (Star f) = PStar (pattern f)
pattern (Interleave f g) = PInterleave (pattern f) (pattern g)
pattern (Iso f g z) = PWith f (pattern z)

-- |Pattern is internal representation for the 'Shape' during parsing.
--  The idea here is that we can do type-checked parsing.
--  Note that 'Empty' is 'PAccept ()'
data Pattern x a where
    PReject     :: Pattern x a
    PAccept     :: a -> Pattern x a
    PMatch      :: (x -> Maybe y) -> Pattern x y
    PGroup      :: (a -> b -> c) -> Pattern x a -> Pattern x b -> Pattern x c
    PAlt        :: (Either a b -> c) -> Pattern x a -> Pattern x b -> Pattern x c
    PStar       :: Pattern x a -> Pattern x [a]
    PInterleave :: Pattern x a -> Pattern x b -> Pattern x (a,b)
    PWith       :: (a -> b) -> Pattern x a -> Pattern x b

-- |Produce a Brzozowski derivative for the given input symbol.
deriv :: Pattern x a -> x -> Pattern x a
deriv PReject      j      = PReject
deriv (PAccept _)  j      = PReject
deriv (PMatch f)   j      = case f j of
                           Nothing -> PReject
                           Just x  -> PAccept x
deriv (PGroup k f g) j    = case accept f of
                           Just x  -> alt vanish (group k (deriv f j) g) (PWith (k x) (deriv g j))
                           Nothing -> group k (deriv f j) g
deriv (PAlt k f g)   j    = alt k (deriv f j) (deriv g j)
deriv (PStar f)    j      = group (:) (deriv f j) (PStar f)
deriv (PInterleave f g) j = alt vanish (interleave (deriv f j) g)
                                (interleave f (deriv g j))
deriv (PWith h f) j       = case (deriv f j) of
                           PAccept x -> PAccept (h x)
                           PReject   -> PReject
                           g'       -> PWith h g'

-- |Removes catenation whenever accepted or rejected item is derived.
group :: (a -> b -> c) -> Pattern x a -> Pattern x b -> Pattern x c
group k (PAccept x) g = PWith (k x) g
group k f (PAccept y) = PWith (\x -> k x y) f
group _ PReject     g = PReject
group _ _     PReject = PReject
group k f           g = PGroup k f g

-- |Removes alternation whenever either branch is clearly rejected.
alt :: (Either a b -> c) -> Pattern x a -> Pattern x b -> Pattern x c
alt k PReject g = PWith (k.Right) g
alt k f PReject = PWith (k.Left)  f
alt k f       g = PAlt k f g

-- |Small combinator to erase a 'Either' whenever the branches
--  do not represent actual parse trees.
vanish :: Either a a -> a
vanish (Left a)  = a
vanish (Right a) = a

-- |Removes interleaving whenever feasible.
interleave :: Pattern x a -> Pattern x b -> Pattern x (a,b)
interleave (PAccept x) g = PWith (\y -> (x,y)) g
interleave f (PAccept y) = PWith (\x -> (x,y)) f
interleave PReject     g = PReject
interleave f     PReject = PReject
interleave f           g = PInterleave f g

-- |Whether the pattern is an accepted string.
accept :: Pattern x a -> Maybe a
accept PReject           = Nothing
accept (PAccept x)       = Just x
accept (PMatch _)        = Nothing
accept (PGroup k f g)    = k <$> accept f <*> accept g
accept (PAlt k f g)      = case accept f of
    Just x  -> pure (k (Left x))      -- I would prefer to check ambiguity on regexes, but this is ok.
    Nothing -> (k.Right) <$> accept g
accept (PStar f)         = Just []
accept (PWith h g)       = fmap h (accept g)
accept (PInterleave f g) = (,) <$> accept f <*> accept g

-- |Whether the pattern refers to a plain rejection.
rejected :: Pattern x a -> Bool
rejected PReject           = True
rejected (PAccept x)       = False
rejected (PMatch _)        = False
rejected (PGroup k f g)    = rejected f
rejected (PAlt k f g)      = rejected f && rejected g
rejected (PStar f)         = False
rejected (PWith h g)       = rejected g
rejected (PInterleave f g) = rejected f || rejected g
