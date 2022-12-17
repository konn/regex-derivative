{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Text.Regex.Derivative (
  RE,
  matchesL,
  anySym,
  sym,
  psym,
  neg,
  (<&&>),
  (<&&),
  (&&>),
  (.&&.),
  (.||.),
  nullable,
  string,
  stringOf,
  eps,
  derivative,
) where

import Control.Alternative.Free
import Control.Applicative
import Control.Foldl qualified as L
import Control.Lens (Traversal, alaf)
import Data.Functor.Coyoneda
import Data.Monoid (Ap)
import Data.Monoid qualified as Monoid
import Data.String (IsString (..))

data RE1 c a where
  Sym1 :: c -> RE1 c c
  PSym1 :: (c -> Bool) -> RE1 c c
  (:<&&>:) :: RE c (a -> b) -> RE c a -> RE1 c b
  Neg1 :: RE c a -> RE1 c ()

newtype RE c a = RE {unRE :: Alt (Coyoneda (RE1 c)) a}
  deriving newtype (Functor, Applicative, Alternative)
  deriving (Semigroup, Monoid) via Ap (RE c) a

embed1 :: RE1 c a -> RE c a
{-# INLINE embed1 #-}
embed1 = RE . liftAlt . liftCoyoneda

eps :: RE c ()
{-# INLINE eps #-}
eps = pure ()

sym :: c -> RE c c
{-# INLINE sym #-}
sym = embed1 . Sym1

psym :: (c -> Bool) -> RE c c
{-# INLINE psym #-}
psym = embed1 . PSym1

neg :: RE c a -> RE c ()
{-# INLINE neg #-}
neg = embed1 . Neg1

(<&&>) :: RE c (a -> b) -> RE c a -> RE c b
{-# INLINE (<&&>) #-}
(<&&>) l r = embed1 $ l :<&&>: r

(<&&) :: RE c a -> RE c b -> RE c a
{-# INLINE (<&&) #-}
(<&&) = (<&&>) . fmap const

(&&>) :: RE c a -> RE c b -> RE c b
{-# INLINE (&&>) #-}
(&&>) = (<&&>) . fmap (const id)

(.&&.) :: RE c a -> RE c b -> RE c (a, b)
{-# INLINE (.&&.) #-}
(.&&.) = (<&&>) . fmap (,)

infixl 4 <&&>, <&&, &&>, .&&.

(.||.) :: RE c a -> RE c b -> RE c (Either a b)
{-# INLINE (.||.) #-}
l .||. r = Left <$> l <|> Right <$> r

infixl 3 .||.

string :: Traversable t => t c -> RE c (t c)
{-# INLINE string #-}
string = traverse sym

stringOf :: Traversal s t c c -> s -> RE c t
{-# INLINE stringOf #-}
stringOf f = f sym

instance (c ~ Char, str ~ [Char]) => IsString (RE c str) where
  fromString = string
  {-# INLINE fromString #-}

anySym :: RE c c
{-# INLINE anySym #-}
anySym = psym $ const True

matchesL :: Eq c => RE c a -> L.Fold c (Maybe a)
{-# INLINE matchesL #-}
matchesL re = L.Fold (flip derivative) re nullable

derivative :: forall c a. Eq c => c -> RE c a -> RE c a
derivative c = go
  where
    go :: RE c x -> RE c x
    go = goAlt . unRE

    goAlt :: Alt (Coyoneda (RE1 c)) x -> RE c x
    goAlt (Alt alts) = alaf Monoid.Alt foldMap goF alts

    goF :: AltF (Coyoneda (RE1 c)) x -> RE c x
    goF Pure {} = empty
    goF (Ap coy f) =
      goCo coy <**> RE f <|> nullable (RE $ liftAlt coy) <**> goAlt f

    goCo :: Coyoneda (RE1 c) x -> RE c x
    goCo (Coyoneda g f) = g <$> go1 f

    go1 :: RE1 c x -> RE c x
    go1 (Sym1 c')
      | c == c' = pure c
      | otherwise = empty
    go1 (PSym1 p)
      | p c = pure c
      | otherwise = empty
    go1 (l :<&&>: r) = go l <*> go r
    go1 (Neg1 re) = neg $ go re

{- | We need 'Foldable' to empty

>>> nullable @Maybe $ string "hoge" <|> pure "Empty"
Just "Empty"

>>> nullable @Maybe $ (,) <$> pure True <*> pure 42 <|> pure (False, 45)
Just (True,42)

>>> nullable @[] $ (,) <$> pure True <*> pure 42 <|> pure (False, 45)
[(True,42),(False,45)]

>>> nullable @Maybe $ pure "I'm null!" <|> string "vaa"
Just "I'm null!"

>>> nullable @Maybe $ many (sym 'c')
Just ""

>>> nullable @Maybe $ some $ sym 'd'
Nothing
-}
nullable :: (Alternative f) => RE c a -> f a
{-# INLINE nullable #-}
nullable = go
  where
    go :: Alternative g => RE c x -> g x
    {-# INLINE go #-}
    go = runAlt goCo . unRE

    goCo :: Alternative g => Coyoneda (RE1 c) x -> g x
    {-# INLINE goCo #-}
    goCo (Coyoneda g f) = g <$> go1 f

    go1 :: Alternative g => RE1 c b -> g b
    go1 Sym1 {} = empty
    go1 PSym1 {} = empty
    go1 (l :<&&>: r) = go l <*> go r
    go1 (Neg1 a) =
      maybe (pure ()) (const empty) $ go a
