{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Text.Regex.Derivative (
  RE,
  matchL,
  premapRE,
  reFoldl,
  anySym,
  sym,
  psym,
  msym,
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
import Control.Monad (guard)
import Data.Function ((&))
import Data.Functor.Coyoneda
import Data.Monoid (Ap)
import Data.Monoid qualified as Monoid
import Data.Profunctor hiding (Star)
import Data.String (IsString (..))

data RE1 c a where
  MSym1 :: (c -> Maybe a) -> RE1 c a
  (:<&&>:) :: RE c (a -> b) -> RE c a -> RE1 c b
  Neg1 :: RE c a -> RE1 c ()
  Star :: (b -> a -> b) -> b -> RE c a -> RE1 c b

newtype RE c a = RE {unRE :: Alt (Coyoneda (RE1 c)) a}
  deriving newtype (Functor, Applicative, Alternative)
  deriving (Semigroup, Monoid) via Ap (RE c) a

embed1 :: RE1 c a -> RE c a
{-# INLINE embed1 #-}
embed1 = RE . liftAlt . liftCoyoneda

eps :: RE c ()
{-# INLINE eps #-}
eps = pure ()

reFoldl :: (b -> a -> b) -> b -> RE s a -> RE s b
{-# INLINE reFoldl #-}
reFoldl = fmap (fmap embed1) . Star

sym :: Eq c => c -> RE c c
{-# INLINE sym #-}
sym = psym . (==)

msym :: (c -> Maybe a) -> RE c a
{-# INLINE msym #-}
msym = embed1 . MSym1

psym :: (c -> Bool) -> RE c c
{-# INLINE psym #-}
psym p = msym $ \c -> c <$ guard (p c)

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

string :: (Traversable t, Eq c) => t c -> RE c (t c)
{-# INLINE string #-}
string = traverse sym

stringOf :: Eq c => Traversal s t c c -> s -> RE c t
{-# INLINE stringOf #-}
stringOf f = f sym

instance (c ~ Char, str ~ [Char]) => IsString (RE c str) where
  fromString = string
  {-# INLINE fromString #-}

anySym :: RE c c
{-# INLINE anySym #-}
anySym = msym Just

premapRE :: forall c' c a. (c' -> c) -> RE c a -> RE c' a
premapRE g = go'
  where
    go' :: RE c x -> RE c' x
    go' = runAlt (lowerCoyoneda . hoistCoyoneda go) . unRE
    go :: RE1 c x -> RE c' x
    go = \case
      MSym1 p -> msym $ p . g
      Neg1 p -> neg $ go' p
      l :<&&>: r -> go' l <&&> go' r
      Star step z re -> reFoldl step z (go' re)

instance Profunctor RE where
  lmap = premapRE
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}

matchL :: RE c a -> L.Fold c (Maybe a)
{-# INLINE matchL #-}
matchL re = L.Fold (flip derivative) re nullable

derivative :: forall c a. c -> RE c a -> RE c a
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
    go1 (MSym1 p) = maybe empty pure $ p c
    go1 (l :<&&>: r) = go l <&&> go r
    go1 (Neg1 re) = neg $ go re
    go1 (Star step (z :: z) re) =
      go (step z <$> re)
        <**> reFoldl
          (\lft !a !w -> lft $! step w a)
          id
          re

{- |

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
    {-# SPECIALIZE INLINE go :: RE c x -> Maybe x #-}
    go = runAlt (lowerCoyoneda . hoistCoyoneda go1) . unRE

    go1 :: Alternative g => RE1 c b -> g b
    {-# SPECIALIZE INLINE go1 :: RE1 c x -> Maybe x #-}
    {-# INLINE go1 #-}
    go1 = \case
      MSym1 {} -> empty
      l :<&&>: r -> go l <*> go r
      Neg1 a -> maybe (pure ()) (const empty) $ go a
      Star _ z _ -> pure z
