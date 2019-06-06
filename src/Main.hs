{-# LANGUAGE
  ExistentialQuantification
  , ConstraintKinds
  , KindSignatures
  , RankNTypes
  , ScopedTypeVariables
  , DeriveFunctor
  , DeriveTraversable
  , BangPatterns
  , FunctionalDependencies
  , InstanceSigs
  , StandaloneDeriving
  , UnicodeSyntax
  , ImpredicativeTypes
  , FlexibleInstances
  , FlexibleContexts
  , ScopedTypeVariables
  , LambdaCase
#-}

{-# LANGUAGE DeriveGeneric #-}

module Main where

import Prelude hiding (or)
import GHC.Generics (Generic)
import Data.Hashable
import Data.IORef
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Control.Monad.Reader (ReaderT, runReaderT)

data Type = Fin  Integer
          | Prod Type Type
          | Sum  Type Type
          | Arr  Type Type
          | Forall Type
          | Use Int
  deriving (Show, Eq, Ord, Generic)

instance Hashable Type

isFree :: Int -> Type -> Bool
isFree _ (Fin _)    = True
isFree t (Prod l r) = isFree t l && isFree t r
isFree t (Sum l r)  = isFree t l && isFree t r
isFree t (Arr l r)  = isFree t l && isFree t r
isFree t (Use i)    = i /= t
isFree t (Forall e) = isFree (t + 1) e

isFunctor :: Bool -> Int -> Type -> Bool
isFunctor pos t (Fin _)    = True
isFunctor pos t (Prod l r) = isFunctor pos t l && isFunctor pos t l
isFunctor pos t (Sum l r)  = isFunctor pos t l && isFunctor pos t l
isFunctor pos t (Arr l r)  = isFunctor (not pos) t l && isFunctor pos t l
isFunctor pos t (Use i)    = if i == t then pos else True
isFunctor pos t (Forall e) = isFunctor pos (t + 1) e

isCovariant     = isFunctor True
isContravariant = isFunctor False

adjustFree :: Int -> Int -> Type -> Type
adjustFree _ _ e@(Fin _) = e
adjustFree inc depth (Prod l r) = Prod (adjustFree inc depth l) (adjustFree inc depth r)
adjustFree inc depth (Sum l r)  = Sum  (adjustFree inc depth l) (adjustFree inc depth r)
adjustFree inc depth (Arr l r)  = Arr  (adjustFree inc depth l) (adjustFree inc depth r)
adjustFree inc depth (Use i)    = if i >= depth then Use (i + inc) else Use i
adjustFree inc depth (Forall e) = Forall (adjustFree inc (depth + 1) e)

subst :: Int -> Int -> Type -> Type -> Type
subst _ _ _ e@(Fin _) = e
subst tgt depth tree (Prod l r) = Prod (subst tgt depth tree l) (subst tgt depth tree r)
subst tgt depth tree (Sum l r)  = Sum  (subst tgt depth tree l) (subst tgt depth tree r)
subst tgt depth tree (Arr l r)  = Arr  (subst tgt depth tree l) (subst tgt depth tree r)
subst tgt depth tree (Use i)    = if i == tgt then adjustFree depth 0 tree else Use i
subst tgt depth tree (Forall e) = Forall (subst (tgt + 1) (depth + 1) tree e)

data Rule = Rule {
  runRule :: Type -> [Type]
}

or :: Rule -> Rule -> Rule
or (Rule a) (Rule b) = Rule (\x -> a x ++ b x)

orElse :: Rule -> Rule -> Rule
orElse (Rule a) (Rule b) = Rule (\x -> case a x of [] -> b x; l -> l)

orId :: Rule -> Rule
orId (Rule a) = Rule (\x -> case a x of [] -> [x];
                                         l -> filter (/= x) l)

andId :: Rule -> Rule
andId (Rule a) = Rule (\x -> a x ++ [x])

bottomUp :: Rule -> Rule
bottomUp rule = Rule $
  \case e@(Fin _) -> runRule rule e
        e@(Use _) -> runRule rule e
        Sum l r   -> do
          a <- runRule (bottomUp rule) l
          b <- runRule (bottomUp rule) r
          runRule rule (Sum a b)
        Prod l r  -> do
          a <- runRule (bottomUp rule) l
          b <- runRule (bottomUp rule) r
          runRule rule (Prod a b)
        Arr l r  -> do
          a <- runRule (bottomUp rule) l
          b <- runRule (bottomUp rule) r
          runRule rule (Arr a b)
        Forall l  -> do
          a <- runRule (bottomUp rule) l
          runRule rule (Forall a)

fix :: Rule -> Rule
fix self = Rule $
  \e -> go (HS.fromList [e]) where
    go :: HS.HashSet Type -> [Type]
    go visited = if newSet == visited then HS.toList newSet else go newSet
      where newSet = HS.fromList $ (HS.toList visited >>= runRule self)

fixCumulative :: Rule -> Rule
fixCumulative self = Rule $
  \e -> go (HS.fromList [e]) where
    go :: HS.HashSet Type -> [Type]
    go visited = if newSet == visited then HS.toList newSet else go (HS.union newSet visited)
      where newSet = HS.fromList $ (HS.toList visited >>= runRule self)

andThen :: Rule -> Rule -> Rule
andThen a b = Rule (\e -> runRule a e >>= runRule b)

isoRule :: Rule
isoRule =
  foldl1 or $ fmap Rule [
  -- Commutativity
  (\case (Prod a b) -> [Prod b a];
         (Sum a b)  -> [Sum b a];
         _          -> []),
  -- Associativity
  (\case (Prod a (Prod b c)) -> [Prod (Prod a b) c]; _ -> []),
  (\case (Sum a (Sum b c))   -> [Sum (Sum a b) c];   _ -> []),
  (\case (Prod (Prod a b) c) -> [Prod a (Prod b c)]; _ -> []),
  (\case (Sum (Sum a b) c)   -> [Sum a (Sum b c)];   _ -> []),
  -- Distributivity
  (\case (Prod a (Sum b c)) -> [Sum (Prod a b) (Prod a c)]; _ -> []),
  (\case (Prod (Sum a b) c) -> [Sum (Prod a c) (Prod b c)]; _ -> []),
  -- Currying & uncurrying
  (\case (Arr (Prod a b) c) -> [Arr a (Arr b c)];  _ -> []),
  (\case (Arr a (Arr b c))  -> [Arr (Prod a b) c]; _ -> []),
  -- Distributivity of ->
  (\case (Arr (Sum a b) c)  -> [Prod (Arr a c) (Arr b c)]; _ -> []),
  (\case (Arr a (Prod b c)) -> [Prod (Arr a b) (Arr a c)]; _ -> [])
  ]

normRule :: Rule
normRule =
  foldl1 orElse $ fmap Rule [
  -- Sort of a hack, covers A \/ not A.
  (\case (Prod (Arr a (Fin 0)) b) | a == b -> [Fin 0]; _ -> []),
  (\case (Prod b (Arr a (Fin 0))) | a == b -> [Fin 0]; _ -> []),
  -- Fin simplifications
  (\case (Prod (Fin 0) _) -> [Fin 0];
         (Prod _ (Fin 0)) -> [Fin 0];

         (Prod (Fin 1) x) -> [x];
         (Prod x (Fin 1)) -> [x];
         (Sum (Fin 0) x)  -> [x];
         (Sum x (Fin 0))  -> [x];

         (Arr (Fin 0) _) -> [Fin 1];
         (Arr (Fin 1) x) -> [x];
         (Arr _ (Fin 1)) -> [Fin 1];

         (Prod (Fin a) (Fin b)) -> [Fin (a * b)];
         (Sum (Fin a) (Fin b))  -> [Fin (a + b)];
         (Arr (Fin a) (Fin b))  -> [Fin (b ^ a)];

         _ -> []),
  -- Yoneda
  (\case Forall fx | isCovariant     0 fx -> [subst 0 0 (Fin 0) fx]; _ -> []),
  (\case Forall fx | isContravariant 0 fx -> [subst 0 0 (Fin 1) fx]; _ -> []),
  (\case Forall (Arr (Use 0) fx) | isCovariant 0 fx -> [subst 0 0 (Fin 1) fx]; _ -> []),
  (\case Forall (Arr (Arr a (Use 0)) fx) | isFree 0 a && isCovariant 0 fx -> [subst 0 0 a fx]; _ -> [])
  ]


rule :: Rule
rule = fix (bottomUp $ orId normRule) `andThen` bottomUp (andId isoRule)

small :: Type -> Either [Type] Integer
small (Fin x) = Right x
small e = Left $ runRule rule e

solve :: (Hashable a, Eq a) => Int -> a -> (a -> Either [a] b) -> Either (HS.HashSet a) b
solve max seed small = go max [seed] HS.empty where
  go k l v | k <= 0 = Left v
  go _ [] v         = Left v
  go s (h : t) visited =
    if HS.member h visited then go (s - 1) t visited
    else case small h of
      Right b -> Right b
      Left more -> go (s - 1) (t ++ more) (HS.insert h visited)

main :: IO ()
main = do
  let x = Forall (Arr (Prod (Use 0) (Use 0)) (Use 0))
  print $ solve 2000 x small