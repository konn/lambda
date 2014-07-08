{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable           #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction, TypeOperators                   #-}
module Lambda where
import Bound
import Control.Applicative       (Applicative (..), (<$>), (<|>))
import Control.Eff
import Control.Eff.Reader.Strict (Reader, ask, local, runReader)
import Control.Monad             (ap)
import Data.DList                (singleton, snoc, toList)
import Data.Foldable             (Foldable)
import Data.Maybe                (fromMaybe)
import Data.Traversable          (Traversable)
import Prelude.Extras

data Term a = Var a
            | App (Term a) (Term a)
            | Abs (Scope () Term a)
            deriving (Read, Show, Eq, Ord, Functor, Foldable, Traversable)

instance Eq1 Term
instance Ord1 Term
instance Read1 Term
instance Show1 Term
instance Applicative Term where
  pure  = Var
  (<*>) = ap

instance Monad Term where
  return = Var
  Var a   >>= f = f a
  App x y >>= f = App (x >>= f) (y >>= f)
  Abs e   >>= f = Abs (e >>>= f)

infixl 1 @:

(@:) :: Term a -> Term a -> Term a
(@:) = App

lam, lambda :: Eq a => a -> Term a -> Term a
lambda v b = Abs $ abstract1 v b
lam = lambda

fixedPoint :: (a -> Maybe a) -> a -> a
fixedPoint f e = fromMaybe e $ fixedPoint f <$> f e

headReduction :: Term a -> Term a
headReduction e = fromMaybe e $ tryHeadReduction e

tryHeadReduction :: Term a -> Maybe (Term a)
tryHeadReduction Var{} = Nothing
tryHeadReduction (Abs e) = Abs . toScope <$> tryHeadReduction (fromScope e)
tryHeadReduction (App Var{} _) = Nothing
tryHeadReduction (App (Abs body) x) = Just $ instantiate1 x body
tryHeadReduction (App a b) = App <$> tryHeadReduction a <*> pure b

headNF :: Term a -> Term a
headNF = fixedPoint tryHeadReduction

leftReduction :: Term a -> Term a
leftReduction e0 = fromMaybe e0 $ tryLeftReduction e0

tryLeftReduction :: Term b -> Maybe (Term b)
tryLeftReduction Var{} = Nothing
tryLeftReduction (Abs e) = Abs . toScope <$> tryLeftReduction (fromScope e)
tryLeftReduction (App (Abs body) x) = Just $ instantiate1 x body
tryLeftReduction (App v@Var{} y)    = App v <$> tryLeftReduction y
tryLeftReduction (App a b) = App   <$> tryLeftReduction a <*> pure b
                         <|> App a <$> tryLeftReduction b

betaNF :: Term b -> Term b
betaNF = fixedPoint tryLeftReduction

catApps :: Term t -> [Term t]
catApps (App x0 y0) = toList $ go x0 `snoc` y0
  where
    go (App x y) = go x `snoc` y
    go e = singleton e
catApps e = [e]

yComb :: Term String
yComb = lam "y" $ lam "x" (Var "y" @: (Var "x" @: Var "x"))
               @: lam "x" (Var "y" @: (Var "x" @: Var "x"))

aComb :: Term String
aComb = lam "x" $ lam "y" $ Var "y" @: (Var "x" @: Var "x" @: Var "y")

turing :: Term String
turing = aComb @: aComb


prettyPrec :: Int -> Term String -> ShowS
prettyPrec d = run . flip runReader 'a' . prettyM d

pretty :: Term String -> String
pretty = ($ "") . prettyPrec 0

prettyM :: Member (Reader Char) r => Int -> Term String -> Eff r ShowS
prettyM _ (Var a) = return $ showString a
prettyM d l@(Abs _) = do
  (vars, body) <- flattenAbs l
  body' <- prettyM 0 body
  return $ showParen (d > 0) $
    showChar 'λ' . showString vars . showString ". " . body'
prettyM d (App a b) = do
  l <- prettyM 1 a
  r <- prettyM 2 b
  return $ showParen (d > 1) $ l . showChar ' ' . r

flattenAbs :: Member (Reader Char) r => Term String -> Eff r (String, Term String)
flattenAbs (Abs l) = do
  v <- ask
  (vars, body) <- local (succ :: Char -> Char) $ flattenAbs $ instantiate1 (Var [v]) l
  return $ (v: vars, body)
flattenAbs l = return ([], l)

lred :: PTerm a -> PTerm a
lred = PTerm . leftReduction . runPTerm

newtype PTerm a = PTerm { runPTerm :: Term a
                        } deriving (Read, Eq, Ord)

instance Show (PTerm String) where
  showsPrec d = showParen (d > 5) . prettyPrec 0 . runPTerm
