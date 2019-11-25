{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module NiceLanguage where

import Control.Monad.Var
import Data.Maybe
import Data.List hiding (group)
import Data.List.Key (group)
import Safe
import Control.Monad.Fail
import qualified Control.Monad.State.Lazy as S (get,put)
import Control.Monad.State.Lazy  hiding (get,put)

import Data.Char
import Data.IORef

getS::(Monad m) => StateT a m a
getS = S.get
putS::(Monad m) => a -> StateT a m ()
putS = S.put

--do binding with a function as parameter. Makes context sensitive binding easier
data Term a = TBOT | CONT a | APPL (Term a) (Term a) deriving (Show, Eq)
data VTerm v a = VBOT | VCONT (v a) | VAPPL (v (VTerm v a)) (v (VTerm v a))
deriving instance (Eq a, Eq (v a), Eq (v (VTerm v a))) => Eq (VTerm v a)

--the vvar has a list of the terms it is being used in
data VarTerm v a = UNAS | VVBOT | VVATOM (v a) | VVAR (PVarTerm v a) [PVarTerm v a] | VVAPPL (PVarTerm v a) (PVarTerm v a)
deriving instance (Eq a, Eq (v a), Eq (v (VarTerm v a))) => Eq (VarTerm v a)

type PVTerm v a = v (VTerm v a)
type PVarTerm v a = v (VarTerm v a)

{-
class (VarMonad m v) => Rewireable m v t where
  rewire::(v (t a) -> v (t a)) -> t a -> t a

instance (VarMonad m v) => Rewirable m v (VTerm v a) where
  rewire fkt (VAPPL x y) = VAPPL (fkt x) (fkt y)
  rewire fkt x = x
-}

rewireTo::(VarMonad m v) => PVarTerm v a -> [PVarTerm v a] -> PVarTerm v a -> m ()
--rewire ptrold ptrnew newrefs (VVAPPL x y) = VVAPPL (exchange ptrold ptrnew x) (exchange ptrold ptrnew y) --shouldn't be necessary. Variables should only point to other variables
rewireTo ptrnew newrefs pv = do {
  v <- get pv;
  case v of
    (VVAR ptr lst) -> put pv $ VVAR ptrnew (lst ++ newrefs)
    --other cases should not happen. Vars should only point to other vars
}

termVars::Term a -> [a]
termVars TBOT = []
termVars (CONT a) = [a]
termVars (APPL x y) = (termVars x) ++ (termVars y)

--needs terminal pointer so be set correctly already
termToVTerm::(VarMonad m v) => (a -> v a) -> Term a -> m (PVTerm v a)
termToVTerm _ TBOT = new $ VBOT
termToVTerm bound (CONT a) = new $ VCONT $ bound a
termToVTerm bound (APPL x y) = do {
  x' <- termToVTerm bound x;
  y' <- termToVTerm bound y;
  new $ VAPPL x' y';
}

{-
termToConstrVTerm::(VarMonad m v, Eq a) => Term a -> m (PVTerm v a, [[(PVTerm v a, PVTerm v a)]])
termToConstrVTerm term = do {
  (ptr, lst) <- termToConstrVTerm' term;
  --group them by equivalence class and formulate one line of equality
  return (ptr, filter (\x -> length x > 2) [zip cls (tail cls) | cls <- (map.map) snd $ group fst lst])
}
termToConstrVTerm'::(VarMonad m v,Eq a) => Term a -> m (PVTerm v a, [(a,PVTerm v a)])
termToConstrVTerm' TBOT = new VBOT >>= \x -> return (x, [])
termToConstrVTerm' (CONT a) = new (VCONT a) >>= \x -> return (x, [(a,x)]) --TODO: terminals don't have an address yet
termToConstrVTerm' (APPL x y) = do {
  (t1, l1) <- termToConstrVTerm' x;
  (t2, l2) <- termToConstrVTerm' y;
  ptr <- new (VAPPL t1 t2);
  return (ptr, l1 ++ l2)
}
-}

--get pointers that ensure equality of terminals
shallowEqPtrs::(VarMonad m v, Eq a) => Term a -> m [(a, v a)]
shallowEqPtrs t = (zip vars) <$> sequence (new <$> vars)
          where vars = nub $ termVars t

shalEqTermtoVTerm::(VarMonad m v, Eq a) => Term a -> m (PVTerm v a)
shalEqTermtoVTerm term = do {
  mp <- shallowEqPtrs term;
  termToVTerm (\x -> lookupJust x mp) term
}

shalEqVarPtrs::(VarMonad m v, Eq a) => (a -> Bool) -> Term a -> m [(a,PVarTerm v a)]
shalEqVarPtrs bound term = (zip vars) <$> sequence varms
  where vars = nub $ termVars term
        varms = (\x -> if bound x then new x >>= \v -> new $ VVATOM v else do{
                          udf <- new UNAS;
                          var <- new $ VVAR udf [];
                          put var $ VVAR udf [var]; --make sure it points to itself for rewireing
                          return var;
                        }) <$> vars

termToVarTerm::(VarMonad m v, Eq a) => (a -> Bool) -> Term a -> m (PVarTerm v a)
termToVarTerm bound term = do {
  pts <- shalEqVarPtrs bound term;
  termToVarTerm' (\x -> lookupJust x pts) term
}

termToVarTerm'::(VarMonad m v, Eq a) => (a -> PVarTerm v a) -> Term a -> m (PVarTerm v a)
termToVarTerm' bound TBOT = new VVBOT
termToVarTerm' bound (CONT a) = return $ bound a
termToVarTerm' bound (APPL x y) = do {
  x' <- termToVarTerm' bound x;
  y' <- termToVarTerm' bound y;
  new $ VVAPPL x' y'
}

--------------------------------------------------
--some output
--------------------------------------------------

type VarT a m v = StateT [a] m v

nextVar::(Monad m) => VarT a m a
nextVar = do {
  s <- getS;
  case s of
    (x:xs) -> do {
      putS xs;
      return x
    }
    x -> error "no more variables to take from!" --weirdly needs to be here...
}

varTermToTerm::(VarMonad m v) => [a] -> VarTerm v a -> m (Term a)
varTermToTerm vars term = evalStateT (varTermToTerm' term) vars

varTermToTerm'::(VarMonad m v) => VarTerm v a -> StateT [a] m (Term a)
varTermToTerm' UNAS = CONT <$> nextVar
varTermToTerm' VVBOT = return TBOT
varTermToTerm' (VVATOM p) = lift $ CONT <$> get p
varTermToTerm' v@(VVAR p lst) = do {
  cont <- lift $ get p;
  case cont of
    UNAS -> do {
      var <- nextVar;
      ptr <- lift $ new var;
      lift $ sequence $ (\x -> put x $ VVATOM ptr) <$> lst;
      varTermToTerm' (VVATOM ptr);
    }
    x -> varTermToTerm' x
}
varTermToTerm' (VVAPPL p1 p2) = do {
  x <- lift $ get p1;
  y <- lift $ get p2;
  x' <- varTermToTerm' x;
  y' <- varTermToTerm' y;
  return $ APPL x' y'
}

testVars = (\x -> [x]) <$> ['A'..]

test1::IO (Term String)
test1 = (tp >>= get >>= varTermToTerm testVars)
  where t = APPL (APPL (CONT "x") (CONT "Y")) ((CONT "x"))
        tp = (termToVarTerm (isLower.head) t)::IO (IORef (VarTerm IORef String))

test2::IO (Term String)
test2 = do{
  c <- (new "x")::IO (IORef String);
  t1 <- new (VVATOM c);
  varTermToTerm testVars $ VVAPPL t1 t1
}

ioifyPVarTerm::IO (IORef (VarTerm IORef String)) -> IO (IORef (VarTerm IORef String))
ioifyPVarTerm x = x

--------------------------------------------------
--term matching
--------------------------------------------------
--TODO: check whether merge is possible first
--for now, just produces a new term for safety
mergePointers'::(VarMonad m v, Eq (v a), Eq a) => PVarTerm v a -> PVarTerm v a -> m (Maybe (PVarTerm v a))
mergePointers' p1 p2 = do{
  (t1,t2) <- getCts2 (p1,p2);
  case (t1,t2) of
    (VVBOT, VVBOT) -> Just <$> (new VVBOT)
    (VVATOM a, VVATOM b)
        | a == b -> Just <$> (new $ VVATOM a)
        | otherwise ->  return Nothing
    (VVAR a lst1, VVAR b lst2) -> do {
            mab_merg <- mergePointers' a b;
            case mab_merg of
              Just merg -> do {
                nv <- new (VVAR merg []);
                put nv (VVAR merg (lst1++[nv]++lst2));
                --rewire both variables to a common target, merging the reference lists
                sequence $ rewireTo a (nv:lst1) <$> lst2;
                sequence $ rewireTo a (nv:lst2) <$> lst1;
                return $ Just nv;
              }
              Nothing -> return Nothing;
        }
    (VVAR a lst, term) -> mergePointers' a p2   --TODO: Problem: already writes things into the variables, even if merge fails
    (term, VVAR a lst) -> mergePointers' p1 a
    (VVAPPL x y, VVAPPL x' y') -> do {
          px <- mergePointers' x x';
          py <- mergePointers' y y';
          case do {rx <- px; ry <- py; return $ VVAPPL rx ry} of
            Just apl -> Just <$> new apl
            Nothing -> return Nothing
        }
    (UNAS, UNAS) -> Just <$> new UNAS;
    (UNAS, t ) -> return $ Just p2; --WARNING! not sure if that gives the right behaviour
    (t , UNAS) -> return $ Just p1;
    (x,y) -> return Nothing
}


-------------------------------------------------------
--util
-------------------------------------------------------

getCts::(VarMonad m v) => [v a] -> m [a]
getCts pts = sequence $ get <$> pts

getCts2::(VarMonad m v) => (v a, v b) -> m (a, b)
getCts2 (p1, p2) = do { x1 <- get p1; x2 <- get p2; return (x1,x2) }
getCts3::(VarMonad m v) => (v a, v b, v c) -> m (a, b, c)
getCts3 (p1, p2, p3) = do { x1 <- get p1; x2 <- get p2; x3 <- get p3; return (x1,x2, x3) }


exchange::(Eq a) => a -> a -> a -> a
exchange match ex y
  | match==y = ex
  | otherwise = y
