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
import Debug.Trace

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
data VarTerm v a = UNAS (v Bool) | VVBOT (v Bool) | VVATOM (v a) (v Bool) | VVAR (PVarTerm v a) [PVarTerm v a] (v Bool) | VVAPPL (PVarTerm v a) (PVarTerm v a) (v Bool)
deriving instance (Eq a, Eq (v a), Eq (v Bool), Eq (v (VarTerm v a))) => Eq (VarTerm v a)

type PVTerm v a = v (VTerm v a)
type PVarTerm v a = v (VarTerm v a)

{-
class (VarMonad m v) => Rewireable m v t where
  rewire::(v (t a) -> v (t a)) -> t a -> t a

instance (VarMonad m v) => Rewirable m v (VTerm v a) where
  rewire fkt (VAPPL x y) = VAPPL (fkt x) (fkt y)
  rewire fkt x = x
-}

getSeenPtr::VarTerm v a -> (v Bool)
getSeenPtr (UNAS p) = p
getSeenPtr (VVBOT p) = p
getSeenPtr (VVATOM _ p) = p
getSeenPtr (VVAR _ _ p) = p
getSeenPtr (VVAPPL _ _ p) = p

newPVT::(VarMonad m v) => (v Bool -> VarTerm v a) -> Bool -> m (PVarTerm v a)
newPVT fkt b = new b >>= \x -> new (fkt x)

newUPVT::(VarMonad m v) => (v Bool -> VarTerm v a) -> m (PVarTerm v a)
newUPVT fkt = newPVT fkt False

putPVT::(VarMonad m v) => PVarTerm v a -> (v Bool -> VarTerm v a) -> m ()
putPVT ptr fkt = do {
  term <- get ptr;
  put ptr (fkt $ getSeenPtr term)
}

putPVTF::(VarMonad m v) => PVarTerm v a -> (v Bool -> VarTerm v a) -> m ()
putPVTF ptr fkt = do {
  term <- get ptr;
  put (getSeenPtr term) False;
  put ptr (fkt $ getSeenPtr term)
}

rewireTo::(VarMonad m v) => PVarTerm v a -> [PVarTerm v a] -> PVarTerm v a -> m ()
--rewire ptrold ptrnew newrefs (VVAPPL x y) = VVAPPL (exchange ptrold ptrnew x) (exchange ptrold ptrnew y) --shouldn't be necessary. Variables should only point to other variables
rewireTo ptrnew newrefs pv = do {
  v <- get pv;
  case v of
    (VVAR ptr lst seen) -> put pv $ VVAR ptrnew (lst ++ newrefs) seen
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
        varms = (\x -> if bound x then new x >>= \v -> newUPVT (VVATOM v) else do{
                          udf <- newUPVT UNAS;
                          var <- newUPVT $ VVAR udf [];
                          putPVT var $ VVAR udf [var]; --make sure it points to itself for rewireing
                          return var;
                        }) <$> vars

termToVarTerm::(VarMonad m v, Eq a) => (a -> Bool) -> Term a -> m (PVarTerm v a)
termToVarTerm bound term = do {
  pts <- shalEqVarPtrs bound term;
  termToVarTerm' (\x -> lookupJust x pts) term
}

termToVarTerm'::(VarMonad m v, Eq a) => (a -> PVarTerm v a) -> Term a -> m (PVarTerm v a)
termToVarTerm' bound TBOT = newUPVT VVBOT
termToVarTerm' bound (CONT a) = return $ bound a
termToVarTerm' bound (APPL x y) = do {
  x' <- termToVarTerm' bound x;
  y' <- termToVarTerm' bound y;
  newUPVT $ VVAPPL x' y'
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

pVarTermToTerm::(VarMonad m v) => [a] -> PVarTerm v a -> m (Term a)
pVarTermToTerm vars term = get term >>= varTermToTerm vars
varTermToTerm::(VarMonad m v) => [a] -> VarTerm v a -> m (Term a)
varTermToTerm vars term = evalStateT (varTermToTerm' term) vars

varTermToTerm'::(VarMonad m v) => VarTerm v a -> StateT [a] m (Term a)
varTermToTerm' (UNAS _) = CONT <$> nextVar
varTermToTerm' (VVBOT _) = return TBOT
varTermToTerm' (VVATOM p _) = lift $ (CONT <$> get p)
varTermToTerm' v@(VVAR p lst _) = do {
  cont <- lift $ get p;
  case cont of
    (UNAS _) -> do {
      var <- nextVar;
      ptr <- lift $ new var;
      lift $ putPVTF p (VVATOM ptr);
      (lift $ get p) >>= varTermToTerm';
    }
    x -> varTermToTerm' x
}
varTermToTerm' (VVAPPL p1 p2 _) = do {
  x <- lift $ get p1;
  x' <- varTermToTerm' x;
  y <- lift $ get p2;
  y' <- varTermToTerm' y;
  return $ APPL x' y'
}

testVars = (\x -> [x]) <$> ['A'..]
testBound = (isLower.head)

test1::IO (Term String)
test1 = (tp >>= get >>= varTermToTerm testVars)
  where t = APPL (APPL (CONT "x") (CONT "Y")) ((CONT "x"))
        tp = (termToVarTerm testBound t)::IO (IORef (VarTerm IORef String))

test2::IO (Term String)
test2 = do{
  c <- (new "x")::IO (IORef String);
  t1 <- newUPVT (VVATOM c);
  p <- new False;
  varTermToTerm testVars (VVAPPL t1 t1 p)
}

test3::IO [Term String]
test3 = do {
  t <- ioifyPVarTerm $ termToVarTerm testBound (APPL t1 t2);
  (VVAPPL pt1 pt2 _) <- get t;
  merg <- mergePointers pt1 pt2;
  (case merg of
        Just melt -> do {
          (mptr, pt1', pt2') <- get3 melt pt1 pt2;
          --tp1 <- varTermToTerm testVars pt1';
          --tp2 <- varTermToTerm (drop 5 testVars) pt2';
          tres <- varTermToTerm (drop 10 testVars) mptr;
          --TODO: Problem. During the merging, the variable equivalences are changed in the original terms.
          --therefore they are interconnected afterwards
          --TODO!!!!!!
          return [{-tp1, tp2, -}tres]
        }
        Nothing -> return [])
}
  where t1 = APPL (CONT "x") (CONT"Y")--t1 = APPL (APPL (CONT "x") (CONT "Y")) ((CONT "x"))
        t2 = APPL (CONT "Z") (CONT"Z")--t2 = APPL (APPL (CONT "Y") (CONT "Y")) ((CONT "x"))

test4::IO [Term String]
test4 = do {
  t <- ioifyPVarTerm $ termToVarTerm testBound (APPL t1 t2);
  (VVAPPL pt1 pt2 _) <- get t;
  merg <- mergePointers pt1 pt2;
  (case merg of
        Just melt -> do {
          (mptr, pt1', pt2') <- get3 melt pt1 pt2;
          --tp1 <- varTermToTerm testVars pt1';
          --tp2 <- varTermToTerm (drop 5 testVars) pt2';
          tres <- varTermToTerm (drop 10 testVars) mptr;
          --TODO: Problem. During the merging, the variable equivalences are changed in the original terms.
          --therefore they are interconnected afterwards
          return [{-tp1, tp2, -}tres]
        }
        Nothing -> return [])
}
  where t1 = APPL (APPL (CONT "x") (CONT "Y")) ((CONT "x"))
        t2 = APPL (APPL (CONT "Z") (CONT "Z")) ((CONT "x"))


ioifyPVarTerm::IO (IORef (VarTerm IORef String)) -> IO (IORef (VarTerm IORef String))
ioifyPVarTerm x = x

--------------------------------------------------
--term matching
--------------------------------------------------
--TODO: check whether merge is possible first
mergePointers::(VarMonad m v, Eq (PVarTerm v a), Eq (v a), Eq a) => PVarTerm v a -> PVarTerm v a -> m (Maybe (PVarTerm v a))
mergePointers p1 p2 = mergePointers' p1 p1 p2
mergePointers'::(VarMonad m v, Eq (PVarTerm v a), Eq (v a), Eq a) => PVarTerm v a -> PVarTerm v a -> PVarTerm v a -> m (Maybe (PVarTerm v a))
mergePointers' mainptr p1 p2 = do {
  t1 <- get p1;
  t2 <- get p2;
  b1 <- get $ getSeenPtr t1;
  b2 <- get $ getSeenPtr t2;
  put (getSeenPtr t1) True;
  put (getSeenPtr t2) True;
  if b1 && b2 then return $ Just p1 else mergePointers'' mainptr p1 p2
}
mergePointers''::(VarMonad m v, Eq (PVarTerm v a), Eq (v a), Eq a) => PVarTerm v a -> PVarTerm v a -> PVarTerm v a -> m (Maybe (PVarTerm v a))
--throughout this algorithm, both terms are made euqal (so they actually change). The first term is assumed to be
--the main one and returned as the merged term.
mergePointers'' mainptr p1 p2 = if p1==p2 then return $ Just p1 else do{
  (t1,t2) <- get2 p1 p2;
  case (t1,t2) of
    (VVBOT _, VVBOT _) -> return $ Just mainptr
    (VVATOM a _, VVATOM b _)
        | a == b -> return $ Just mainptr
        | otherwise ->  return Nothing
    (VVAR a lst1 _, VVAR b lst2 _) -> do {
            mab_merg <- mergePointers' a a b;
            case mab_merg of
              Just merg -> do {
                --rewire both variables to a common target, merging the reference lists
                sequence $ rewireTo merg (lst1) <$> lst2;
                sequence $ rewireTo merg (lst2) <$> lst1;
                return $ Just mainptr; --necessary. Otherwise, if a variable gets rewired later, terms don't notice.
              }
              Nothing -> return Nothing;
        }
    (term, VVAR a lst _) -> mergePointers'' p2 p2 p1 --needs to be mergePointers' to avoid recursion lock
    (VVAR a lst _, term) -> do {
      mptr <- mergePointers' a a p2;
      case mptr of
        Just ptr -> do {
          put a =<< get ptr;
          return $ Just p1; --again, variable needs to be returned for changes to come into effect!
        }
        Nothing -> return Nothing
    }
    (VVAPPL x y _, VVAPPL x' y' _) -> do {
          px <- mergePointers' x x x';
          py <- mergePointers' y y y';
          case do {rx <- px; ry <- py; return $ VVAPPL rx ry} of
            --Just apl -> Just <$> newPVT apl True --would create a new term. WARNING! Recursion lock might not work here
            Just apl -> do {putPVT p1 $ apl; putPVT p2 $ apl; return $ Just p1}
            Nothing -> return Nothing
        }
    (UNAS _, UNAS _) -> return $ Just mainptr;--WARNING! --Just <$> newPVT UNAS True;
    (UNAS _, t ) -> return $ Just p2; --WARNING! not sure if that gives the right behaviour
    (t , UNAS _) -> return $ Just p1;
    (x,y) -> return Nothing
}


-------------------------------------------------------
--util
-------------------------------------------------------

getCts::(VarMonad m v) => [v a] -> m [a]
getCts pts = sequence $ get <$> pts

get2::(VarMonad m v) => v a -> v b -> m (a, b)
get2 p1 p2 = do { x1 <- get p1; x2 <- get p2; return (x1,x2) }
get3::(VarMonad m v) => v a -> v b -> v c -> m (a, b, c)
get3 p1 p2 p3 = do { x1 <- get p1; x2 <- get p2; x3 <- get p3; return (x1,x2, x3) }


exchange::(Eq a) => a -> a -> a -> a
exchange match ex y
  | match==y = ex
  | otherwise = y
