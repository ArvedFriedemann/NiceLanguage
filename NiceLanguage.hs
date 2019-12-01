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
import Control.Monad.Trans.Writer.Lazy
import Debug.Trace

import Data.Char
import Data.Maybe
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
data VarTerm v a = UNAS | VVBOT | VVATOM (v a)| VVAR (PVarTerm v a) [PVarTerm v a] | VVAPPL (PVarTerm v a) (PVarTerm v a)
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

getVarCnts::(VarMonad m v) => PVarTerm v a -> m (PVarTerm v a)
getVarCnts var = do {
  (VVAR a lst) <- get var;
  return a
}

newVar::(VarMonad m v) => PVarTerm v a -> m (PVarTerm v a)
newVar con = do {
  var <- new $ VVAR con [];
  put var (VVAR con [var]);
  return var
}

termVars::Term a -> [a]
termVars TBOT = []
termVars (CONT a) = [a]
termVars (APPL x y) = (termVars x) ++ (termVars y)


pVarTermVars::(VarMonad m v) => PVarTerm v a -> m [PVarTerm v a]
pVarTermVars ptr = execWriterT $ pVarTermVars' ptr

pVarTermVars'::(VarMonad m v) => PVarTerm v a -> WriterT [PVarTerm v a] m ()
pVarTermVars' ptr = do {t <- lift $ get ptr;
  case t of
    (VVAR _ _) -> tell [ptr] >> return ();
    (VVAPPL x y) -> (pVarTermVars' x) >> (pVarTermVars' y)
    x -> return ();
}

--variable equivalency class to assignment
pVarTermVarAsm::(VarMonad m v) => PVarTerm v a -> m [([PVarTerm v a], PVarTerm v a)]
pVarTermVarAsm ptr = execWriterT $ pVarTermVarAsm' ptr

pVarTermVarAsm'::(VarMonad m v) => PVarTerm v a -> WriterT [([PVarTerm v a], PVarTerm v a)] m ()
pVarTermVarAsm' ptr = do {t <- lift $ get ptr;
  case t of
    (VVAR a lst) -> tell [(lst, a)] >> return ();
    (VVAPPL x y) -> (pVarTermVarAsm' x) >> (pVarTermVarAsm' y)
    x -> return ();
}


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
        varms = (\x -> if bound x then new x >>= \v -> new (VVATOM v) else do{
                          udf <- new UNAS;
                          var <- newVar udf;
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

zipVars::(Monad m) => [b] -> VarT a m [(b,a)]
zipVars [] = return []
zipVars (x:xs) = do {v <- nextVar; vs <- zipVars xs; return $ (x,v):vs}

pVarTermToShallowAssignments::(VarMonad m v, Eq (PVarTerm v a)) => [a] -> PVarTerm v a -> m (Term a, [([a], Term a)])
pVarTermToShallowAssignments vars ptr = evalStateT (pVarTermToShallowAssignments' ptr) vars

pVarTermToShallowAssignments'::(VarMonad m v, Eq (PVarTerm v a)) => PVarTerm v a -> VarT a m (Term a, [([a], Term a)])
pVarTermToShallowAssignments' ptr = do {
  asm <- pVarTermToAssignments ptr;
  varCnts <- lift $ pVarTermVarAsm ptr;
  namesToTerms <- return $ (\(vs, t) -> (catMaybes $ (\x -> lookup x asm) <$> (nub vs), pVarTermToShallowTerm asm t)) <$> varCnts;
  lst <- (zip (fst <$> namesToTerms)) <$> (sequence $ (map snd namesToTerms));
  orig <- pVarTermToShallowTerm asm ptr;
  return (orig, lst);
}

pVarTermToShallowTerm::(VarMonad m v, Eq (PVarTerm v a)) => [(PVarTerm v a, a)] -> PVarTerm v a -> VarT a m (Term a)
pVarTermToShallowTerm asm ptr = do {
  t <- lift $ get ptr;
  case t of
    UNAS -> CONT <$> nextVar
    VVBOT -> return TBOT
    (VVATOM x) -> CONT <$> lift (get x)
    (VVAR _ _) -> return $ CONT (lookupJust ptr asm) --TODO: This does not evaluate the variable (but would be necessary once)
    (VVAPPL x y) -> do {
      x' <- pVarTermToShallowTerm asm x;
      y' <- pVarTermToShallowTerm asm y;
      return $ APPL x' y'
    }
}

pVarTermToAssignments::(VarMonad m v) => PVarTerm v a -> VarT a m [(PVarTerm v a, a)]
pVarTermToAssignments ptr = do {
  termVars <- lift $ pVarTermVars ptr;
  zipVars termVars
}

pVarTermToTerm::(VarMonad m v) => [a] -> PVarTerm v a -> m (Term a)
pVarTermToTerm vars term = get term >>= varTermToTerm vars
varTermToTerm::(VarMonad m v) => [a] -> VarTerm v a -> m (Term a)
varTermToTerm vars term = evalStateT (varTermToTerm' term) vars

varTermToTerm'::(VarMonad m v) => VarTerm v a -> StateT [a] m (Term a)
varTermToTerm' UNAS = CONT <$> nextVar
varTermToTerm' VVBOT = return TBOT
varTermToTerm' (VVATOM p) = lift $ (CONT <$> get p)
varTermToTerm' v@(VVAR p lst) = do {
  cont <- lift $ get p;
  case cont of
    UNAS -> do {
      var <- nextVar;
      ptr <- lift $ new var;
      lift $ put p (VVATOM ptr);
      (lift $ get p) >>= varTermToTerm';
    }
    x -> varTermToTerm' x
}
varTermToTerm' (VVAPPL p1 p2) = do {
  x <- lift $ get p1;
  x' <- varTermToTerm' x;
  y <- lift $ get p2;
  y' <- varTermToTerm' y;
  return $ APPL x' y'
}

ioifyPVarTerm::IO (IORef (VarTerm IORef String)) -> IO (IORef (VarTerm IORef String))
ioifyPVarTerm x = x

--------------------------------------------------
--term matching
--------------------------------------------------
--TODO: check whether merge is possible first
mergePointers::(VarMonad m v, Eq (PVarTerm v a), Eq (v a), Eq a) => PVarTerm v a -> PVarTerm v a -> m (Maybe (PVarTerm v a))
mergePointers p1 p2 = mergePointers' p1 p1 p2

mergePointers'::(VarMonad m v, Eq (PVarTerm v a), Eq (v a), Eq a) => PVarTerm v a -> PVarTerm v a -> PVarTerm v a -> m (Maybe (PVarTerm v a))
--throughout this algorithm, both terms are made equal (so they actually change). The first term is assumed to be
--the main one and returned as the merged term.
mergePointers' mainptr p1 p2 = if p1==p2 then return $ Just p1 else do{
  (t1,t2) <- get2 p1 p2;
  case (t1,t2) of
    (VVBOT, VVBOT) -> return $ Just mainptr
    (VVATOM a, VVATOM b)
        | a == b -> return $ Just mainptr
        | otherwise ->  return Nothing
    (VVAR a lst1, VVAR b lst2) -> do {
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
    (term, VVAR a lst) -> mergePointers' p2 p2 p1 --needs to be this mergePointers to avoid recursion lock
    (VVAR a lst, term) -> do {
      mptr <- mergePointers' a a p2;
      case mptr of
        Just ptr -> do {
          put a =<< get ptr;
          return $ Just p1; --again, variable needs to be returned for changes to come into effect!
        }
        Nothing -> return Nothing
    }
    (VVAPPL x y, VVAPPL x' y') -> do {
          px <- mergePointers' x x x';
          py <- mergePointers' y y y';
          case do {rx <- px; ry <- py; return $ VVAPPL rx ry} of
            --Just apl -> Just <$> new apl --would create a new term. WARNING! Recursion lock might not work here
            Just apl -> do {put p1 $ apl; put p2 $ apl; return $ Just p1}
            Nothing -> return Nothing
        }
    (UNAS, UNAS) -> return $ Just mainptr;--WARNING! --Just <$> newPVT UNAS True;
    (UNAS, t ) -> return $ Just p2; --WARNING! not sure if that gives the right behaviour
    (t , UNAS) -> return $ Just p1;
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
