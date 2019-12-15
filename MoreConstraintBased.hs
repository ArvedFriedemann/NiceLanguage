{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module MoreConstraintBased where

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


data TermConst = TOP | BOT | UNAS deriving (Show, Eq)
--this time, variables don't store their equivalence class, but a more general list of terms that need updating
data VarTerm v a =    CONST TermConst
                    | ATOM (v a)
                    | VAR (PVarTerm v a) [PVarTerm v a] --only here universal list to make type construction terminate!
                    | APPL (PVarTerm v a) (PVarTerm v a)
                    | EQ  (PVarTerm v a) (PVarTerm v a) (PVarTerm v a)
--The EQ constructor could be done as a term compound, but that makes things cumbersome. It stores the terms it connects and a variable pointing towards whether the equality holds or not.
deriving instance (Eq a, Eq (v a), Eq (v (VarTerm v a))) => Eq (VarTerm v a)

--NOTE: It is probably easier to have variables as the only reassignable thing. It is harder at some points, sure, but the main problem is the infinite type constructed by everything having a pointer to possibly everything. Allowing for infinite types could potentially introduce more errors. With the term type, the type eventually stops!
--type ConstrCTX v a = (a, [v (ConstrCTX v a)])
--type VarCTX v a = ConstrCTX v (VarTerm v a)
--type PVarCTX v a = v (VarCTX v a)
type PVarTerm v a = v (VarTerm v a)


placeEqConstr::(VarMonad m v) => PVarPCTX v a -> PVarPCTX v a -> m ()
placeEqConstr p1 p2 = do {
  [(t1, ctx1),(t2, ctx2)] <- getCts [p1,p2];
  constr <- return $ EQ p1 p2;
  if constr `elem` (ctx1++ctx2)
    then
    else return ()
}

nubEq::(VarMonad m v, Eq (PVarPCTX v a)) => PVarPCTX v a -> PVarPCTX v a -> [PVarPCTX v a] -> m (PVarPCTX v a)
nubEq p1 p2 [] = do {
  res <- new (UNAS, []);
  var <- new (VAR res, []);
  eq <- new (EQ p1 p2 var, []);
  pushCtx p1 eq;
  pushCtx p2 eq;
  return eq
}
nubEq p1 p2

((EQ p1' p2' resp):xs)
  | (p1==p1' && p2==p2') ||

pushCtx::(VarMonad m v) => PVarPCTX v a -> PVarPCTX v a -> m ()
pushCtx p ctx = do {
  (t, ctxlst) <- get p;
  put p (t, ctx:ctxlst)
}

getCts::(VarMonad m v) => [v a] -> m [a]
getCts pts = sequence $ get <$> pts
