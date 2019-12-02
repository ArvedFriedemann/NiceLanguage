module ConstraintBased where

import NiceLanguage

--constraint X=Y with Z if it holds and a pointer that can remove it
--maybe pointer of if it needs to hold? Or remove it from the update queue? Would deactivate (kill?) them on update
--constraints come from an assignment. is it removed, so is the constraint?
--notify variables upon write. They have their equalities and constraints stored

lAssocListMatch::(VarMonad m v) => PVarTerm v a -> m [PVarTerm v a]
lAssocListMatch = execWriterT.lAssocListMatch'

lAssocListMatch'::(VarMonad m v) => PVarTerm v a -> WriterT [PVarTerm v a] m ()
lAssocListMatch' ptr = do {
  ttop <- lift $ get ptr;
  case ttop of
    (VVAPPL pt1 pt2) -> do {
      lAssocListMatch' pt1;
      tell [pt2]
    }
    x -> return ()
}

newlAssocList::(VarMonad m v) => [PVarTerm v a] -> m (PVarTerm v a)
newlAssocList lst = newlAssocList $ reverse lst
newlAssocListRev::(VarMonad m v) => [PVarTerm v a] -> m (PVarTerm v a)
newlAssocListRev [] = new VVBOT
newlAssocListRev (x:xs) = do {
  lst <- newlAssocList xs;
  new $ VVAPPL lst x;
}


{-
General idea:
memory changes trigger updates
when executing program, function trace preserved
every operation has a reverse for backtracking or is operated on separate memory.
-}

--TODO: equality constraints constantly doubled for DAGs. existence only checked from root constraint down, never the other way around
--BIG TODO: universal queue for new constraints (or old reactivated ones)
--Maybe equality always needs to be conditional?
evalEqConstr::(VarMonad m v, Eq (PVarTerm v a)) => PVarTerm v a -> m ()
evalEqConstr constr = do {
  lst <- lAssocListMatch constr
  case lst of
    [pt1,pt2,respt, con1, con2, prev1, prev2] -> do { --two additional constraints. Also: TODO: previous state missing (would be the previous var pointers. Problem: the list of references should be updated, but now equalities could have been forged)
      [res,t1,t2] <- sequence $ getVarCnts <$> [rept,pt1, pt2];
      case res of
        VVBOT -> do { --make sure the variables are separated again
        case (t1,t2) of
          (VVBOT,VVBOT) -> updateVar res VVTOP
          (VVTOP,VVTOP) -> updateVar res VVTOP
          (VVATOM a, VVATOM b)
            | a==b -> updateVar res VVTOP
            | otherwise -> return ()
          (VVAR a lst, VVAR b lst) --clean up! Move the pointers back! make sure the subterms stay different!
          (VVAR a lst, t) -> --move
          (t, VVAR b lst) -> --I said, move!
          (VVAPPL x x', VVAPPL y y') -> --as well, potentially create new equiv constraints
          (UNAS,UNAS) -> return () --can't do anything here
          (t,UNAS) -> return ()
          (UNAS,t) -> return ()
          x -> return ()
        }
        VVTOP ->  do{ --check if things are equal
          case (t1,t2) of
            (VVBOT,VVBOT) -> return ()
            (VVTOP,VVTOP) -> return ()
            (VVATOM a, VVATOM b)
              | a==b -> return ()
              | otherwise -> updateVar res VVBOT
            (VVAR a lst, VVAR b lst)
              | a==b -> return ()
              | otherwise -> --potentially create new equiv constraint
            (VVAR a lst, t) -> --move
            (t, VVAR b lst) -> --I said, move!
            (VVAPPL x x', VVAPPL y y') -> --as well, potentially create new equiv constraints
            (UNAS,UNAS) -> return () --can't do anything here
            (t,UNAS) -> --assign!
            (UNAS,t) -> --assign!
            x -> updateVar res VVBOT
        }
        UNAS -> do{ --only assign result, not variables!
          case (t1,t2) of
            (VVBOT,VVBOT) -> updateVar res VVTOP
            (VVTOP,VVTOP) -> updateVar res VVTOP
            (VVATOM a, VVATOM b)
              | a==b -> updateVar res VVTOP
              | otherwise -> updateVar res VVBOT
            (VVAR a lst, VVAR b lst)
              | a==b -> updateVar res VVTOP
              | otherwise -> --potentially create new UNASSIGNED equiv constraint
            (VVAR a lst, t) -> --move
            (t, VVAR b lst) -> --I said, move!
            (VVAPPL x x', VVAPPL y y') -> --as well, potentially create new UNASSIGNED equiv constraints
            (UNAS,UNAS) -> return () --can't do anything here
            (t,UNAS) -> return ()
            (UNAS,t) -> return ()
            x -> updateVar res VVBOT
        }


    }
    x -> error "not an equality constraint!"
}

updateVar::(VarMonad m v) => PVarTerm v a -> VarTerm v a -> m ()
updateVar variable value = undefined
