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

--BIG TODO: universal queue for new constraints (or old reactivated ones)
--Maybe equality always needs to be conditional?
evalEqConstr::(VarMonad m v, Eq (PVarTerm v a)) => PVarTerm v a -> m ()
evalEqConstr constr = do {
  lst <- lAssocListMatch constr
  case lst of
    [pt1,pt2,respt, con1, con2, prev1, prev2] -> do { --two additional constraints. Also: TODO: previous state missing (would be the previous var pointers. Problem: the list of references should be updated, but now equalities could have been forged)
      res <- getVarCnts respt;
      case res of
        VVBOT -> --make sure the variables are separated again
        x -> --check if things are still equal
      [t1,t2] <- sequence $ getVarCnts <$> [pt1, pt2];
      case (t1, t2) of
        (VVBOT, VVBOT) -> updateVar res VVTOP --TODO! TOP needed!
        (VVTOP, VVTOP) -> updateVar res VVTOP --TODO! TOP needed!
        (ATOM a, ATOM b) | a==b -> updateVar res VVTOP
                         | otherwise -> updateVar res VVBOT
        (VVAR a lst1, VVAR b lst2) -> --TODO: The pointers need to be dynamically updated with the result of the equality!
        (VVAR a lst, t) -> evalEqConstr a pt2 --swap
        (t, VVAR a lst) -> evalEqConstr pt1 a --WARNING! For update, make sure variable indirection removed
        (VVAPPL x x', VVAPPL y y') -> do { --TODO: make sure not to copy the constraint! Maybe follow up constraints?
          [c1,c2] <- sequence $ getVarCnts <$> [con1, con2];
          case (c1,c2) of
            (UNAS, UNAS) -> --make new constraints. Give same result var.
            (eq1, eq2) -> --put them back onto the stack for reevaluation (if necesary)
        }
        (UNAS, UNAS) -> --no further ado. Constraint should be woken up by its parents
        (UNAS, t) -> --new term?
        (t, UNAS) ->
        x -> updateVar res VVBOT
    }
    x -> error "not an equality constraint!"
}

updateVar::(VarMonad m v) => PVarTerm v a -> VarTerm v a -> m ()
updateVar variable value = undefined
