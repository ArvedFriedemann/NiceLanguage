module NLParser where

import NiceLanguage
import Text.Parsec hiding (spaces)
import Data.Char
import Control.Monad.Trans.Writer.Lazy
import Control.Monad.Var
import Data.IORef

forbiddenSymb = "() \t\n`"
spaceChars = " \t"

idfr::Parsec String st String
idfr = many1 (noneOf forbiddenSymb)

idfr0::Parsec String st String
idfr0 = many (noneOf forbiddenSymb)

baseTerm::Parsec String st (Term String)
baseTerm = (try $ string "()" >> return TBOT) <|> (try $ parens term) <|> (CONT <$> idfr)

term::Parsec String st (Term String)
term = (spaces >> sepEndBy1 baseTerm spaces1) >>= \x -> return $ foldl1 APPL x

parens::Parsec String st a -> Parsec String st a
parens p = do {string "("; r <- p; string ")"; return r}

spaces::Parsec String st String
spaces = many (oneOf spaceChars)

spaces1::Parsec String st String
spaces1 = many1 (oneOf spaceChars)

encap::Parsec String st b -> Parsec String st a -> Parsec String st a
encap e p = do {e; r <- p; e; return r}


safeParse::Parsec [a] () b -> [a] -> b
safeParse p ipt = case parse p "" ipt of
                    Right v -> v
                    Left err -> error (show err)

termFromString::String -> Term String
termFromString = safeParse term
rt::String -> Term String
rt = termFromString

wt::Term String -> String
wt = termToString
termToString::Term String -> String
termToString t = execWriter $ termToString' t
termToString'::Term String -> Writer String ()
termToString' TBOT = tell "()"
termToString' (CONT a) = tell a
termToString' (APPL x b@(APPL y z)) = do {
  termToString' x;
  tell " (";
  termToString' b;
  tell ")";
}
termToString' (APPL x y) = do {
  termToString' x;
  tell " ";
  termToString' y;
}

showPVarTerm::(VarMonad m v) => PVarTerm v String -> m String
showPVarTerm ptr = wt <$> pVarTermToTerm stdVars ptr

stdBound::String -> Bool
stdBound (x:xs) = not $ (x=='_') || isUpper x

stdVars::[String]
stdVars = aToZ ++ (concat $ zipWith (\i s -> map (\k -> k++(show i)) s) [0..] (repeat aToZ))
  where aToZ = (\x -> [x]) <$> ['A'..'Z']


stdUnify::String -> String -> IO ()
stdUnify s1 s2 = do {
  (VVAPPL pt1 pt2 seen) <- get =<< (ioifyPVarTerm $ termToVarTerm stdBound (APPL (rt s1) (rt s2)) );
  mptm <- mergePointers pt1 pt2;
  case mptm of
    Just ptm -> putStrLn =<< showPVarTerm ptm
    Nothing -> putStrLn "No match."
}

--(showPVarTerm =<< (ioifyPVarTerm $ termToVarTerm stdBound $ rt "add X"))
