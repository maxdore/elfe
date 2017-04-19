module Language where

import Data.List
import Debug.Trace

data Term = Cons String [Term]
           | Var String
  deriving (Eq)
instance Show Term where
  show (Var s) = "" ++ s
  show (Cons s terms) = s ++ "(" ++ (intercalate "," $ map show terms) ++ ")" 

data Formula = Impl Formula Formula  | Iff Formula Formula
             | Atom String [Term]    | Not Formula
             | Top                   | Bot
             | Or Formula Formula    | And Formula Formula
             | Exists String Formula | Forall String Formula
  deriving (Eq)
instance Show Formula where
  show (Impl l r)    = "(" ++ (show l) ++ ") => (" ++ (show r) ++ ")"
  show (Iff l r)     = "(" ++ (show l) ++ ") <=> (" ++ (show r) ++ ")"
  show (Atom n args) = n ++ "(" ++ (intercalate "," $ map show args) ++ ")"
  show (Not f)       = "~(" ++ (show f) ++ ")"
  show (Top)         = "$true"
  show (Bot)         = "$false"
  show (Or l r)      = "(" ++ (show l) ++ ") | (" ++ (show r) ++ ")"
  show (And l r)     = "(" ++ (show l) ++ ") & (" ++ (show r) ++ ")"
  show (Exists v f)  = "? [" ++ quantifiedPrefix ++ v ++ "] : (" ++ (show $ replaceVar f v (quantifiedPrefix++v)) ++ ")"
  show (Forall v f)  = "! [" ++ quantifiedPrefix ++ v ++ "] : (" ++ (show $ replaceVar f v (quantifiedPrefix++v)) ++ ")"

getLeft (Iff l r) = l
getLeft (Forall v f) = getLeft f

getRight (Iff l r) = r
getRight (Forall v f) = getRight f

quantifiedPrefix = "V"
boundPrefix = "b"

safeVar :: Formula -> String -> Formula
safeVar (Atom s terms) v = Atom s $ safeVar' terms v
safeVar (Impl l r)     v = Impl (safeVar l v) (safeVar r v)
safeVar (Iff l r)      v = Iff (safeVar l v) (safeVar r v)
safeVar (Not f)        v = Not $ safeVar f v 
safeVar (Or l r)       v = Or (safeVar l v) (safeVar r v)
safeVar (And l r)      v = And (safeVar l v) (safeVar r v)
safeVar (Exists s f)   v = Exists s $ safeVar f v
safeVar (Forall s f)   v = Forall s $ safeVar f v
safeVar f              v = f

safeVar' :: [Term] -> String -> [Term]
safeVar' [] _ = []
safeVar' ((Var s):ts) v | s == v    = Var (quantifiedPrefix ++ v) : (safeVar' ts v) 
                        | otherwise = Var s : (safeVar' ts v) 
safeVar' ((Cons s t):ts) v = (Cons s (safeVar' t v)) : (safeVar' ts v) 


replaceVar :: Formula -> String -> String -> Formula
replaceVar (Atom s terms) old new = Atom s $ replaceVar' terms old new
replaceVar (Impl l r)     old new = Impl (replaceVar l old new) (replaceVar r old new)
replaceVar (Iff l r)      old new = Iff (replaceVar l old new) (replaceVar r old new)
replaceVar (Or l r)       old new = Or (replaceVar l old new) (replaceVar r old new)
replaceVar (And l r)      old new = And (replaceVar l old new) (replaceVar r old new)
replaceVar (Not f)        old new = Not $ replaceVar f old new 
replaceVar (Exists s f)   old new = Exists s $ replaceVar f old new
replaceVar (Forall s f)   old new = Forall s $ replaceVar f old new
replaceVar f              old new = f

replaceVar' :: [Term] -> String -> String -> [Term]
replaceVar' [] _ _ = []
replaceVar' ((Var s):ts) old new    | s == old    = Var (new) : (replaceVar' ts old new) 
                                    | otherwise   = Var s : (replaceVar' ts old new) 
replaceVar' ((Cons s t):ts) old new = (Cons s (replaceVar' t old new)) : (replaceVar' ts old new) 


-- Collection of sanity criteria for a formula
cleanFormula :: Formula -> Formula
cleanFormula f = cleanQuantifier f [] []

-- Remove multiple quantified variables
cleanQuantifier :: Formula -> [String] -> [String] -> Formula
cleanQuantifier (Forall s f)   a e = if s `elem` a then (cleanQuantifier f a e) else (Forall s (cleanQuantifier f (s:a) e))
cleanQuantifier (Exists s f)   a e = if s `elem` e then (cleanQuantifier f a e) else (Forall s (cleanQuantifier f a (s:e)))
cleanQuantifier (Impl l r)     a e = Impl (cleanQuantifier l a e) (cleanQuantifier r a e)
cleanQuantifier (Iff l r)      a e = Iff (cleanQuantifier l a e) (cleanQuantifier r a e)
cleanQuantifier (Or l r)       a e = Or (cleanQuantifier l a e) (cleanQuantifier r a e)
cleanQuantifier (And l r)      a e = And (cleanQuantifier l a e) (cleanQuantifier r a e)
cleanQuantifier (Not f)        a e = Not $ cleanQuantifier f a e
cleanQuantifier f              _ _ = f 



contains :: Formula -> [Term] -> Bool
contains (Atom _ fvs) vs = foldl (\a x -> x `elem` vs || a) False (concat $ map getVarsOfTerm fvs)
contains (Impl l r) vs = l `contains` vs || r `contains` vs
contains (Iff l r) vs = l `contains` vs || r `contains` vs
contains (Or l r) vs = l `contains` vs || r `contains` vs
contains (And l r) vs = l `contains` vs || r `contains` vs
contains (Not f) vs = f `contains` vs
contains (Exists _ f) vs = f `contains` vs
contains (Forall _ f) vs = f `contains` vs
contains f _ = False


universallyQuantify :: [Term] -> Formula -> Formula
universallyQuantify [] f = f 
universallyQuantify ((Var s):vs) f = Forall s $ universallyQuantify vs f



getVarsOfFormula :: Formula -> [Term]
getVarsOfFormula (Atom s ts)  = concat $ map getVarsOfTerm ts
getVarsOfFormula (Impl l r)   = getVarsOfFormula l ++ getVarsOfFormula r  
getVarsOfFormula (Iff l r)    = getVarsOfFormula l ++ getVarsOfFormula r  
getVarsOfFormula (Or l r)     = getVarsOfFormula l ++ getVarsOfFormula r  
getVarsOfFormula (And l r)    = getVarsOfFormula l ++ getVarsOfFormula r  
getVarsOfFormula (Not f)      = getVarsOfFormula f  
getVarsOfFormula (Exists s f) = getVarsOfFormula f  
getVarsOfFormula (Forall s f) = getVarsOfFormula f  
getVarsOfFormula _            = []             

getVarsOfTerm :: Term -> [Term]
getVarsOfTerm (Var s) = [(Var s)]
getVarsOfTerm (Cons _ ts) = concat $ map getVarsOfTerm ts

insertLets :: Formula -> [Formula] -> Formula
insertLets f [] = f
insertLets f ((Atom s ts):as) =
  if f `contains` vars
    then universallyQuantify vars ((Atom s ts) `Impl` (insertLets f as))
    else f
      where vars = concat $ map getVarsOfTerm ts


data Statement = Statement { id :: String
                           , formula :: Formula
                           , proof :: Proof
                           }
instance Show Statement where
  show (Statement id formula proof) = id ++ ": " ++ show formula ++ " -- " ++ show proof ++ "\n"


stat2Conj :: [Statement] -> Formula
stat2Conj [(Statement _ f _)] = f
stat2Conj ((Statement _ f _):xs) = f `And` (stat2Conj xs)

formulas2Conj :: [Formula] -> Formula
formulas2Conj [f] = f
formulas2Conj (f:fs) = f `And` formulas2Conj fs


strings2Vars :: [String] -> [Term]
strings2Vars = map (\s -> (Var s))

vars2Strings :: [Term] -> [String]
vars2Strings = map (\(Var s) -> s)

idPrefix :: String
idPrefix = "s"

getId :: Statement -> String
getId (Statement id f p) = drop (length idPrefix) id

data Proof = Assumed | ByContext | BySubcontext [String] | BySequence [Statement] | BySplit [Statement]
instance Show Proof where
  show Assumed = "Assumed"
  show ByContext = "ByContext"
  show (BySubcontext is) = "BySubcontext: " ++  (intercalate "" is)
  show (BySequence hs) = "Prove by seq:\n" ++ (concat $ map (\h -> "   " ++ show h) hs) ++ "   end seq"
  show (BySplit cs) = "Prove by split:\n" ++ (concat $ map (\c -> "   " ++ show c) cs)