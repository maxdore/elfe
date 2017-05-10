module Elfe.Language where

import Data.List
import Debug.Trace
import GHC.Generics (Generic)

data Term = Cons String [Term]
           | Var String

instance Eq Term where
    t == t' = (show t) == (show t')

instance Show Term where
  show (Var s) = "" ++ s
  show (Cons s []) = s
  show (Cons s terms) = functorToString s terms


data Formula = Impl Formula Formula  | Iff Formula Formula
             | Atom String [Term]    | Not Formula
             | Top                   | Bot
             | Or Formula Formula    | And Formula Formula
             | Exists String Formula | Forall String Formula

instance Eq Formula where
    f == f' = True --(show f) == (show f')

instance Show Formula where
  show (Impl l r)    = "(" ++ (show l) ++ ") => (" ++ (show r) ++ ")"
  show (Iff l r)     = "(" ++ (show l) ++ ") <=> (" ++ (show r) ++ ")"
  show (Atom n terms) = functorToString n terms
  show (Not f)       = "~(" ++ (show f) ++ ")"
  show (Top)         = "$true"
  show (Bot)         = "$false"
  show (Or l r)      = "(" ++ (show l) ++ ") | (" ++ (show r) ++ ")"
  show (And l r)     = "(" ++ (show l) ++ ") & (" ++ (show r) ++ ")"
  show (Exists v f)  = "? [" ++ quantifiedPrefix ++ v ++ "] : (" ++ (show $ replaceVar f v (quantifiedPrefix++v)) ++ ")"
  show (Forall v f)  = "! [" ++ quantifiedPrefix ++ v ++ "] : (" ++ (show $ replaceVar f v (quantifiedPrefix++v)) ++ ")"


replacements = [ ("sum", "$sum")
               , ("difference", "$difference")
               , ("product", "$product")
               , ("quotient", "$quotient")
               ]

replaceFunctors :: String -> [(String, String)] -> String
replaceFunctors n [] = n
replaceFunctors n (r:rs) = if fst r == n
                             then snd r
                             else replaceFunctors n rs

functorToString :: String -> [Term] -> String
functorToString n terms = if n == "equal"
                            then (show $ terms !! 0) ++ "=" ++ (show $ terms !! 1)
                            else (replaceFunctors n replacements) ++ "(" ++ (intercalate "," $ map show terms) ++ ")"


data Context = Context [Statement] Context | Empty
instance Show Context where
  show (Context [] Empty) = ""
  show (Context [] p) = show p
  show (Context ((Statement id axiom proof _):hs) p) = show (Context hs p) ++ "fof(" ++ id ++ ", axiom, (" ++ show axiom ++ ")).\n"

restrContext :: [Statement] -> [String] -> [Statement]
restrContext [] _ = []
restrContext (s:sts) ids | getId s `elem` ids = s : restrContext sts ids
                         | otherwise          = restrContext sts ids

restrictContext :: Context -> [String] -> Context
restrictContext (Context sts Empty) ids = Context (restrContext sts ids) Empty
restrictContext (Context sts p) ids = Context sts $ restrictContext p ids

data Position = Position (Int, Int) | None
  deriving (Eq, Show, Generic)

data ProverInfo = ProverName String
  deriving (Eq, Show, Generic)

data ProofStatus = Correct ProverInfo | Incorrect ProverInfo | Unknown
  deriving (Eq, Show, Generic)

data StatementStatus = StatementStatus { sid :: String
                                       , status :: ProofStatus
                                       , children :: [StatementStatus]
                                       , opos :: Position
                                       }
  deriving (Eq, Show, Generic)


quantifiedPrefix = "V"
boundPrefix = "c"

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
cleanQuantifier (Exists s f)   a e = if s `elem` e then (cleanQuantifier f a e) else (Exists s (cleanQuantifier f a (s:e)))
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

enfoldExists :: [Term] -> Formula -> Formula
enfoldExists [] f = f
enfoldExists ((Var v):vs) f = Exists v (enfoldExists vs f)


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
    else insertLets f as
      where vars = concat $ map getVarsOfTerm ts




formulas2Conj :: [Formula] -> Formula
formulas2Conj [] = Top
formulas2Conj [f] = f
formulas2Conj (f:fs) = f `And` formulas2Conj fs


strings2Vars :: [String] -> [Term]
strings2Vars = map (\s -> (Var s))

vars2Strings :: [Term] -> [String]
vars2Strings = map (\(Var s) -> s)

idPrefix :: String
idPrefix = "s"

getId :: Statement -> String
getId (Statement id _ _ _) = drop (length idPrefix) id

data Statement = Statement { id :: String
                           , formula :: Formula
                           , proof :: Proof
                           , pos :: Position
                           }

data Proof = Assumed | ByContext | BySubcontext [String] | BySequence [Statement] | BySplit [Statement]


instance Show Statement where show = prettyStatement 0
prettyStatement l (Statement id formula proof _) = (replicate (l*3) ' ') ++ id ++ ": " ++ show formula ++ " -- " ++ (prettyProof l proof)

prettyProof l Assumed = "Assumed\n"
prettyProof l ByContext = "ByContext\n"
prettyProof l (BySubcontext ids) = "BySubcontext: " ++  (intercalate "," ids) ++ "\n"
prettyProof l (BySequence hs) = "Prove by sequence:\n" ++ (concat $ map (prettyStatement (l+1)) hs)
prettyProof l (BySplit cs) = "Prove by split:\n" ++ (concat $ map (prettyStatement (l+1)) cs)

