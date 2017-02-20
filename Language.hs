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
  show (Exists v f)  = "? [" ++ varPrefix ++ v ++ "] : (" ++ (show $ safeVar f v) ++ ")"
  show (Forall v f)  = "! [" ++ varPrefix ++ v ++ "] : (" ++ (show $ safeVar f v) ++ ")"

varPrefix = "V"

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
safeVar' ((Var s):ts) v | s == v    = Var (varPrefix ++ v) : (safeVar' ts v) 
                        | otherwise = Var s : (safeVar' ts v) 
safeVar' ((Cons s t):ts) v = (Cons s (safeVar' t v)) : (safeVar' ts v) 


data Statement = Statement { id :: String
                           , formula :: Formula
                           , proof :: Proof
                           }
instance Show Statement where
  show (Statement id formula proof) = id ++ ": " ++ show formula ++ " -- " ++ show proof ++ "\n"


stat2Conj :: [Statement] -> String
stat2Conj [] = ""
stat2Conj [(Statement id formula proof)] = "(" ++ show formula ++ ")"
stat2Conj ((Statement id formula proof):xs) = "(" ++ show formula ++ ") & " ++ (stat2Conj xs)


getFormula (Statement id f p) = f

idPrefix = "s"
getId :: Statement -> String
getId (Statement id f p) = drop (length idPrefix) id

data Proof = Assumed | ByContext | BySubcontext [String] | BySequence [Statement] | BySplit [Statement]
instance Show Proof where
  show Assumed = "Assumed"
  show ByContext = "ByContext"
  show (BySubcontext is) = "BySubcontext: " ++  (intercalate "" is)
  show (BySequence hs) = "Prove by seq:\n" ++ (concat $ map (\h -> "   " ++ show h) hs)
  show (BySplit cs) = "Prove by cases:\n" ++ (concat $ map (\c -> "   " ++ show c) cs)