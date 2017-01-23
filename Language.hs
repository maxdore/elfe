module Language where

import Data.List

-- Data structures to represent FOL

data Term = Const String [Term]
           | Var String
  deriving (Eq, Show)

data Formula = Impl Formula Formula
              | Atom String [Term]    | Not Formula
              | Top                   | Bottom
              | Or Formula Formula    | And Formula Formula
              | Exists String Formula | Forall String Formula
  deriving (Eq, Show)


data ERole = Axiom | Conjecture
  deriving (Eq, Show)

data EFormula = EFormula { name :: String
                         , role :: ERole
                         , formula :: Formula
                         }
  deriving (Eq, Show)

-- The main data structures for an Elfe-text

data EText = EText [ESection]
  deriving (Eq, Show)

data ESection = EDefinition ESent 
              | EProposition ESent
              | ELemma ESent [ESent]
  deriving (Eq, Show)

data ESent = EAssignProp EVar EProp
           | EIff ESent ESent
           | EImpl ESent ESent
           | EForall EVar ESent
           | ESent String
  deriving (Eq, Show)

data EVar = EVar String
  deriving (Eq, Show)

data EProp = EProp String
  deriving (Eq, Show)


-- Converts a text to formulas

sent2ef :: ESent -> EFormula
sent2ef (EAssignProp var prop) = EFormula "name" Axiom (Atom (show var) [Var (show prop)])

-- Converts a formula to TPTP-Syntax

ef2TPTP :: EFormula -> String
ef2TPTP (EFormula n r f) = "fof(" ++ n ++ ", " ++ (show r) ++ ", " ++ (f2TPTP f) ++ ")"

f2TPTP :: Formula -> String
f2TPTP (Impl l r)    = "(" ++ (f2TPTP l) ++ ") => (" ++ (f2TPTP r) ++ ")"
f2TPTP (Atom n args) = n ++ "(" ++ "(intercalate  args)" ++ ")"
f2TPTP (Not f)       = "~(" ++ (f2TPTP f) ++ ")"
f2TPTP (Top)         = "$true"
f2TPTP (Bottom)      = "$false"
f2TPTP (Or l r)      = "(" ++ (f2TPTP l) ++ ") | (" ++ (f2TPTP r) ++ ")"
f2TPTP (And l r)     = "(" ++ (f2TPTP l) ++ ") & (" ++ (f2TPTP r) ++ ")"

