
import Data.List

data Term = Const String [Term]
           | Var String
  deriving (Eq)
instance Show Term where
  show (Var s) = s
  show (Const s terms) = s ++ "(" ++ (intercalate "," $ map show terms) ++ ")" 


data Formula = Impl Formula Formula  | Iff Formula Formula
             | Atom String [Term]    | Not Formula
             | Top                   | Bottom
             | Or Formula Formula    | And Formula Formula
             | Exists String Formula | Forall String Formula
  deriving (Eq)
instance Show Formula where
  show (Impl l r)    = "(" ++ (show l) ++ ") => (" ++ (show r) ++ ")"
  show (Iff l r)    = "(" ++ (show l) ++ ") <=> (" ++ (show r) ++ ")"
  show (Atom n args) = n ++ "(" ++ (intercalate "," $ map show args) ++ ")"
  show (Not f)       = "~(" ++ (show f) ++ ")"
  show (Top)         = "$true"
  show (Bottom)      = "$false"
  show (Or l r)      = "(" ++ (show l) ++ ") | (" ++ (show r) ++ ")"
  show (And l r)     = "(" ++ (show l) ++ ") & (" ++ (show r) ++ ")"
  show (Exists v f)     = "? [" ++ v ++ "] : " ++ (show f)
  show (Forall v f)     = "! [" ++ v ++ "] : " ++ (show f)


data Statement = Statement { id :: String
                           , goal :: Formula
                           , proof :: Proof
                           }
instance Show Statement where
  show (Statement id goal proof) = id ++ ": " ++ show goal ++ " -- " ++ show proof ++ "\n"

data Proof = Assumed | ProofByContext | ProofByDerivation [Statement] 
instance Show Proof where
  show Assumed = "Assumed"
  show ProofByContext = "ProofByContext"
  show (ProofByDerivation hs) = "Proofed by derivation:\n" ++ (concat $ map (\h -> "   " ++ show h) hs)


data Context = Context [Statement] Context | Empty
instance Show Context where
  show (Context [] Empty) = ""
  show (Context [] p) = show p
  show (Context ((Statement id axiom proof):hs) p) = "fof(" ++ id ++ ", axiom, (" ++ show axiom ++ ")).\n" ++ show (Context hs p)


p = [
    (Statement "rIsRelation" (Atom "relation" [Var "R"]) Assumed),
    (Statement "xIsElement" (Atom "element" [Var "X"]) Assumed),
    (Statement "yIsElement" (Atom "element" [Var "Y"]) Assumed),
    (Statement "zIsElement" (Atom "element" [Var "Z"]) Assumed),
    (Statement "defSymmetric" (Forall "R" (Atom "symmetric" [Var "R"] `Iff` Forall "X" (Forall "Y" (Atom "relapp" [Var "R", Var "X", Var "Y"] `Impl` Atom "relapp" [Var "R", Var "Y", Var "X"])))) Assumed),
    (Statement "defBound" (Forall "R" (Atom "bound" [Var "R"] `Iff` Forall "X" (Exists "Y" (Atom "relapp" [Var "R", Var "X", Var "Y"])))) Assumed),
    (Statement "defTransitive" (Forall "R" (Atom "transitive" [Var "R"] `Iff` Forall "X" (Forall "Y" (Forall "Z" ((Atom "relapp" [Var "R", Var "X", Var "Y"] `And` Atom "relapp" [Var "R", Var "Y", Var "z"]) `Impl` Atom "relapp" [Var "R", Var "X", Var "z"]))))) Assumed),
    (Statement "defReflexive" (Forall "R" (Atom "reflexive" [Var "R"] `Iff` Forall "X" (Atom "relapp" [Var "R", Var "X", Var "X"]))) Assumed),
    (Statement "lemma" (((Atom "transitive" [Var "R"]) `And` (Atom "symmetric" [Var "R"]) `And` (Atom "bound" [Var "R"])) `Impl` (Atom "reflexive" [Var "R"])) 
        (ProofByDerivation [
          (Statement "lemmaAntecedent" ((Atom "transitive" [Var "R"]) `And` (Atom "symmetric" [Var "R"]) `And` (Atom "bound" [Var "R"])) Assumed), 
          (Statement "applyBound" (Atom "relapp" [Var "R", Var "X", Var "Y"]) ProofByContext),
          (Statement "applySymmetry" (Atom "relapp" [Var "R", Var "Y", Var "X"]) ProofByContext),
          (Statement "applyTransitivity" (Atom "relapp" [Var "R", Var "X", Var "X"]) ProofByContext),
          (Statement "lemmaConsequent" (Atom "reflexive" [Var "R"]) ProofByContext)
        ])
    )
    ]


task2TPTP :: Statement -> Context -> String
task2TPTP (Statement id goal ProofByContext) context = "BEGIN TPTP TASK\n" ++ show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show goal ++ ")).\nEND TPTP TASK\n"

verifyStatement :: Statement -> Context -> String
verifyStatement (Statement id goal Assumed) context = "Statement " ++ id ++ " " ++ show goal ++ " is assumed"
verifyStatement (Statement id goal ProofByContext) context = "Statement " ++ id ++ " is proved with task:\n" ++ task2TPTP (Statement id goal ProofByContext) context
verifyStatement (Statement id goal (ProofByDerivation derivation)) context = verifyDerivation derivation (Context [] context)

verifyDerivation :: [Statement] -> Context -> String
verifyDerivation [] context = "Derivation correct\n"
verifyDerivation (st:sts) (Context hs p) = (verifyStatement st (Context hs p)) ++ "\n" ++ verifyDerivation sts (Context (hs ++ [st]) p)

main :: IO()
main = do
  putStr $ verifyDerivation p (Context [] Empty)


