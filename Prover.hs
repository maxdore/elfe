module Prover where

import Control.Applicative                                   
import Control.Exception
import Control.Monad                                   
import Data.List
import System.Process
import System.Exit
import System.IO
import System.IO.Error
import Debug.Trace

import Language


data Context = Context [Statement] Context | Empty
instance Show Context where
  show (Context [] Empty) = ""
  show (Context [] p) = show p
  show (Context ((Statement id axiom proof):hs) p) = show (Context hs p) ++ "fof(" ++ id ++ ", axiom, (" ++ show axiom ++ ")).\n"


restrContext :: Context -> [String] -> [Statement]
restrContext (Context [] Empty)  ids = []
restrContext (Context [] p)      ids = restrContext p ids
restrContext (Context (s:sts) p) ids | getId s `elem` ids = s : (restrContext (Context sts p) ids)
                                     | otherwise          = (restrContext (Context sts p) ids)

subContext :: Context -> [String] -> Context
subContext (Context cur p) ids = Context (cur ++ (restrContext p ids)) Empty

p = [
    (Statement "rIsRelation" (Atom "relation" [Var "R"]) Assumed),
    (Statement "xIsElement" (Atom "element" [Var "X"]) Assumed),
    (Statement "yIsElement" (Atom "element" [Var "Y"]) Assumed),
    (Statement "zIsElement" (Atom "element" [Var "Z"]) Assumed),
    (Statement "defSymmetric" (Forall "R" (Atom "symmetric" [Var "R"] `Iff` Forall "X" (Forall "Y" (Atom "relapp" [Var "R", Var "X", Var "Y"] `Impl` Atom "relapp" [Var "R", Var "Y", Var "X"])))) Assumed),
    (Statement "defBound" (Forall "R" (Atom "bound" [Var "R"] `Iff` Forall "X" (Atom "element" [Var "X"] `Impl` Exists "Y" (Atom "relapp" [Var "R", Var "X", Var "Y"])))) Assumed),
    (Statement "defTransitive" (Forall "R" (Atom "transitive" [Var "R"] `Iff` Forall "X" (Forall "Y" (Forall "Z" ((Atom "relapp" [Var "R", Var "X", Var "Y"] `And` Atom "relapp" [Var "R", Var "Y", Var "Z"]) `Impl` Atom "relapp" [Var "R", Var "X", Var "Z"]))))) Assumed),
    (Statement "defReflexive" (Forall "R" (Atom "reflexive" [Var "R"] `Iff` Forall "X" (Atom "relapp" [Var "R", Var "X", Var "X"]))) Assumed),
    (Statement "lemma" (((Atom "transitive" [Var "R"]) `And` (Atom "symmetric" [Var "R"]) `And` (Atom "bound" [Var "R"])) `Impl` (Atom "reflexive" [Var "R"])) 
        (BySequence [
          (Statement "lemmaAntecedent" ((Atom "transitive" [Var "R"]) `And` (Atom "symmetric" [Var "R"]) `And` (Atom "bound" [Var "R"])) Assumed), 
          (Statement "applyBound" (Atom "relapp" [Var "R", Var "X", Var "Y"]) ByContext),
          (Statement "applySymmetry" (Atom "relapp" [Var "R", Var "Y", Var "X"]) ByContext),
          (Statement "applyTransitivity" (Atom "relapp" [Var "R", Var "X", Var "X"]) ByContext),
          (Statement "lemmaConsequent" (Atom "reflexive" [Var "R"]) ByContext)
        ])
    )
    ]

p2 = [
      (Statement "defRational" ((Atom "rational" [Var "X"]) `Iff` (Exists "A" (Exists "B" ((Atom "relprime" [Var "A", Var "B"]) `And` (Atom "equals" [Var "X", Cons "frac" [Var "A", Var "B"]]))))) Assumed),
      (Statement "defIrrational" ((Atom "irrational" [Var "X"]) `Iff` (Not (Atom "rational" [Var "X"]))) Assumed),
      (Statement "defDiv" ((Atom "div" [Var "2", Var "Y"]) `Iff` (Exists "X" (Atom "equals" [Cons "times" [Var "X", Var "2"], Var "Y"]))) Assumed),
      --(Statement "divPowClosure" ((Atom "div" [Var "X", Var "Y"]) `Impl` (Atom "div" [Var "X", Cons "pow" [Var "Y"]])) Assumed),
      (Statement "sqrtPow" (Atom "equals" [Var "X", Cons "pow" [Cons "sqrt" [Var "X"]]]) Assumed),
      (Statement "equalSymmetric" ((Atom "equals" [Var "X", Var "Y"]) `Impl` (Atom "equals" [Var "Y", Var "X"])) Assumed),
      (Statement "equalTransitive" (((Atom "equals" [Var "X", Var "Y"]) `And` (Atom "equals" [Var "Y", Var "Z"])) `Impl` (Atom "equals" [Var "X", Var "Z"])) Assumed),
      (Statement "equalReflexive" (Atom "equals" [Var "X", Var "X"]) Assumed),
      (Statement "timesComm" (Atom "equals" [Cons "times" [Var "X", Var "Y"], Cons "times" [Var "Y", Var "X"]]) Assumed),
      (Statement "powIntro" ((Atom "equals" [Var "X", Var "Y"]) `Impl` (Atom "equals" [Cons "pow" [Var "X"], Cons "pow" [Var "Y"]])) Assumed),
      --(Statement "powInFrac" (Atom "equals" [Cons "pow" [Cons "frac" [Var "X", Var "Y"]], Cons "frac" [Cons "pow" [Var "X"], Cons "pow" [Var "Y"]]]) Assumed),
      (Statement "fracSymm" ((Atom "equals" [Var "X", Cons "frac" [Var "Y", Var "Z"]]) `Impl` (Atom "equals" [Cons "times" [Var "X", Var "Z"], Var "Y"])) Assumed),
      (Statement "lemma" (Atom "irrational" [Cons "sqrt" [Var "2"]]) 
        (BySequence [
            (Statement "negLemma" (Atom "rational" [Cons "sqrt" [Var "2"]]) Assumed),
            (Statement "existsPrime" ((((Atom "relprime" [Var "A", Var "B"]) `And` (Atom "equals" [Cons "sqrt" [Var "2"], Cons "frac" [Var "A", Var "B"]])))) ByContext),
            (Statement "transform" (Atom "equals" [Var "2", Cons "frac" [Cons "pow" [Var "A"], Cons "pow" [Var "B"]]]) ByContext),
            (Statement "transform2" (Atom "equals" [Cons "times" [Var "2", Cons "pow" [Var "B"]], Cons "pow" [Var "A"]]) ByContext),
            (Statement "transform2" (Atom "div" [Var "2", Var "A"]) ByContext)
            --(Statement "bot" (Atom "test" [Var "X"]) ByContext)

        ]))
     ]


-- A = ( A \ B ) ∪ ( A ∩ B )
pCases = [
  (Statement "setsEqualProof" ((Atom "equals" [Var "A", Var "B"]) `Iff` (((Atom "elem" [Var "X", Var "A"]) `Impl` (Atom "elem" [Var "X", Var "B"])) `And` ((Atom "elem" [Var "X", Var "B"]) `Impl` (Atom "elem" [Var "X", Var "A"])))) Assumed),
  (Statement "lemma" (Atom "equals" [Var "A", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) 
    (BySplit [
      (Statement "leftImplRight" ((Atom "elem" [Var "X", Var "A"]) `Impl` (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])) 
          (BySequence [
              (Statement "takeXInLeft" (Atom "elem" [Var "$fixedX", Var "A"]) Assumed),
              (Statement "xInRight" (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])
                (BySplit [
                  (Statement "xInB" ((Atom "elem" [Var "X", Var "B"]) `Impl` (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])) 
                     (BySequence [
                        (Statement "fixedXinB" (Atom "elem" [Var "X", Var "B"]) Assumed),
                        (Statement "xInAintsecB" (Atom "elem" [Var "X", Cons "intsec" [Var "A", Var "B"]]) ByContext),
                        (Statement "xInRight" (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) ByContext)
                      ])
                  ),
                  (Statement "xNotInB" (Not ((Atom "elem" [Var "X", Var "B"])) `Impl` (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])) 
                     (BySequence [
                        (Statement "fixedXinB" (Not (Atom "elem" [Var "X", Var "B"])) Assumed),
                        (Statement "xInAdiffB" (Atom "elem" [Var "X", Cons "diff" [Var "A", Var "B"]]) ByContext),
                        (Statement "xInRight" (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) ByContext)
                     ])
                  )
                ])
              )
          ])
        ),
      (Statement "rightImplLeft" ((Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) `Impl` (Atom "elem" [Var "X", Var "A"])) Assumed)
    ])
  )
 ]

-- n! ≤ n for any integer n ≥ 1.
--IA For n=1 (1.3) is true, since 1! = 11
--IH Suppose (1.3) is true for some n = k ≥ 1, that is k! ≤ k
--IS Prove that (1.3) is true for n = k + 1, that is (k + 1)! ≤ (k + 1)^(k+1)
--(k + 1)! = k! · (k + 1) ≤ k^k (k+1) < (k + 1)^k * (k + 1) = (k + 1)^(k+1)

pInduction = [
    (Statement "lesseqWellfounded" (Atom "welldefined" [Var "lesseq"]) Assumed),
    --(Statement "inductionProof" ((Atom "welldefined" [Var "rel"]) `And` (Atom "rel" []) `Impl` Bot) Assumed),
    (Statement "lesseq" ((Atom "lesseq" [Var "X", Var "Y"]) `Iff` (Atom "equals" [Var "X", Var "Y"] `Or` Atom "less" [Var "X", Var "Y"]) ) Assumed),
    (Statement "facBase" (Atom "equals" [Cons "fac" [Var "1"], Var "1"]) Assumed),
    --(Statement "facRec" (Atom "equals" [Cons "fac" [Var "n"], Var "1"]) Assumed),
    (Statement "lemma" (Atom "lesseq" [Cons "fac" [Var "n"], Var "n"]) 
      (BySplit [
          (Statement "inductionStart" ((Atom "lesseq" [Cons "fac" [Var "1"], Var "1"])) ByContext),
          (Statement "inductionStep" ((Atom "lesseq" [Cons "fac" [Cons "plus" [Var "n", Var "1"]], Cons "plus" [Var "n", Var "1"]])) 
            (BySequence [
              (Statement "inductionHypothesis" (Atom "lesseq" [Cons "fac" [Var "n"], Var "n"]) Assumed),
              -- ...
              (Statement "inductionformula" (Atom "lesseq" [Cons "fac" [Cons "plus" [Var "n", Var "1"]], Cons "plus" [Var "n", Var "1"]]) ByContext)
            ]) )
      ])
    )
  ]

data ProofStatus = Correct | Incorrect | Unknown
  deriving (Eq, Show)

checkStat :: Statement -> Context -> IO ProofStatus
checkStat (Statement id formula p) context = runProver (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n") --return Correct

runProver :: String -> IO ProofStatus
runProver task = do
  let run = runInteractiveProcess "../prover/E/PROVER/eprover" ["--definitional-cnf=24", "-s", "--print-statistics", "-R", "--print-version", "--proof-object", "--auto-schedule"] Nothing Nothing
  do 
    (wh,rh,eh,ph) <- run
    hPutStrLn wh task ; hClose wh
    ofl <- hGetContents rh
    --efl <- hGetContents eh
    let lns = filter (not . null) $ lines $ ofl -- ++ efl

    let pos = any (\l -> any (`isPrefixOf` l) ["# SZS status Theorem"]) lns
        neg = any (\l -> any (`isPrefixOf` l) ["# SZS status CounterSatisfiable"]) lns
        unk = any (\l -> any (`isPrefixOf` l) ["uns"]) lns

    hClose eh ; waitForProcess ph

    if pos
      then trace "PROVED" return Correct
    else if neg
      then trace "DISPROVED" return Incorrect
    else trace "UNKNOWN" return Unknown

stat2Conj :: [Statement] -> String
stat2Conj [] = ""
stat2Conj [(Statement id formula proof)] = "(" ++ show formula ++ ")"
stat2Conj ((Statement id formula proof):xs) = "(" ++ show formula ++ ") & " ++ (stat2Conj xs)

verifyCases :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verifyCases [] context status = status 
verifyCases (c:cs) context status = do
  r <- verStat c context
  if r == Correct then verifyCases cs context status 
  else verifyCases cs context (return Incorrect)

verCaseDist :: Statement -> [Statement] -> Context -> IO ProofStatus
verCaseDist (Statement id formula _) cases context = do
  distR <- trace ("Prove distinction correct:\n" ++ stat2Conj cases) runProver (show context ++ "fof(" ++ id ++ ", conjecture, ((" ++ stat2Conj cases ++ ") => (" ++ show formula ++ "))).\n") 
  caseR <- verifyCases cases context (return Correct)
  if distR == Correct && caseR == Correct
    then return Correct
    else return Incorrect


verStat :: Statement -> Context -> IO ProofStatus
verStat (Statement id f Assumed) context = trace ("Assume " ++ id ++ ": " ++ show f) return Correct 
verStat (Statement id f ByContext) context = trace ("Prove  " ++ id ++ ": " ++ show f) checkStat (Statement id f ByContext) context 
verStat (Statement id f (BySubcontext ids)) context = trace ("Prove  " ++ id ++ ": " ++ show f) checkStat (Statement id f ByContext) $ subContext context ids
verStat (Statement id f (BySequence sequ)) context = trace ("Check  " ++ id ++ ": " ++ show f) verSeq sequ (Context [] context) (return Correct) 
verStat (Statement id f (BySplit cases)) context = trace ("Cases  " ++ id ++ ": " ++ show f) verCaseDist (Statement id f Assumed) cases context

verSeq :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verSeq [] _ status = status
verSeq (st:sts) (Context hs p) status = do
  r <- verStat st (Context hs p)
  if r == Correct then verSeq sts (Context (hs ++ [st]) p) status 
  else verSeq sts (Context (hs ++ [st]) p) (return Incorrect)

--main :: IO()
--main = do
  --res <- verSeq p (Context [] Empty) (return Correct)
  --putStrLn $ show res

