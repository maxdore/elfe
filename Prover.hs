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


-- CONTEXT MANAGMENT

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



-- MAIN PROVING LOGIC

data ProofStatus = Correct | Incorrect | Unknown
  deriving (Eq, Show)

verStat :: Statement -> Context -> IO ProofStatus
verStat (Statement id f Assumed) context = trace ("Assume " ++ id ++ ": " ++ show f) return Correct 
verStat (Statement id f ByContext) context = trace ("Prove  " ++ id ++ ": " ++ show f) checkStat (Statement id f ByContext) context 
verStat (Statement id f (BySubcontext ids)) context = trace ("Prove  " ++ id ++ ": " ++ show f ++ " by " ++ concat ids) checkStat (Statement id f ByContext) $ subContext context ids
verStat (Statement id f (BySequence sequ)) context = trace ("Check  " ++ id ++ ": " ++ show f) verSeq sequ (Context [] context) (return Correct) 
verStat (Statement id f (BySplit cases)) context = trace ("Cases  " ++ id ++ ": " ++ show f) verCaseDist (Statement id f Assumed) cases context

verSeq :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verSeq [] _ status = status
verSeq (st:sts) (Context hs p) status = do
  r <- verStat st (Context hs p)
  if r == Correct then verSeq sts (Context (hs ++ [st]) p) status 
  else verSeq sts (Context (hs ++ [st]) p) (return Incorrect)

checkStat :: Statement -> Context -> IO ProofStatus
checkStat (Statement id formula p) context = runProver (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n") --return Correct

verCaseDist :: Statement -> [Statement] -> Context -> IO ProofStatus
verCaseDist (Statement id formula _) cases context = do
  distR <- trace ("Prove distinction correct:\n" ++ stat2Conj cases) runProver (show context ++ "fof(" ++ id ++ ", conjecture, ((" ++ stat2Conj cases ++ ") => (" ++ show formula ++ "))).\n") 
  caseR <- verifyCases cases context (return Correct)
  if distR == Correct && caseR == Correct
    then return Correct
    else return Incorrect

verifyCases :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verifyCases [] context status = status 
verifyCases (c:cs) context status = do
  r <- verStat c context
  if r == Correct then verifyCases cs context status 
  else verifyCases cs context (return Incorrect)


-- PROVER CALL

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
