{-# LANGUAGE DeriveGeneric #-}

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

import GHC.Generics (Generic)

-- CONTEXT MANAGMENT

data Context = Context [Statement] Context | Empty
instance Show Context where
  show (Context [] Empty) = ""
  show (Context [] p) = show p
  show (Context ((Statement id axiom proof):hs) p) = show (Context hs p) ++ "fof(" ++ id ++ ", axiom, (" ++ show axiom ++ ")).\n"

restrContext :: [Statement] -> [String] -> [Statement]
restrContext [] _ = []
restrContext (s:sts) ids | getId s `elem` ids = s : restrContext sts ids
                         | otherwise          = restrContext sts ids

subContext :: Context -> [String] -> Context
subContext (Context sts Empty) ids = Context (restrContext sts ids) Empty
subContext (Context sts p) ids = Context sts $ subContext p ids


-- MAIN PROVING LOGIC

data ProofStatus = Correct | Incorrect | Unknown
  deriving (Eq, Show, Generic)

verify problem = verSeq problem (Context [] Empty) (return Correct)

verStat :: Statement -> Context -> IO ProofStatus
verStat (Statement id f Assumed) context = trace ("Assume " ++ id ++ ": " ++ show f) return Correct 
verStat (Statement id f ByContext) context = trace ("Prove  " ++ id ++ ": " ++ show f) checkStat (Statement id f ByContext) context 
verStat (Statement id f (BySubcontext ids)) context = trace ("Prove  " ++ id ++ ": " ++ show f ++ " by " ++ concat ids) checkStat (Statement id f ByContext) $ subContext context ids
verStat (Statement id f (BySequence sequ)) context = trace ("Check  " ++ id ++ ": " ++ show f) verSeq sequ (Context [] context) (return Correct) 
verStat (Statement id f (BySplit cases)) context = trace ("Cases  " ++ id ++ ": " ++ show f) verifyCases cases context (return Correct)

verSeq :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verSeq [] _ status = status
verSeq (st:sts) (Context hs p) status = do
  r <- verStat st (Context hs p)
  if r == Correct then verSeq sts (Context (hs ++ [st]) p) status 
  else verSeq sts (Context (hs ++ [st]) p) (return Incorrect)

checkStat :: Statement -> Context -> IO ProofStatus
checkStat (Statement id formula p) context = prove (show context ++ "fof(" ++ id ++ ", conjecture, (" ++ show formula ++ ")).\n") --return Correct

verifyCases :: [Statement] -> Context -> IO ProofStatus -> IO ProofStatus
verifyCases [] context status = status 
verifyCases (c:cs) context status = do
  r <- verStat c context
  if r == Correct then verifyCases cs context status 
  else verifyCases cs context (return Incorrect)


-- BACKGROUND PROVER

data Prover = Prover { command :: String
                     , args :: [String]
                     , provedMessage :: [String]
                     , disprovedMessage :: [String]
                     , unknownMessage :: [String]
                     }

eprover = Prover "../prover/E/PROVER/eprover" ["--definitional-cnf=24", "-s", "--print-statistics", "-R", "--print-version", "--proof-object", "--auto-schedule"] ["# SZS status Theorem"] ["# SZS status CounterSatisfiable"] ["uns"]
z3 = Prover "../prover/Z3/build/z3_wrapper.sh" [] ["% SZS status Theorem"] ["% SZS status CounterSatisfiable"] ["% SZS status GaveUp"]

prove :: String -> IO ProofStatus
prove s = runATP s z3
  
runATP :: String -> Prover -> IO ProofStatus
runATP task (Prover command args provedMessage disprovedMessage unknownMessage) = do
  let run = runInteractiveProcess command args Nothing Nothing
  do 
    (wh,rh,eh,ph) <- run
    hPutStrLn wh task ; hClose wh
    ofl <- hGetContents rh
    --efl <- hGetContents eh
    let lns = filter (not . null) $ lines $ ofl -- ++ efl

    let pos = any (\l -> any (`isPrefixOf` l) provedMessage) lns
        neg = any (\l -> any (`isPrefixOf` l) disprovedMessage) lns
        unk = any (\l -> any (`isPrefixOf` l) unknownMessage) lns

    hClose eh ; waitForProcess ph

    if pos
      then trace "PROVED" return Correct
    else if neg
      then trace ("DISPROVED\n" ++ task) return Incorrect
    else trace ("UNKNOWN\n" ++ ofl) return Unknown
