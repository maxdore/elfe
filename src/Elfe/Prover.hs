module Elfe.Prover where

import Data.List
import System.Process
import System.Exit
import System.IO
import System.IO.Error
import Debug.Trace

import Elfe.Language

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
    else trace ("UNKNOWN\n" ++ ofl ++ task) return Unknown
