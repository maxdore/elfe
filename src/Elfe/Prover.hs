module Elfe.Prover where

import Data.List
import System.Process
import System.Exit
import System.IO
import System.IO.Error
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad

import Debug.Trace

import Elfe.Language

data Prover = Prover { name :: String
                     , command :: String
                     , args :: [String]
                     , provedMessage :: [String]
                     , disprovedMessage :: [String]
                     , unknownMessage :: [String]
                     }

eprover = Prover "E Prover" "../prover/E/PROVER/eprover" ["--cpu-limit=10", "-s", "--auto-schedule"] ["# SZS status Theorem"] ["# SZS status CounterSatisfiable"] ["uns"]
z3 = Prover "Z3" "../prover/Z3/build/z3_wrapper.sh" [] ["% SZS status Theorem"] ["% SZS status CounterSatisfiable"] ["% SZS status GaveUp"]

provers = [z3, eprover]

prove :: String -> IO ProofStatus
prove s = do
    done <- newEmptyMVar
    threads <- mapM (\p -> newChan >>= \ c -> forkIO $ runATP c s p done) provers
    prover <- readMVar done
    mapM killThread threads
    trace (show threads) return Correct


--runATP :: Chan ProofStatus -> String -> Prover -> IO ()
runATP channel task (Prover name command args provedMessage disprovedMessage unknownMessage) done = do
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
      then writeChan channel Correct >> putMVar done name
    else if neg
      then trace ("DISPROVED by " ++ name ++ "\n" ++ task) writeChan channel Incorrect
    else trace ("UNKNOWN by " ++ name ++ "\n" ++ ofl ++ task) writeChan channel Unknown
