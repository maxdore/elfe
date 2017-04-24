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
spass = Prover "SPASS" "../prover/SPASS/SPASS" ["-TPTP", "-Stdin"] ["SPASS beiseite: Proof found."] ["SPASS beiseite: Completion found."] ["SPASS beiseite: Ran out of time."]
beagle = Prover "BEAGLE" "java -jar ~/bin/beagle/target/scala-2.11/beagle.jar" [] ["SPASS beiseite: Proof found."] ["SPASS beiseite: Completion found."] ["SPASS beiseite: Ran out of time."]

provers = [z3, eprover, spass]

prove :: String -> IO ProofStatus
prove s = do
    done <- newEmptyMVar
    chan <- newChan
    threads <- mapM (\p -> forkIO $ runATP chan s p done) provers
    timeoutThread <- forkIO $ timeout chan done
    readMVar done
    result <- readChan chan
    mapM killThread $ threads++[timeoutThread]
    return result

--runATP :: Chan ProofStatus -> String -> Prover -> IO ()
runATP chan task (Prover name command args provedMessage disprovedMessage unknownMessage) done = do
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
      then trace ("PROVED by " ++ name) writeChan chan Correct >> putMVar done True
    else if neg
      then trace ("DISPROVED by " ++ name ++ "\n" ++ task) writeChan chan Incorrect >> putMVar done True
    else trace ("UNKNOWN by " ++ name ++ "\n" ++ ofl ++ task) return ()


timeout chan done = do
  threadDelay $ 10*1000000
  trace ("TIMEOUT") writeChan chan Unknown >> putMVar done True
  