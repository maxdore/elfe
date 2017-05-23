module Elfe.Prover where

import Data.List
import System.Process
import System.Exit
import System.IO
import System.IO.Error
import System.Directory (removeFile)
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad

import Debug.Trace

import Elfe.Language

data Prover = Prover { pName :: String
                     , pCommand :: String
                     , pArgs :: [String]
                     , provedMsg :: [String]
                     , disprovedMsg :: [String]
                     , unknownMsg :: [String]
                     }

data Countermodler = Countermodler { cName :: String
                                   , cCommand :: String
                                   , cArgs :: [String]
                                   , clauseMarker :: String
                                   }

eprover = Prover "E Prover" "../prover/E/PROVER/eprover" ["--cpu-limit=5", "-s", "--auto-schedule"] ["# SZS status Theorem"] ["# SZS status CounterSatisfiable"] ["uns"]
z3 = Prover "Z3" "../prover/Z3/build/z3_tptp" ["-t:5"] ["% SZS status Theorem"] ["% SZS status CounterSatisfiable"] ["% SZS status GaveUp"]
spass = Prover "SPASS" "../prover/SPASS/SPASS" ["-TPTP", "-TimeLimit=5"] ["SPASS beiseite: Proof found."] ["SPASS beiseite: Completion found."] ["SPASS beiseite: Ran out of time."]
beagle = Countermodler "BEAGLE" "../prover/beagle/beagle.sh" [] "Saturated clause set:"

provers = [z3, eprover, spass]
countermodler = [beagle]

--tptpFile = "temp/wrong.tptp"
tptpFile = "task.tptp"

prove :: String -> IO ProofStatus
prove task = do
    writeFile tptpFile task
    done <- newEmptyMVar
    chan <- newChan
    pThreads <- mapM (\p -> forkIO $ runProver chan task p done) provers
    cThreads <- mapM (\p -> forkIO $ runCountermodler chan task p done) countermodler
    timeoutThread <- forkIO $ timeout task chan done
    readMVar done
    result <- readChan chan
    mapM killThread ([timeoutThread]++pThreads++cThreads)
    removeFile tptpFile
    return result

runProver :: Chan ProofStatus -> String -> Prover -> MVar Bool -> IO ()
runProver chan task (Prover name command args provedMsg disprovedMsg unknownMsg) done = do
  let run = runInteractiveProcess command (tptpFile:args) Nothing Nothing
  do 
    (wh,rh,eh,ph) <- run
    hPutStrLn wh task ; hClose wh
    ofl <- hGetContents rh
    --efl <- hGetContents eh
    let lns = filter (not . null) $ lines $ ofl -- ++ efl

    let pos = any (\l -> any (`isPrefixOf` l) provedMsg) lns
        neg = any (\l -> any (`isPrefixOf` l) disprovedMsg) lns
        unk = any (\l -> any (`isPrefixOf` l) unknownMsg) lns

    hClose eh ; waitForProcess ph

    if pos
      then trace ("PROVED by " ++ name) writeChan chan (Correct (ProverName name "")) >> putMVar done True
    else if neg
      then trace ("DISPROVED by " ++ name) return () -- writeChan chan (Incorrect (ProverName name "")) >> putMVar done True
    else trace ("UNKNOWN by " ++ name ++ "\n" ++ ofl ++ command ++ " " ++   show (args++[tptpFile])) return ()


runCountermodler :: Chan ProofStatus -> String -> Countermodler -> MVar Bool -> IO ()
runCountermodler chan task (Countermodler name command args clauseMarker) done = do
  let run = runInteractiveProcess command (tptpFile:args) Nothing Nothing
  do 
    (wh,rh,eh,ph) <- run
    hPutStrLn wh task ; hClose wh
    ofl <- hGetContents rh
    let startMarker = elemIndex clauseMarker $ lines ofl
    case startMarker of
      Nothing -> return ()
      Just start -> do 
        let contermodel = retrieveClauses $ drop (start+1) $ lines ofl
        traceM $ show $ contermodel
        writeChan chan (Incorrect (ProverName name contermodel)) >> putMVar done True


retrieveClauses :: [String] -> String
retrieveClauses [] = []
retrieveClauses (s:rs) = if s == ""
                            then ""
                            else s ++ "\n" ++ retrieveClauses rs


timeout :: String -> Chan ProofStatus -> MVar Bool -> IO ()
timeout task chan done = do
  threadDelay $ 5*1000000
  trace ("TIMEOUT\n" ++ task) writeChan chan Unknown >> putMVar done True
  