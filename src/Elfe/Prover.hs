module Elfe.Prover where

import Data.List
--import Data.String.Utils (replace)
import System.Process
import System.Exit
import System.IO
import System.IO.Error
import System.Directory (removeFile)
import System.Random
import Control.Concurrent
import Control.Concurrent.Chan
import Control.Monad

import Debug.Trace

import Elfe.Language
import Settings (provers, countermodler, atpTimeout)

fileGenerator :: IO String
fileGenerator = do
  g <- newStdGen
  let rnd = take 12 $ randomRs ('a','z') g
  return $ rnd ++ ".tptp"

prove :: String -> IO ProofStatus
prove task = do
    tptpFile <- fileGenerator
    writeFile tptpFile task
    done <- newEmptyMVar
    chan <- newChan
    pThreads <- mapM (\p -> forkIO $ runProver chan task p done tptpFile) provers
    cThreads <- mapM (\p -> forkIO $ runCountermodler chan task p done tptpFile) countermodler
    timeoutThread <- forkIO $ timeout task chan done
    readMVar done
    result <- readChan chan
    mapM killThread ([timeoutThread]++pThreads++cThreads)
    removeFile tptpFile
    return result

runProver :: Chan ProofStatus -> String -> Prover -> MVar Bool -> String -> IO ()
runProver chan task (Prover name command args provedMsg disprovedMsg unknownMsg) done tptpFile = do
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

    when (pos) (trace ("PROVED by " ++ name) writeChan chan (Correct (ProverName name "")) >> putMVar done True)
    --when (neg) (("DISPROVED by " ++ name ++ "\n" ++ task) (return ())) -- writeChan chan (Incorrect (ProverName name "")) >> putMVar done True
    --when (not pos && not neg) (("UNKNOWN by " ++ name ++ "\n") (return ()))


runCountermodler :: Chan ProofStatus -> String -> Countermodler -> MVar Bool -> String -> IO ()
runCountermodler chan task (Countermodler name command args clauseMarker) done tptpFile = do
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
                            else cleaned ++ retrieveClauses rs
                              where cleaned = if s `strcontains` ", c" || s `strcontains` "(c"
                                                then s -- replace "(c" "(" (replace ", c" ", " s) ++ "\n" 
                                                else []


timeout :: String -> Chan ProofStatus -> MVar Bool -> IO ()
timeout task chan done = do
  threadDelay $ atpTimeout*1000000
  trace ("TIMEOUT\n" ++ task) writeChan chan Unknown >> putMVar done True
  
