module Settings where

import Elfe.Language

port :: Int
port = 8000

eprover = Prover "E Prover" "../prover/E/PROVER/eprover" ["--cpu-limit=20", "-s", "--auto-schedule"] ["# SZS status Theorem"] ["# SZS status CounterSatisfiable"] ["uns"]
z3 = Prover "Z3" "../prover/Z3/build/z3_tptp" ["-t:20"] ["% SZS status Theorem"] ["% SZS status CounterSatisfiable"] ["% SZS status GaveUp"]
spass = Prover "SPASS" "../prover/SPASS/SPASS" ["-TPTP", "-TimeLimit=20"] ["SPASS beiseite: Proof found."] ["SPASS beiseite: Completion found."] ["SPASS beiseite: Ran out of time."]
vampire = Prover "Vampire" "online-atps" ["--atp=vampire", "--only-check"] ["Theorem"] ["No theorem"] ["uns"]
beagle = Countermodler "BEAGLE" "../prover/beagle/beagle.sh" [] "Saturated clause set:"

provers = [eprover, z3, spass, vampire]
countermodler = [beagle]