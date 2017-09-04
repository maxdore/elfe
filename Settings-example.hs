module Settings where

import Elfe.Language

port :: Int
port = 8000

vampire = Prover "Vampire" "online-atps" ["--atp=vampire", "--only-check"] ["Theorem"] ["No theorem"] ["uns"]
eprover = Prover "E Prover" "../prover/eprover/PROVER/eprover" ["--cpu-limit=20", "-s", "--auto-schedule"] ["# SZS status Theorem"] ["# SZS status CounterSatisfiable"] ["uns"]
beagle = Countermodler "BEAGLE" "beagle" [] "Saturated clause set:"

provers = [vampire, eprover]
countermodler = [beagle]