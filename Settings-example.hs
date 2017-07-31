module Settings where

import Elfe.Language

port :: Int
port = 8000

vampire = Prover "Vampire" "online-atps" ["--atp=vampire", "--only-check"] ["Theorem"] ["No theorem"] ["uns"]
beagle = Countermodler "BEAGLE" "beagle" [] "Saturated clause set:"

provers = [vampire]
countermodler = [beagle]