module Verify where

import Language
import Parser



verifySection :: ESection -> String
verifySection (EDefinition sent) = (ef2TPTP $ sent2ef sent)
verifySection (EProposition sent) = "bsd"
verifySection (ELemma sent proof) = "csd"

verify :: EText -> String
verify (EText sections) = concat $ map verifySection sections

main :: IO()
main = do
  problem <- getContents
  print $ verify $ parseString problem 