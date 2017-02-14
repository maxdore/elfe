import Language
import Parser
import Prover


main = do
  p <- getContents
  s <- parseString p
  res <- verifySequence s (Context [] Empty) (return Correct)
  putStrLn $ show res