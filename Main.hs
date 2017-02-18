import System.Environment (getArgs)

import Language
import Parser
import Prover
import Sequences

main = do
  args <- getArgs;
  case args of
    [] -> error "Give the problem file"
    [arg] -> do str <- readFile $ arg
                --problem <- parseString str
                --putStrLn $ show problem
                res <- verSeq p (Context [] Empty) (return Correct)
                putStrLn $ show res
    _ -> error "too many arguments - just give the file"