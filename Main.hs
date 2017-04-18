import Control.Monad.Trans (lift)
import System.Environment (getArgs)

import Language
import Preprocessor
import Parser
import Prover
import Sequences

main = do
  args <- getArgs;
  case args of
    []    -> do res <- verSeq p (Context [] Empty) (return Correct) -- todo allow stdin 
                putStrLn $ show res
    [arg] -> do raw <- readFile arg
                let included = includeLibraries raw
                --putStrLn included
                problem <- parseString included
                print problem
                res <- verify problem
                putStrLn $ show res
    _ -> error "too many arguments - just give the file"