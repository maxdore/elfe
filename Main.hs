import Control.Monad.Trans (lift)
import System.Environment (getArgs)

import Elfe

main :: IO ()
main = do
  args <- getArgs;
  case args of
    []    -> do raw <- getContents
                check raw
    [arg] -> do raw <- readFile arg
                check raw 
    _ -> error "too many arguments - just give the file"

check :: String -> IO ()
check raw = do
    let included = includeLibraries raw
    problem <- parseString included
    putStrLn "--------------------------PARSING--------------------------"
    putStrLn $ show problem
    putStrLn "-------------------------VERIFYING-------------------------" 
    res <- verify problem
    putStrLn $ show res