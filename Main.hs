import System.Environment (getArgs)

import Elfe

main :: IO ()
main = do
  args <- getArgs
  case args of
    []    -> do raw <- getContents
                check raw
    [arg] -> do raw <- readFile arg
                check raw 
    _ -> error "too many arguments - just give the file"

check :: String -> IO ()
check raw = do
    let included = includeLibraries raw
    putStrLn "\n--------------------------PARSING--------------------------"
    sequ <- parseString included
    putStrLn $ concat $ map (prettyStatement 0) sequ
    putStrLn "-------------------------VERIFYING-------------------------" 
    res <- verify sequ
    putStrLn "--------------------------FINISHED-------------------------" 
