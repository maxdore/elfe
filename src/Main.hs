import System.Environment (getArgs)
import Criterion.Measurement (getTime, secs)

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
    putStrLn "\n--------------------------PARSING--------------------------"
    startParsing <- getTime
    let included = includeLibraries raw
    sequ <- parseString included
    endParsing <- getTime
    putStrLn $ concat $ map (prettyStatement 0) sequ
    putStrLn "-------------------------VERIFYING--------------------------" 
    startVerifying <- getTime
    res <- verify sequ
    endVerifying <- getTime
    putStrLn "---------------------------RESULT--------------------------" 
    printRes res
    putStrLn "-------------------------STATISTICS------------------------" 
    putStrLn $ "Parsing time: " ++ (secs $ endParsing - startParsing)
    putStrLn $ "Verifying time: " ++ (secs $ endVerifying - startVerifying)
    putStrLn $ "Total: " ++ (secs $ endParsing - startParsing + endVerifying - startVerifying)


printRes ss = if null (filterSs ss Unknown)
                 then putStrLn "Everything correct"
                 else putStrLn "Nope"
