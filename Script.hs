import Control.Applicative                                   
import System.IO                                             
import System.Process 

main = do                                                    
    (inn, out, err, idd) <- runInteractiveCommand "mongo"    
    mapM_ (flip hSetBinaryMode False) [inn, out]             
    hSetBuffering inn LineBuffering                          
    hSetBuffering out NoBuffering                            
    hPutStrLn inn "help"                                    
    parsedIntro <- parseUntilPrompt out                      
    mapM_ (putStrLn . \x -> "PARSED:: " ++  x) parsedIntro   

parseUntilPrompt :: Handle -> IO [String]                    
parseUntilPrompt out = do                                    
  latest <- hGetLine out                                     
  if latest == ""                                            
    then return []                                           
    else (:) <$> return latest <*> parseUntilPrompt out