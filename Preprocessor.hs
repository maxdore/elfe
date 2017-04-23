module Preprocessor where

import Data.List
import Data.Maybe (listToMaybe)
import System.IO.Unsafe (unsafePerformIO)

incMarker :: String
incMarker = "Include "

includeLibraries :: String -> String
includeLibraries t = case findSubstring incMarker t of
    Nothing -> t
    Just i -> includeLibraries $ insertLibrary t i

insertLibrary :: String -> Int -> String
insertLibrary t i = inserted
    where lname = strPrefix $ drop (i + length incMarker) t
          lcontent = unsafePerformIO $ readFile $ "library/" ++ lname ++ ".elfe"
          inserted = take i t ++ lcontent ++ "\n!!!NEWCONTEXT!!!" ++ drop (i + length incMarker + length lname + 1) t


findSubstring :: Eq a => [a] -> [a] -> Maybe Int
findSubstring pat str = findIndex (isPrefixOf pat) (tails str) 


strPrefix :: String -> String
strPrefix [] = []
strPrefix (x:xs) | x `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'])  = x : strPrefix xs -- TODO match all possible variables!!!
                 | otherwise  = [] 
