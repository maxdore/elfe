{-# LANGUAGE OverloadedStrings #-}

import Network.HTTP.Types
import Web.Scotty
import Text.Hastache 
import Text.Hastache.Context
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import Data.Text.Lazy.Encoding

import Data.Data
import Data.Aeson (ToJSON, toJSON)
import Data.Monoid
import Control.Monad.Trans (lift)
import Control.Monad.IO.Class (liftIO)
import Network.Wai.Middleware.Static
import Text.ParserCombinators.Parsec.Prim (runParser)
import Text.ParserCombinators.Parsec.Error
import GHC.Generics (Generic)
import Control.Exception (catch)
import System.Directory
import Data.Time.Clock (getCurrentTime)

import Settings (port)
import Elfe

data ProblemStatus = NotParsed ParseError | Verified [StatementStatus]
  deriving (Show, Generic)

instance ToJSON Term where
  toJSON t = toJSON $ show t
instance ToJSON Formula where
  toJSON f = toJSON $ show f
instance ToJSON ProverInfo
instance ToJSON Position
instance ToJSON ProofStatus
instance ToJSON StatementStatus
instance ToJSON ProblemStatus
instance ToJSON ParseError where
    toJSON e = toJSON $ show e


data TemplateCtx = TemplateCtx
  { body :: TL.Text
  , title :: TL.Text
  } deriving (Data, Typeable)

data Example = Example { name :: String, content :: String } deriving (Data, Typeable)
data Examples = Examples { examples :: [Example] } deriving (Data, Typeable)


--let ctx = TemplateCtx { body = "Hello", title = "Haskell" }
--output <- template "templates/home.html" (mkGenericContext ctx)

main = scotty port $ do
  middleware $ staticPolicy (noDots >-> addBase "web")
  get "/api" $ do 
    raw <- param "problem"
    let included = includeLibraries raw
    status <- lift $ case (runParser elfeParser initParseState "" included) of
        Left e  -> return $ NotParsed e
        Right r -> do
            res <- verify r
            return $ Verified res
    time <- lift getCurrentTime
    lift $ appendFile "./web/logs/problems" (show time ++ "\n" ++ show status ++ "\nINPUT\n" ++ raw ++ "\n\n")
    json status

  get "/examples" $ do 
    dircontent <- liftIO $ getDirectoryContents "./examples"
    let examples = map (reverse . drop 5 . reverse ) (filter (\x -> x `notElem` [".", ".."]) dircontent)
    content <- hastacheFile defaultConfig "./web/templates/examples.html" (mkGenericContext $ Examples $ map (\e -> Example e "content") examples)
    compiled <- compile content
    html (decodeLatin1 compiled)

  get "/tutorial" $ do
    redirect "/training?exercise=0"

  get "/training" $ do
    exercise <- (param "exercise")
    header <- hastacheFile defaultConfig "./web/templates/training/header.html" (mkGenericContext ())
    content <- hastacheFile defaultConfig ("./web/templates/training/" ++ (TL.unpack exercise) ++ ".html") (mkGenericContext ())
    footer <- hastacheFile defaultConfig "./web/templates/footer.html" (mkGenericContext ())
    html $ (decodeLatin1 header) <> (decodeLatin1 content) <> (decodeLatin1 footer)
 
  get "/" $ do
    example <- (param "example") `rescue` (\msg -> return msg)
    let filePath = "./examples/" ++ filter (\x -> x `notElem` ['/']) (TL.unpack example) ++ ".elfe"
    exampleExists <- liftIO $ doesFileExist filePath
    if exampleExists
      then do
        content <- liftIO $ readFile filePath
        content <- hastacheFile defaultConfig "./web/templates/index.html" (mkGenericContext $ Example (show example) content)
        compiled <- compile content
        html (decodeLatin1 compiled)
      else do
        content <- liftIO $ readFile "./examples/Symmetric and transitive relations are reflexive.elfe"
        content <- hastacheFile defaultConfig "./web/templates/index.html" (mkGenericContext $ Example (show example) content)
        compiled <- compile content
        html (decodeLatin1 compiled)

compile template = do
  header <- hastacheFile defaultConfig "./web/templates/header.html" (mkGenericContext ())
  footer <- hastacheFile defaultConfig "./web/templates/footer.html" (mkGenericContext ()) 
  return $ header <> template <> footer

  
