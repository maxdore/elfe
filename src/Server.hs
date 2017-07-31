import Network.HTTP.Types
import Web.Scotty
import Data.Aeson (ToJSON, toJSON)
import Control.Monad.Trans (lift)
import Network.Wai.Middleware.Static
import Text.ParserCombinators.Parsec.Prim (runParser)
import Text.ParserCombinators.Parsec.Error
import GHC.Generics (Generic)
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
    json status
 
  get "/" $ file "./web/index.html" 
