{-# LANGUAGE OverloadedStrings, DeriveGeneric #-}
import Network.HTTP.Types
import Web.Scotty
import qualified Data.Text as T
import Data.Monoid (mconcat)
import Data.Aeson (object, (.=), ToJSON, toJSON)
import Control.Monad.Trans (lift)
import Control.Monad (liftM)
import Network.Wai.Middleware.Static
import Text.ParserCombinators.Parsec.Prim (runParser)
import Text.ParserCombinators.Parsec.Error
import GHC.Generics (Generic)

import Language
import Parser
import Prover
import Sequences

data ProblemStatus = NotParsed ParseError | Verified ProofStatus
  deriving (Show, Generic)

instance ToJSON ProofStatus
instance ToJSON ProblemStatus
instance ToJSON ParseError where
    toJSON e = toJSON $ show e

main = scotty 8000 $ do
  middleware $ staticPolicy (noDots >-> addBase "web")
  get "/api" $ do 
    input <- param "problem"
    status <- lift $ case (runParser sections initParseState "" input) of
        Left e  -> return $ NotParsed e
        Right r -> do
            res <- verify r
            return $ Verified res
    json status

  get "/" $ file "./web/index.html" 
