{-# LANGUAGE OverloadedStrings #-}
 
import Network.Wai
import Network.Wai.Handler.Warp
import Network.HTTP.Types (status200)
import Blaze.ByteString.Builder (copyByteString)
import qualified Data.ByteString.UTF8 as BU
import Data.Monoid
 
main = do
    let port = 8000
    putStrLn $ "Listening on port " ++ show port
    run port app
 
app req respond = respond $
    case pathInfo req of
        ["wotttt"] -> wotttt
        x -> index x
 
wotttt = responseBuilder status200 [ ("Content-Type", "text/plain") ] $ mconcat $ map copyByteString
    [ "wotttt" ]
 
index x = responseBuilder status200 [("Content-Type", "text/html")] $ mconcat $ map copyByteString
    [ "<p>Hello from ", BU.fromString $ show x, "!</p>"
    , "<p><a href='/wotttt'>wotttt</a></p>\n" ]
