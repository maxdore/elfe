module Test where
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as P

lexer = haskell
reserved   = P.reserved lexer
reservedOp = P.reservedOp lexer

data Term = Term String
  deriving (Show)

term :: Parser Term
term = try (do { x <- many alphaNum
          ; reservedOp "="
          ; y <- many alphaNum
          ; return (Term (x++y))
          })
        <|> 
          do { reserved "prefix"
          --; _ <- spaces
          ; x <- many alphaNum
          ; return (Term x)
          }

parser = do { e<-term; return e }

