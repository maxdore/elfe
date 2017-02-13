module Parser where

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Debug.Trace

import Language

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum <|> oneOf "_'"
           --, Token.reservedNames   = [ "Definition"
           --                          , "Proposition"
           --                          , "Lemma"
           --                          , "Proof"
           --                          , "qed"
           --                          , "Let"
           --                          , "be"
           --                          ]
           --, Token.reservedOpNames = [ " iff"
           --                          , "iff"
           --                          ]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer 
reserved   = Token.reserved   lexer 
parens     = Token.parens     lexer 
whiteSpace = Token.whiteSpace lexer 
semiSep    = Token.semiSep    lexer
reservedOp = Token.reservedOp lexer


data ParseContext = ParseContext { 
    predicates :: [String] 
}


atom :: Parser Formula
atom =
  do name <- many alphaNum
     return (Atom name [])

iff :: Parser (Formula -> Formula -> Formula)
iff =
  do spaces
     reservedOp "iff"
     spaces
     return Iff

implies :: Parser (Formula -> Formula -> Formula)
implies =
  do spaces
     reservedOp "implies"
     spaces
     return Impl

and' :: Parser (Formula -> Formula -> Formula)
and' =
  do spaces
     reservedOp "and"
     spaces
     return And


-- We have different precedences

level0 :: Parser Formula
level0 = atom `chainl1` try and'

level1 :: Parser Formula
level1 = level0 `chainl1` try implies

subSentence :: Parser Formula
subSentence = level1 `chainl1` (try iff)

sentence =
  do sent <- subSentence
     reserved "."
     return sent 

definitionSection :: Parser Statement
definitionSection =
  do reserved "Definition:"
     sent  <- sentence
     return $ (Statement "ID" sent Assumed)


lemmaSection :: Parser Statement
lemmaSection =
  do reserved "Lemma:"
     sent  <- sentence
     return $ (Statement "ID" sent Assumed)




sections :: Parser [Statement]
sections = many $ definitionSection
                <|> lemmaSection




parseString :: String -> [Statement]
parseString str =
  case parse sections "" str of
    Left e  -> error $ show e
    Right r -> (r)

main :: IO()
main = do
  problem <- getContents
  print $ parseString problem 