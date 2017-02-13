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


atom :: ParseContext -> Parser Formula
atom pc =
  do name <- many alphaNum
     return (Atom name [])

iff :: ParseContext -> Parser (Formula -> Formula -> Formula)
iff pc =
  do spaces
     reservedOp "iff"
     spaces
     return Iff

implies :: ParseContext -> Parser (Formula -> Formula -> Formula)
implies pc =
  do spaces
     reservedOp "implies"
     spaces
     return Impl

and' :: ParseContext -> Parser (Formula -> Formula -> Formula)
and' pc =
  do spaces
     reservedOp "and"
     spaces
     return And


-- We have different precedences

level0 :: ParseContext -> Parser Formula
level0 = atom pc `chainl1` try (and' pc)

level1 :: ParseContext -> Parser Formula
level1 pc = level0 pc `chainl1` try (implies pc)

subSentence :: ParseContext -> Parser Formula
subSentence pc = level1 pc `chainl1` (try (iff pc))

subSentence :: ParseContext -> Parser Formula
sentence pc =
  do sent <- subSentence pc
     reserved "."
     return sent 

definitionSection :: ParseContext -> Parser Statement
definitionSection pc =
  do reserved "Definition:"
     sent  <- sentence pc
     return $ (Statement "ID" sent Assumed)


lemmaSection :: ParseContext -> Parser Statement
lemmaSection pc =
  do reserved "Lemma:"
     sent  <- sentence pc
     return $ (Statement "ID" sent Assumed)




sections :: ParseContext -> Parser [Statement]
sections pc = many $   definitionSection pc
                   <|> lemmaSection pc




parseString :: String -> [Statement]
parseString str =
  case parse (sections (ParseContext [])) "" str of
    Left e  -> error $ show e
    Right r -> (r)

main :: IO()
main = do
  problem <- getContents
  print $ parseString problem 