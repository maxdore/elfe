module Parser where

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Language

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.reservedNames   = [ "Definition"
                                     , "Proposition"
                                     , "Lemma"
                                     , "Proof"
                                     , "qed"
                                     , "Let"
                                     , "be"
                                     , "iff"
                                     ]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer 
reserved   = Token.reserved   lexer 
parens     = Token.parens     lexer 
whiteSpace = Token.whiteSpace lexer 


data EParser a = EParser { parser :: Parser a
                         , predicates :: [String] 
                         }

elfeParser :: Parser [ESection]
elfeParser = whiteSpace >> eText

eText :: Parser [ESection]
eText = parserLoop

parserLoop :: Parser [ESection]
parserLoop = many $   definitionSection
                         <|> lemmaSection

definitionSection :: Parser ESection
definitionSection =
  do reserved "Definition."
     sent  <- sentence
     return $ EDefinition sent

lemmaSection :: Parser ESection
lemmaSection =
  do reserved "Lemma."
     sent  <- sentence
     reserved "Proof."
     proof <- many sentence
     reserved "qed."
     return $ ELemma sent proof
 

-- Sentence parsing

sentence :: Parser ESent
sentence =
  do sent <- subSentence
     reserved "."
     return sent 

subSentence :: Parser ESent
subSentence =   letSentence
            <|> iffSentence
            <|> implSentence
            <|> forallSentence
            <|> isSentence

letSentence :: Parser ESent
letSentence =
  do reserved "Let"
     var  <- many alphaNum
     reserved " be"
     predicate <- many alphaNum
     return $ EAssignProp (EVar var) (EProp predicate)

iffSentence :: Parser ESent
iffSentence =
  do reserved "Iff:"
     first <- subSentence
     reserved " <=>"
     second <- subSentence
     return $ EIff first second

implSentence :: Parser ESent
implSentence =
  do reserved "Impl:"
     first <- subSentence
     reserved " =>"
     second <- subSentence
     return $ EImpl first second

forallSentence :: Parser ESent
forallSentence =
  do reserved "for all"
     var <- many alphaNum
     reserved " :"
     sent <- subSentence
     return $ EForall (EVar var) sent

isSentence :: Parser ESent
isSentence =
  do var  <- many alphaNum
     reserved " is"
     predicate <- many alphaNum
     return $ EAssignProp (EVar var) (EProp predicate)

-- Main logic

parseString :: String -> EText
parseString str =
  case parse elfeParser "" str of
    Left e  -> error $ show e
    Right r -> (EText r)

main :: IO()
main = do
  problem <- getContents
  print $ parseString problem 