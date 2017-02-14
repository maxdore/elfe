module Parser where

import System.IO
import Control.Monad
import Text.Parsec.Prim (ParsecT)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Functor.Identity (Identity)
import Debug.Trace

import Language

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum <|> oneOf "_'"
           , Token.caseSensitive   = True
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer 
reserved   = Token.reserved   lexer 
--parens     = Token.parens     lexer 
whiteSpace = Token.whiteSpace lexer 
semiSep    = Token.semiSep    lexer
reservedOp = Token.reservedOp lexer


data ParserState = ParserState {
    predicates :: [String] 
}
initParseState = ParserState []

--main :: IO()
--main = do
--  problem <- getContents
--  print $ parseString problem 


parseString :: IO String -> [Statement]
parseString s = do
  str <- s
  case runParser sections initParseState "" str of
    Left e  -> error $ show e
    Right r -> (r)


-- SECTIONS

--sections :: ParsecT ParserState u Identity [Statement]
sections = many1 $   definitionSection
                 <|> lemmaSection
                 -- <|> notionSection

--definitionSection :: Parser Statement
definitionSection =
  do reserved "Definition:"
     st  <- statement Assumed
     return (Statement "ID" (getFormula st) Assumed)

lemmaSection =
  do reserved "Lemma:"
     conj  <- statement Assumed
     reserved "Proof."
     derivation <- proofByTactic $ getFormula conj
     reserved "qed."
     return $ (Statement "ID" (getFormula conj) (BySequence derivation))

--notionSection :: Parser Statement
--notionSection =
--  do reserved "Notion:"
--     notion  <- many alphaNum
--     return (Statement notion (Atom "asd" []) Assumed)


-- PROOFS

proofByTactic :: Formula -> ParsecT [Char] u Identity [Statement]
proofByTactic (Impl l r) = do
  derivation <- many $ statement ByContext
  return ([(Statement "ID" l Assumed)] ++ derivation ++ [(Statement "ID" r ByContext)])


-- SENTENCES 

statement :: Proof -> ParsecT [Char] u Identity Statement
statement pr =
  do f <- subSentence
     reserved "."
     return $ (Statement "ID" f pr) 

-- We have different precedences
subSentence = level1 `chainl1` (try iff)
level1 = (forall <|> exists <|> try then' <|> level2) `chainl1` (try implies)
level2 = (try is <|> try take' <|> try atom) `chainl1` (try andE)

-- FORMULA

--iff :: Parser (Formula -> Formula -> Formula)
iff =
  do spaces
     reservedOp "iff"
     spaces
     return Iff

--forall :: Parser Formula
forall =
  do reserved "for all"
     spaces
     var <- many alphaNum
     spaces
     reserved ":"
     sent <- subSentence
     return (Forall var sent)

--exists :: Parser Formula
exists =
  do reserved "exists"
     spaces
     var <- many alphaNum
     spaces
     reserved ":"
     sent <- subSentence
     return (Exists var sent)

--exists :: Parser Formula
then' =
  do reserved "Then"
     spaces
     sent <- subSentence
     return (sent)

--implies :: Parser (Formula -> Formula -> Formula)
implies =
  do spaces
     reservedOp "implies"
     spaces
     return Impl

--and' :: Parser (Formula -> Formula -> Formula)
andE =
  do spaces
     reservedOp "and"
     spaces
     return And

--is :: Parser Formula
is = 
  do name <- many alphaNum
     spaces
     reserved "is"
     predicate <- many alphaNum
     return (Atom predicate [Var name])

take' = 
  do reserved "Take"
     var <- many alphaNum
     spaces
     reserved "such that"
     atom <- atom
     return (Exists var atom)

--atom :: Parser Formula
atom =
  do predicate <- many alphaNum 
     reservedOp "("
     terms <- sepBy (term) (char ',')
     reserved ")"
     return (Atom predicate terms)

--term :: Parser Term
term = 
  do term <- many1 alphaNum
     return (Var term)