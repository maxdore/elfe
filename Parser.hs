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
  emptyDef { Token.commentStart    = "\"\"\""
           , Token.commentEnd      = "\"\"\""
           , Token.commentLine     = "#"
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


data ParserState = ParserState { counter :: Int
                               , namedIds :: [String]
                               }
initParseState = ParserState 0 []
incCounter (ParserState c ns) = ParserState (c+1) ns
addNamedId n (ParserState c ns) = ParserState c (ns ++ [n])

--main :: IO()
--main = do
--  problem <- getContents
--  print $ parseString problem 


parseString :: String -> IO [Statement]
parseString str = do 
    case runParser sections initParseState "" str of
      Left e  -> return $ error $ show e
      Right r -> return r


-- ID MANAGMENT

newId :: ParsecT s ParserState Identity String
newId = do 
  cur <- counter <$> getState
  updateState incCounter
  return $ idPrefix ++ show cur


givenOrNewId = undefId <|> defId

undefId = 
  do reserved ":"
     id <- newId
     return id

defId = 
  do id <- many1 alphaNum
     updateState (addNamedId id)
     reserved ":"
     return $ idPrefix ++ id

-- SECTIONS

--sections :: ParsecT ParserState u Identity [Statement]
sections = many1 $   definitionSection
                 <|> lemmaSection
                 -- <|> notionSection

--definitionSection :: Parser Statement
definitionSection =
  do reserved "Definition"
     id <- givenOrNewId
     st  <- statement Assumed
     return (Statement id (getFormula st) Assumed)

lemmaSection =
  do reserved "Lemma:"
     conj  <- statement Assumed
     id <- newId
     derivation <- ((proofDirect $ getFormula conj) <|> (proofContradiction $ getFormula conj))
     return $ (Statement id (getFormula conj) (BySequence derivation))


-- PROOFS TACTICS

proofDirect (Impl l r) = 
  do reserved "Proof."
     lId <- newId
     derivation <- many $ statement ByContext
     rId <- newId
     reserved "qed."
     return ([(Statement lId l Assumed)] ++ derivation ++ [(Statement rId r ByContext)])

proofContradiction conj = 
  do reserved "Proof by contradiction."
     assId <- newId
     derivation <- many $ statement ByContext
     botId <- newId
     reserved "Contradiction."
     reserved "qed."
     return ([(Statement assId (Not conj) Assumed)] ++ derivation ++ [(Statement botId Bot ByContext)])




-- SENTENCES 

--statement :: Proof -> ParsecT String u Identity Statement
statement pr =
  do f <- subSentence
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     case by of
       Nothing -> return $ Statement id f pr 
       Just ids -> return $ Statement id f $ BySubcontext ids


subContext = 
  do reserved "by"
     id <- many alphaNum
     return [id]


-- We have different precedences
subSentence = level1 `chainl1` (try iff)
level1 = (forall <|> exists <|> try then' <|> level2) `chainl1` (try implies)
level2 = (try is <|> try take' <|> try atom <|> try not') `chainl1` (try andE)

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

--not' :: Parser Formula
not' = 
  do reserved "not"
     f <- subSentence
     return (Not f)

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
     terms <- term `sepBy` (char ',')
     reserved ")"
     return (Atom predicate terms)

--term :: Parser Term
term = (try cons) <|> var 

cons =
  do predicate <- many alphaNum 
     reservedOp "("
     terms <- term `sepBy` (char ',')
     reserved ")"
     return (Cons predicate terms)

var =
  do var <- many1 alphaNum
     return (Var var)