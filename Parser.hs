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
sections = many1 $   definition
                 <|> proposition
                 <|> lemma
                 -- <|> notionSection

--definitionSection :: Parser Statement
definition =
  do reserved "Definition"
     id <- givenOrNewId
     f  <- fof
     reserved "."
     return (Statement id f Assumed)

proposition = 
  do reserved "Proposition"
     id <- givenOrNewId
     f <- fof
     reserved "."
     return (Statement id f ByContext)

lemma =
  do reserved "Lemma:"
     conj  <- fof
     reserved "."
     id <- newId
     derivation <- ((direct conj) <|> (contradiction conj))
     return $ (Statement id conj (BySequence derivation))


-- PROOFS TACTICS

direct conj = 
  do reserved "Proof."
     sts <- unfoldConj conj
     reserved "qed."
     return sts

unfoldConj (Impl premise r) = 
  do pId <- newId
     cId <- newId
     conclusion <- unfoldConj r
     return $ (Statement pId premise Assumed) : conclusion

unfoldConj (Forall v f) = 
  do premise <- let'
     derivation <- many statement
     conclusion <- -- TODO f WITH FIXED VAR
     return (Statement pId premise)


contradiction conj = 
  do reserved "Proof by contradiction."
     assId <- newId
     derivation <- many statement
     botId <- newId
     reserved "Contradiction."
     reserved "qed."
     return ([(Statement assId (Not conj) Assumed)] ++ derivation ++ [(Statement botId Bot ByContext)])


-- STATEMENTS 

--statement :: ParsecT String u Identity Statement
statement = then' <|> take' <|> assume

-- UNPROVEN STATEMENT MARKERS

let' =
  do reserved "Let"
     spaces
     f <- fof -- TODO ONLY ALLOW FORALL SELECTION
     reserved "."
     id <- newId
     return $ Statement id f Assumed

-- PROVEN STATEMENT MARKERS

--exists :: Parser Formula
then' =
  do reserved "Then"
     spaces
     f <- fof
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     case by of
        Nothing -> return $ Statement id f ByContext 
        Just ids -> return $ Statement id f $ BySubcontext ids
take' = 
  do reserved "Take"
     var <- many alphaNum
     spaces
     reserved "such that"
     f <- fof
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     proofId <- newId
     case by of
        Nothing  -> return (Statement id f (BySequence [
                      (Statement proofId (Exists var (f)) ByContext)
                    ]))
        Just ids -> return (Statement id f (BySequence [
                      (Statement proofId (Exists var (f)) $ BySubcontext ids)
                    ]))

subContext = 
  do reserved "by"
     id <- many alphaNum -- TODO intersperced id's
     return [id]


-- FORMULAS

-- We have different precedences
fof = level1 `chainl1` (try iff)
level1 = (forall <|> exists <|> level2) `chainl1` (try implies)
level2 = (try is <|> try atom <|> try not') `chainl1` (try and')


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
     reserved "."
     sent <- fof
     return (Forall var sent)

--exists :: Parser Formula
exists =
  do reserved "exists"
     spaces
     var <- many alphaNum
     spaces
     reserved "."
     sent <- fof
     return (Exists var sent)

--implies :: Parser (Formula -> Formula -> Formula)
implies =
  do spaces
     reservedOp "implies"
     spaces
     return Impl

--and' :: Parser (Formula -> Formula -> Formula)
and' =
  do spaces
     reservedOp "and"
     spaces
     return And

--not' :: Parser Formula
not' = 
  do reserved "not"
     f <- fof
     return (Not f)

--is :: Parser Formula
is = 
  do name <- many alphaNum
     spaces
     reserved "is"
     predicate <- many alphaNum
     return (Atom predicate [Var name])

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