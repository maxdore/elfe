module Parser where

import System.IO
import Control.Monad
import Data.List
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



parseString :: String -> IO [Statement]
parseString str = do 
    case runParser sections initParseState "" str of
      Left e  -> return $ error $ show e
      Right r -> return r

-- PARSER STATE

data ParserState = ParserState { counter :: Int
                               , namedIds :: [String]
                               , fixedVars :: [String]
                               }
instance Show ParserState where
  show (ParserState c n f) =    "Counter: " ++ show c ++ "\n" 
                               ++ "Named IDs: " ++ intercalate "," n ++ "\n"  
                               ++ "Fixed Vars: " ++ intercalate "," f ++ "\n"  

initParseState                            = ParserState 0 [] []
incCounter    (ParserState c nis fvs) = ParserState (c+1) nis fvs
addNamedId n  (ParserState c nis fvs) = ParserState c (nis ++ [n]) fvs
addFixedVar v (ParserState c nis fvs) = ParserState c nis (fvs ++ [v])


-- ID MANAGMENT

givenOrNewId = undefId <|> defId

undefId = 
  do reserved ":"
     id <- newId
     return id

defId = 
  do id <- many1 alphaNum
     updateState $ addNamedId id
     reserved ":"
     return $ idPrefix ++ id

newId :: ParsecT String ParserState Identity String
newId = do 
  cur <- counter <$> getState
  updateState incCounter
  return $ idPrefix ++ show cur

-- SECTIONS

sections :: ParsecT String ParserState Identity [Statement]
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
     goal  <- fof
     reserved "."
     id <- newId
     derivation <- ((direct goal)) -- <|> (contradiction goal))
     return $ (Statement id goal (BySequence derivation))


-- PROOFS TACTICS

direct :: Formula -> ParsecT String ParserState Identity [Statement]
direct goal = 
  do reserved "Proof."
     derivation <- unfold goal
     reserved "qed."
     return derivation

--contradiction goal = 
--  do reserved "Proof by contradiction."
--     assId <- newId
--     derivation <- many statement
--     botId <- newId
--     reserved "Contradiction."
--     reserved "qed."
--     return ([(Statement assId (Not goal) Assumed)] ++ derivation ++ [(Statement botId Bot ByContext)])


unfold goal = try (tactic goal) <|> (finalGoal goal)

-- unfold common proofs

tactic (Forall v f) = 
  do reserved "Let"
     var <- many alphaNum
     updateState $ addFixedVar var
     spaces
     reserved "be arbitrary."
     lId <- newId
     derivation <- unfold $ replaceVar f v var
     trace ("unfolded forall to " ++ show f) return derivation

tactic (Impl l r) =
  do reserved "Let"
     lId <- newId
     derivation <- unfold r
     rId <- newId
     trace ("unfolded implies to " ++ show r) return $ (Statement lId l Assumed) : derivation ++ [(Statement rId r ByContext)]

tactic _ = fail "Formula cannot be unfolded anymore"


-- otherwise this should be proved 

finalGoal goal =
  do derivation <- many statement
     trace ("final goal " ++ show goal) return derivation


-- STATEMENTS 

--statement :: ParsecT String u Identity Statement
statement = then' <|> take'


-- STATEMENT MARKERS

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

-- We have different precedences
fof = level1 `chainl1` (try iff)
level1 = (forall <|> exists <|> level2) `chainl1` (try implies)
level2 = (try is <|> try atom <|> try not') `chainl1` (try andE)

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
andE =
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