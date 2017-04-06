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
     derivation <- (direct goal) <|> (contradiction goal)
     return $ (Statement id goal (BySequence derivation))


-- PROOFS unfoldS

direct :: Formula -> ParsecT String ParserState Identity [Statement]
direct goal = 
  do reserved "Proof:"
     derivation <- derive goal
     reserved "qed."
     return derivation

contradiction :: Formula -> ParsecT String ParserState Identity [Statement]
contradiction goal = 
  do reserved "Proof by contradiction:"
     derivation <- derive ((Not goal) `Impl` Bot)
     reserved "qed."
     return derivation


derive :: Formula -> ParsecT String ParserState Identity [Statement]
derive goal = try (unfold goal) <|> try (enfold goal) <|> try (finalGoal goal)

-- derive over conjecture structure

unfold :: Formula -> ParsecT String ParserState Identity [Statement]
unfold (Forall v f) = 
  do reserved "Let"
     var <- many alphaNum
     spaces
     reserved "be arbitrary."
     trace ("unfold forall to " ++ show f) try spaces
     updateState $ addFixedVar var
     lId <- newId
     derivation <- derive $ replaceVar f v var
     return derivation

unfold (Exists v f) = 
  do reserved "Take"
     var <- many alphaNum
     reserved "."
     trace ("unfold exists to " ++ show f) try spaces
     lId <- newId
     derivation <- derive f
     return derivation

unfold (Impl l r) =
  do reserved "Assume"
     l' <- fof
     reserved "."
     trace ("unfold implies " ++ show l) try spaces 
     derivation <- derive r
     reserved "Hence"
     r' <- fof
     reserved "."
     lId <- newId
     rId <- newId
     -- TODO check if l (r) equivalent to l' (r')
     return $ (Statement lId l Assumed) : derivation ++ [(Statement rId r ByContext)]

unfold (Not (Impl l r)) = unfold (And l (Not r))
unfold (Not (Forall v f)) = unfold (Exists v (Not f))
unfold (Not (Exists v f)) = unfold (Forall v (Not f))

unfold _ = fail "Formula cannot be unfold anymore"


-- something else is proved

enfold :: Formula -> ParsecT String ParserState Identity [Statement]
enfold oldGoal = 
  do newGoal <- lookAhead enfoldGoal
     derivation <- derive newGoal
     id <- newId
     trace ("Found enfold " ++ show newGoal) return [Statement id newGoal $ BySequence derivation]

enfoldGoal = try enfoldImplies <|> try enfoldForall

enfoldImplies =
  do reserved "Assume"
     l <- fof
     reserved "."
     trace ("Found left impl: " ++ show l) try spaces
     _ <- finalGoal Top -- TODO Allow nested hence also in proof construction
     reserved "Hence"
     r <- fof
     reserved "."
     trace ("Found implies creation " ++ show l ++ " impl " ++ show r) try spaces
     return (Impl l r)

enfoldForall =
  do reserved "Let"
     var <- many alphaNum
     spaces
     reserved "be arbitrary."
     trace ("Found forall creation " ++ var) $ try spaces
     f <- enfoldGoal
     return (Forall var f)


-- otherwise this should be proved 

finalGoal goal =
  do derivation <- many statement
     trace ("final goal " ++ show goal) return derivation


-- STATEMENTS 

--statement :: ParsecT String u Identity Statement
statement = then' <|> take' <|> fail "no derivation statement"


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
     vars <- var `sepBy` char ','
     spaces
     reserved "such that"
     f <- fof
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     proofId <- newId
     case by of
        Nothing  -> return (Statement id f (BySequence [
                      (Statement proofId (enfoldExists vars f) ByContext)
                    ]))
        Just ids -> return (Statement id f (BySequence [
                      (Statement proofId (enfoldExists vars f) $ BySubcontext ids)
                    ]))

enfoldExists :: [Term] -> Formula -> Formula
enfoldExists [] f = f
enfoldExists ((Var v):vs) f = Exists v (enfoldExists vs f)

subContext = 
  do reserved "by"
     id <- many alphaNum -- TODO intersperced id's
     return [id]

-- We have different precedences
fof = level1 `chainl1` (try iff)
level1 = (forall <|> exists  <|> level2) `chainl1` (try implies)
level2 = level3 `chainl1` (try and')
level3 = (try is <|> try atom <|> try not' <|> try bot <|> parentheses) `chainl1` (try or')

-- FORMULA
--parentheses :: Parser Parentheses
parentheses = do
    spaces
    reservedOp "("
    spaces
    f <- fof
    spaces
    reserved ")"
    spaces
    return f

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
     reserved "and"
     spaces
     return And

--or' :: Parser (Formula -> Formula -> Formula)
or' =
  do spaces
     reserved "or"
     spaces
     return And

--not' :: Parser Formula
not' = 
  do reserved "not"
     f <- fof
     return (Not f)

bot = 
  do reserved "contradiction"
     return Bot

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

term :: ParsecT String ParserState Identity Term
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