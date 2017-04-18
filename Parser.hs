{-# LANGUAGE OverloadedStrings #-}
module Parser where

import System.IO
import Control.Monad
import Data.List
import Data.Text (split, pack, unpack)
import Data.Char (isLetter)

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
    case runParser elfeParser initParseState "" str of
      Left e  -> return $ error $ show e
      Right r -> return r

-- PARSER STATE

data ParserState = ParserState { counter :: Int
                               , namedIds :: [String]
                               , fixedVars :: [String]
                               , sugars :: [(String, [String])]
                               , lets :: [Formula]
                               }
instance Show ParserState where
  show (ParserState c n f s l) =    "Counter: " ++ show c ++ "\n" 
                               ++ "Named IDs: " ++ intercalate "," n ++ "\n"  
                               ++ "Fixed Vars: " ++ intercalate "," f ++ "\n"  

initParseState                              = ParserState 0 [] [] [] []
incCounter    (ParserState c nis fvs ss ls) = ParserState (c+1) nis fvs ss ls
addNamedId n  (ParserState c nis fvs ss ls) = ParserState c (nis ++ [n]) fvs ss ls
addFixedVar v (ParserState c nis fvs ss ls) = ParserState c nis (fvs ++ [v]) ss ls
addSugar s    (ParserState c nis fvs ss ls) = ParserState c nis fvs (ss ++ [s]) ls
addLet l      (ParserState c nis fvs ss ls) = ParserState c nis fvs ss (ls ++ [l])
addLets n vs  (ParserState c nis fvs ss ls) = ParserState c nis fvs ss (ls ++ (map (\v -> Atom n [v]) vs))
clearLets     (ParserState c nis fvs ss ls) = ParserState c nis fvs ss []


type PS = ParsecT String ParserState Identity


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

newId :: PS String
newId = do 
  cur <- counter <$> getState
  updateState incCounter
  return $ idPrefix ++ show cur


elfeParser :: PS [Statement]
elfeParser = do
  secs <- many $   newContext
               <|> notation
               <|> let'
               <|> definition
               <|> proposition
               <|> lemma
  return $ foldr (++) [] secs



newContext = do
  reserved "!!!NEWCONTEXT!!!"
  updateState clearLets
  return [] 


insertPlaceholders :: [String] -> [String]
insertPlaceholders [] = []
insertPlaceholders [x] = [x]
insertPlaceholders (x:y:xs) | x /= "" && y /= "" = x : "" : insertPlaceholders (y : xs)
                            | otherwise          = x : (insertPlaceholders (y:xs))

notation =
  do reserved "Notation"
     id <- givenOrNewId
     sugar <- manyTill anyChar $ char '.'
     spaces
     updateState $ addSugar (id, insertPlaceholders $ map unpack $ split (`elem` (['a'..'z'] ++ ['A'..'Z'])) $ pack sugar)
     return []

let' =
  do reserved "Let"
     spaces
     (try letBe) <|> try letRaw
     reserved "."
     return []

letRaw =
  do f <- atom
     trace ("found let " ++ show f) try spaces
     updateState $ addLet f


letBe =
  do vars <- var `sepBy` char ','
     try spaces
     reserved "be"
     try spaces
     name <- eid
     updateState $ addLets name vars


definition =
  do reserved "Definition"
     id <- givenOrNewId
     f  <- fof
     reserved "."
     return [(Statement id f Assumed)]

proposition = 
  do reserved "Proposition"
     id <- givenOrNewId
     f <- fof
     reserved "."
     return [(Statement id f Assumed)]

lemma =
  do reserved "Lemma:"
     goal  <- fof
     reserved "."
     id <- newId
     derivation <- (direct goal) <|> (contradiction goal)
     return [(Statement id goal (BySequence derivation))]


-- PROOFS

qed = string "qed" <|> string "∎"
 
direct :: Formula -> PS [Statement]
direct goal = 
  do reserved "Proof:"
     derivation <- derive $ unfoldLets goal
     qed
     return derivation

contradiction :: Formula -> PS [Statement]
contradiction goal = 
  do reserved "Proof by contradiction:"
     derivation <- derive $ unfoldLets ((Not goal) `Impl` Bot)
     qed
     return derivation



unfoldLets :: Formula -> Formula
unfoldLets f = f



derive :: Formula -> PS [Statement]
derive goal = try (unfold goal) <|> try (enfold goal) <|> try (finalGoal goal)

-- unfold the goal formula

unfold :: Formula -> PS [Statement]
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
     if l /= l'
      then trace ("Assume did not work out") fail "narp"
      else do
       reserved "."
       trace ("unfold implies " ++ show l) try spaces 
       derivation <- derive r
       reserved "Hence"
       r' <- fof
       reserved "."
       lId <- newId
       rId <- newId
       return $ (Statement lId l Assumed) : derivation ++ [(Statement rId r ByContext)]

unfold (Not (Impl l r)) = unfold (And l (Not r))
unfold (Not (Forall v f)) = unfold (Exists v (Not f))
unfold (Not (Exists v f)) = unfold (Forall v (Not f))

unfold _ = fail "Formula cannot be unfold anymore"


-- something else is proved

enfold :: Formula -> PS [Statement]
enfold oldGoal = 
  do newGoal <- lookAhead enfoldGoal
     derivation <- derive newGoal
     oldId <- newId
     soundnessId <- newId
     newId <- newId
     trace ("Found enfold " ++ show newGoal) return [Statement oldId oldGoal $ 
          BySplit [
            (Statement soundnessId (newGoal `Impl` oldGoal) ByContext),
            (Statement newId newGoal $ BySequence derivation)
          ]
        ]

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


-- the final goal is derived with a sequence

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
     f <- level0
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
     f <- level0
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


-- FORMULA

fof :: PS Formula
fof = 
  do f <- level0
     lets <- lets <$> getState
     let qF = insertLets f lets
     return $ cleanFormula qF

-- We have different precedences
level0 = level1 `chainl1` (try iff)
level1 = (forall <|> exists  <|> level2) `chainl1` (try implies)
level2 = level3 `chainl1` (try and')
level3 = (try parentheses <|> try not' <|> try atom <|> try bot) `chainl1` (try or')

parentheses :: PS Formula
parentheses = do
    spaces
    reservedOp "("
    spaces
    f <- level0
    spaces
    reserved ")"
    spaces
    return f

iff :: PS (Formula -> Formula -> Formula)
iff =
  do spaces
     reservedOp "iff"
     spaces
     return Iff

v = 
  do var <- eid 
     spaces
     reserved "."
     f <- level0
     return (Forall var f)

a = 
  do atom <- atom
     spaces
     reserved "."
     f <- level0
     return $ universallyQuantify (getVarsOfAtom atom) (atom `Impl` f) 


forall :: PS Formula
forall =
  do reserved "for all"
     try v <|> a

exists :: PS Formula
exists =
  do reserved "exists"
     spaces
     var <- many alphaNum
     spaces
     reserved "."
     sent <- level0
     return (Exists var sent)

implies :: PS (Formula -> Formula -> Formula)
implies =
  do spaces
     reservedOp "implies"
     spaces
     return Impl

and' :: PS (Formula -> Formula -> Formula)
and' =
  do spaces
     reserved "and"
     spaces
     return And

or' :: PS (Formula -> Formula -> Formula)
or' =
  do spaces
     reserved "or"
     spaces
     return And

not' :: PS Formula
not' = 
  do reserved "not"
     f <- level0
     return (Not f)

bot = 
  do string "contradiction" <|> string "⊥"
     return Bot

atom :: PS Formula
atom = try is <|> try rawAtom <|> try sugaredAtom

is = 
  do name <- many alphaNum
     spaces
     reserved "is"
     predicate <- many alphaNum
     return (Atom predicate [Var name])

rawAtom =
  do predicate <- many alphaNum 
     reservedOp "("
     terms <- term `sepBy` (char ',')
     reserved ")"
     return (Atom predicate terms)


strPrefix :: String -> String
strPrefix [] = []
strPrefix (x:xs) | x `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'])  = x : strPrefix xs -- TODO match all possible variables!!!
                 | otherwise  = [] 

matches :: [String] -> String -> [Term] -> Maybe [Term]
matches [] [] ts      = Just ts
matches _  [] _       = Nothing
matches [] _  _       = Nothing
matches (c:cs) raw ts | c == ""   = if length (strPrefix raw) > 0
                                      then matches cs (drop (length $ strPrefix raw) raw) ((Var $ strPrefix raw):ts)
                                      else Nothing
                      | otherwise = if c `isPrefixOf` raw 
                                      then matches cs (drop (length c) raw) ts
                                      else Nothing

matchSugars :: [(String, [String])] -> String -> Maybe Formula
matchSugars [] _ = Nothing
matchSugars ((id,s):ss) raw = 
    case matches s raw [] of
      Nothing -> matchSugars ss raw -- trace (show s ++ " not matched")
      Just ts -> Just $ Atom id $ reverse ts
 
ops = (try $ string " implies") <|> (try $ string " and") <|> (try $ string " iff") <|> (try $ string " or") <|> (try $ string "not") <|> (try $ string " contradictioncontradiction") 

sugaredAtom =
  do raw <- lookAhead $ manyTill (try anyChar) $ lookAhead $ (try $ string ".") <|> ops
     ss <- sugars <$> getState
     case matchSugars ss raw of
        Nothing -> trace (raw ++ " not matched") return Bot 
        Just f -> do
          ignore <- manyTill (try anyChar) $ lookAhead $ (try $ string ".") <|> ops
          trace (raw ++ " matched! "++ show f) return f

term :: PS Term
term = (try cons) <|> var 
 
cons =
  do predicate <- many alphaNum 
     reservedOp "("
     terms <- term `sepBy` (char ',')
     reserved ")"
     return (Cons predicate terms)

eid =
  do s <- many1 alphaNum
     return s

var =
  do var <- eid
     return (Var var)

