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
import System.IO.Unsafe
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Functor.Identity (Identity)
import Debug.Trace
import Control.Monad.Trans (lift)

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
                               , sugars :: [[String]]
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


elfeParser = do
  includes <- many include
  secs <- sections
  return $ foldr (++) [] includes ++ secs

include = 
  do reserved "Use"
     name <- many alphaNum
     parsed <- lift $ case runParser elfeParser initParseState "" (unsafePerformIO $ readFile $ "library/" ++ name ++ ".elfe") of
        Left e  -> return $ error $ show e
        Right r -> return r
     reserved "."
     return parsed

sections :: PS [Statement]
sections = do
  secs <- many $   
           notation
       <|> let'
       <|> definition
       <|> proposition
       <|> lemma
  return $ foldr (++) [] secs

notation =
  do reserved "Notation:"
     sugar <- manyTill anyChar $ char '.'
     trace ("found sugar " ++ show (split isLetter $ pack sugar) ) try spaces
     updateState $ addSugar $ map unpack $ split isLetter $ pack sugar
     return []

let' =
  do reserved "Let"
     spaces
     f <- atom
     reserved "."
     updateState $ addLet f
     trace ("found let " ++ show f) try spaces
     return []

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
     return [(Statement id f ByContext)]

lemma =
  do reserved "Lemma:"
     goal  <- fof
     reserved "."
     id <- newId
     derivation <- (direct goal) <|> (contradiction goal)
     return [(Statement id goal (BySequence derivation))]


-- PROOFS unfoldS

direct :: Formula -> PS [Statement]
direct goal = 
  do reserved "Proof:"
     derivation <- derive goal
     reserved "qed."
     return derivation

contradiction :: Formula -> PS [Statement]
contradiction goal = 
  do reserved "Proof by contradiction:"
     derivation <- derive ((Not goal) `Impl` Bot)
     reserved "qed."
     return derivation


derive :: Formula -> PS [Statement]
derive goal = try (unfold goal) <|> try (enfold goal) <|> try (finalGoal goal)

-- derive over conjecture structure

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

fof = 
  do f <- level0
     lets <- lets <$> getState
     let qF = insertLets f lets
     if f == qF
         then return qF
         else do
          trace (show f ++ " EXTENDED TO " ++ (show qF)) try spaces
          return qF

-- We have different precedences
level0 = level1 `chainl1` (try iff)
level1 = (forall <|> exists  <|> level2) `chainl1` (try implies)
level2 = level3 `chainl1` (try and')
level3 = (try atom <|> try not' <|> try bot <|> parentheses) `chainl1` (try or')

--parentheses :: Parser Parentheses
parentheses = do
    spaces
    reservedOp "("
    spaces
    f <- level0
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
     sent <- level0
     return (Forall var sent)

--exists :: Parser Formula
exists =
  do reserved "exists"
     spaces
     var <- many alphaNum
     spaces
     reserved "."
     sent <- level0
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
     f <- level0
     return (Not f)

bot = 
  do reserved "contradiction"
     return Bot

atom :: PS Formula
atom = try sugaredAtom <|> try is <|> try rawAtom 

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
strPrefix (x:xs) | isLetter x = x : strPrefix xs
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

sugar2alpha [] = []
sugar2alpha (s:ss) = show (map fromEnum s) ++ sugar2alpha ss 

matchSugars :: [[String]] -> String -> Maybe Formula
matchSugars [] _ = Nothing
matchSugars (s:ss) raw = 
    case matches s raw [] of
      Nothing -> matchSugars ss raw
      Just ts -> Just $ Atom (sugar2alpha s) ts
 
sugaredAtom =
  do ss <- sugars <$> getState
     raw <- manyTill anyChar $ char '.'
     case matchSugars ss raw of
        Nothing -> trace raw fail "No sugar matched"
        Just f -> do
          trace ("matched! "++ show f) return f 

term :: PS Term
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