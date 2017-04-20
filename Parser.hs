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
     name <- eid
     reserved ":"
     sugar <- manyTill anyChar $ char '.'
     spaces
     updateState $ addSugar (name, insertPlaceholders $ map unpack $ split (`elem` (['a'..'z'] ++ ['A'..'Z'])) $ pack sugar)
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
     try (string "be an") <|> try (string "be a") <|> try (string "be")
     try spaces
     name <- eid
     updateState $ addLets name vars


definition :: PS [Statement]
definition =
  do reserved "Definition"
     id <- givenOrNewId
     f  <- fof
     cf <- letify f
     reserved "."
     return [(Statement id cf Assumed)]

proposition :: PS [Statement]
proposition = 
  do reserved "Proposition"
     id <- givenOrNewId
     f <- fof
     cf <- letify f
     reserved "."
     return [(Statement id cf Assumed)]

lemma :: PS [Statement]
lemma =
  do reserved "Lemma:"
     goal  <- fof
     id <- newId
     -- let managment
     cgoal <- letify goal
     lets <- lets <$> getState
     let bvs = map show $ concat $ map getVarsOfFormula lets
     assumeId <- newId
     let assumeLets = Statement assumeId (bindVars (formulas2Conj lets) bvs) Assumed
     -- end
     reserved "."
     derivation <- (direct goal bvs) <|> (contradiction goal bvs)
     return [(Statement id cgoal (BySequence (assumeLets:derivation)))]


-- PROOFS

direct :: Formula -> [String] -> PS [Statement]
direct goal bvs = 
  do reserved "Proof:"
     derivation <- derive (bindVars goal bvs) bvs
     qed
     return derivation

contradiction :: Formula -> [String] -> PS [Statement]
contradiction goal bvs = 
  do reserved "Proof by contradiction:"
     derivation <- derive ((Not goal) `Impl` Bot) []
     qed
     return derivation

qed = string "qed" <|> string "∎"
 

derive :: Formula -> [String] -> PS [Statement]
derive goal bvs =     try (trivial goal bvs) 
                  <|> try (splitGoal goal bvs)
                  <|> try (unfold goal bvs) 
                  <|> try (enfold goal bvs) 
                  <|> try (finalGoal goal bvs)

-- split

subProof :: [String] -> PS Statement
subProof bvs =
  do reserved "Proof that"
     goal <- fof
     reserved ":"
     derivation <- derive goal bvs
     id <- newId
     return $ Statement id (bindVars goal bvs) (BySequence derivation)

splitGoal :: Formula -> [String] -> PS [Statement]
splitGoal goal bvs = 
  do id <- newId
     soundnessId <- newId
     subProofs <- many1 $ subProof bvs
     let soundnessF = stat2Conj subProofs `Impl` goal
     let soundness = Statement soundnessId (bindVars soundnessF bvs) ByContext
     return [(Statement id goal (BySplit (soundness:subProofs)))]


-- trivial throws at ATP
trivial :: Formula -> [String] -> PS [Statement]
trivial goal bvs =
  do reserved "Obvious."
     id <- newId
     return [(Statement id (bindVars goal bvs) ByContext)]


-- unfold the goal formula

unfold :: Formula -> [String] -> PS [Statement]
unfold (Forall v f) bvs = 
  do reserved "Let"
     var <- many alphaNum
     spaces
     reserved "be arbitrary."
     trace ("unfold forall to " ++ show f) try spaces
     updateState $ addFixedVar var
     lId <- newId
     derivation <- derive (replaceVar f v var) bvs
     return derivation

unfold (Exists v f) bvs = 
  do reserved "Take"
     var <- many alphaNum
     reserved "."
     trace ("unfold exists to " ++ show f) try spaces
     lId <- newId
     derivation <- derive f bvs
     return derivation

unfold (Impl l r) bvs =
  do reserved "Assume"
     l' <- fof
     if l /= (bindVars l' bvs)
      then trace ("Assume did not work out, expected " ++ show l ++ ", got " ++ show l') fail "narp"
      else do
       reserved "."
       trace ("unfold implies " ++ show l) try spaces 
       derivation <- derive r bvs
       reserved "Hence"
       r' <- fof
       reserved "."
       lId <- newId
       rId <- newId
       return $ (Statement lId (bindVars l bvs) Assumed) : derivation ++ [(Statement rId (bindVars r bvs) ByContext)]

unfold (Not (Impl l r)) bvs = unfold (And l (Not r)) bvs
unfold (Not (Forall v f)) bvs = unfold (Exists v (Not f)) bvs
unfold (Not (Exists v f)) bvs = unfold (Forall v (Not f)) bvs

unfold _ _ = fail "Formula cannot be unfold anymore"


-- something else is proved

enfold :: Formula -> [String] -> PS [Statement]
enfold oldGoal bvs = 
  do newGoal <- lookAhead $ enfoldGoal bvs
     let newVars =  nub (getVarsOfFormula newGoal) \\ strings2Vars bvs
     derivation <- derive newGoal (bvs ++ (vars2Strings newVars))
     oldId <- newId
     soundnessId <- newId
     newId <- newId
     trace ("Found enfold " ++ show newGoal ++ " | " ++ (show $ newVars)) return [Statement oldId (bindVars oldGoal bvs) $ 
          BySplit [
            (Statement soundnessId (bindVars (universallyQuantify newVars newGoal `Impl` oldGoal) bvs) ByContext),
            (Statement newId (bindVars newGoal (bvs++(vars2Strings newVars))) $ BySequence derivation)
          ]
        ]

enfoldGoal bvs = try (enfoldImplies bvs) <|> try (enfoldForall bvs)

enfoldImplies bvs =
  do reserved "Assume"
     l <- fof
     reserved "."
     trace ("Found left impl: " ++ show l) try spaces
     _ <- finalGoal Top bvs -- TODO Allow nested hence also in proof construction
     reserved "Hence"
     r <- fof
     reserved "."
     trace ("Found implies creation " ++ show l ++ " impl " ++ show r) try spaces
     return (Impl l r)

enfoldForall bvs =
  do reserved "Let"
     var <- many alphaNum
     spaces
     reserved "be arbitrary."
     trace ("Found forall creation " ++ var) $ try spaces
     f <- enfoldGoal bvs
     return (Forall var f)


-- the final goal is derived with a sequence

finalGoal goal bvs =
  do derivation <- many $ statement bvs
     trace ("final goal " ++ show goal) return derivation


-- STATEMENTS 

statement :: [String] -> PS Statement
statement bvs = then' bvs <|> take' bvs <|> fail "no derivation statement"


-- STATEMENT MARKERS

then' :: [String] -> PS Statement
then' bvs =
  do reserved "Then"
     spaces
     f <- fof
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     case by of
        Nothing -> return $ Statement id (bindVars f bvs) ByContext 
        Just ids -> return $ Statement id (bindVars f bvs) $ BySubcontext ids

take' :: [String] -> PS Statement
take' bvs = 
  do reserved "Take"
     vars <- var `sepBy` char ',' -- TODO bind them to bvs as well (only in conjecture, not in proof)
     spaces
     reserved "such that"
     f <- fof
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     proofId <- newId
     case by of
        Nothing  -> return (Statement id (bindVars f bvs) (BySequence [
                      (Statement proofId (enfoldExists vars (bindVars f bvs)) ByContext)
                    ]))
        Just ids -> return (Statement id (bindVars f bvs) (BySequence [
                      (Statement proofId (enfoldExists vars (bindVars f bvs)) $ BySubcontext ids)
                    ]))


-- TODO join with universallyQuantify
enfoldExists :: [Term] -> Formula -> Formula
enfoldExists [] f = f
enfoldExists ((Var v):vs) f = Exists v (enfoldExists vs f)

subContext = 
  do reserved "by"
     id <- many alphaNum -- TODO intersperced id's
     return [id]


-- FORMULA

letify :: Formula -> PS Formula
letify f = 
  do lets <- lets <$> getState
     return $ cleanFormula $ insertLets f lets

bindVars :: Formula -> [String] -> Formula
bindVars f [] = f
bindVars f (v:vs) = bindVars (replaceVar f v (boundPrefix++v)) vs

-- We have different precedences
fof = level1 `chainl1` (try iff)
level1 = (forall <|> exists  <|> level2) `chainl1` (try implies)
level2 = level3 `chainl1` (try and')
level3 = (try parentheses <|> try not' <|> try atom <|> try bot) `chainl1` (try or')

parentheses :: PS Formula
parentheses = do
    spaces
    reservedOp "("
    spaces
    f <- fof
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
     f <- fof
     return (Forall var f)

a = 
  do atom <- atom
     spaces
     reserved "."
     f <- fof
     return $ universallyQuantify (getVarsOfFormula atom) (atom `Impl` f) 


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
     sent <- fof
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
     return Or

not' :: PS Formula
not' = 
  do reserved "not"
     f <- fof
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

