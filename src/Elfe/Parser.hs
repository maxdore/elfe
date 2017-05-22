module Elfe.Parser where

import System.IO
import Control.Monad
import Control.Monad.Trans (lift)
import Data.List
import Data.Text (split, pack, unpack, strip)
import Data.Char (isLetter, isSpace)

import Text.Parsec.Prim (ParsecT)
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import Text.Parsec.Pos (SourcePos)
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Functor.Identity (Identity)

import Debug.Trace

import Elfe.Language

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
    let state = runParser elfeParser initParseState "" str
    case state of
      Left e  -> return $ error $ show e
      Right r -> return r

-- PARSER HELPERS

seeNext :: Int -> ParsecT String u Identity ()
seeNext n = do
  s <- getParserState
  let out = take n (stateInput s)
  traceShowM out

getPos = do
  pos <- getPosition
  let line = sourceLine pos
  let col = sourceColumn pos
  return $ Position (line,col)


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

initParseState                              = ParserState 0 [] [] [("equal",["", " = ", ""])] []
incCounter    (ParserState c nis fvs ss ls) = ParserState (c+1) nis fvs ss ls
addNamedId n  (ParserState c nis fvs ss ls) = ParserState c (nis ++ [n]) fvs ss ls
addFixedVar v (ParserState c nis fvs ss ls) = ParserState c nis (fvs ++ [v]) ss ls
addSugar s    (ParserState c nis fvs ss ls) = ParserState c nis fvs (ss ++ [s]) ls
addLet l      (ParserState c nis fvs ss ls) = ParserState c nis fvs ss (ls ++ [l])
addLets n vs  (ParserState c nis fvs ss ls) = ParserState c nis fvs ss (ls ++ (map (\v -> Atom n [v]) vs))
clearLets     (ParserState c nis fvs ss ls) = ParserState c nis fvs ss []


type PS = ParsecT String ParserState Identity


-- ID MANAGMENT

eid =
  do s <- many1 (satisfy (`elem` ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']) <?> "letter or digit")
     return s

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
  secs <- many1 $   newContext
               <|> notation
               <|> assign
               <|> definition
               <|> lemma
               <|> proposition
               <|> fail "No section could be applied"
  return $ foldr (++) [] secs



newContext = do
  reserved "!!!NEWCONTEXT!!!"
  try spaces
  pos <- getPosition
  setPosition $ setSourceLine pos 3
  updateState clearLets
  return [] 


insertPlaceholders :: [String] -> [String]
insertPlaceholders [] = []
insertPlaceholders [x] = [x]
insertPlaceholders (x:y:xs) | x /= "" && y /= "" = x : "" : insertPlaceholders (y : xs)
                            | otherwise          = x : (insertPlaceholders (y:xs))

-- meta

notation :: PS [Statement]
notation =
  do reserved "Notation"
     name <- eid
     reserved ":"
     sugar <- manyTill anyChar $ char '.'
     spaces
     updateState $ addSugar (name, insertPlaceholders $ map unpack $ split (`elem` (['a'..'z'] ++ ['A'..'Z'])) $ pack sugar)
     return []

assign :: PS [Statement]
assign =
  do reserved "Let"
     spaces
     (try letBe) <|> try letRaw
     reserved "."
     return []

letRaw =
  do f <- atom
     traceM ("found let " ++ show f)
     updateState $ addLet f


letBe =
  do vars <- var `sepBy` char ','
     try spaces
     try (string "be an") <|> try (string "be a") <|> try (string "be")
     try spaces
     name <- eid
     updateState $ addLets name vars


-- sections

definition :: PS [Statement]
definition =
  do reserved "Definition"
     id <- givenOrNewId
     f  <- fof
     cf <- letify f
     reserved "."
     pos <- getPos
     return [(Statement id cf Assumed pos)]

proposition :: PS [Statement]
proposition = 
  do reserved "Proposition"
     id <- givenOrNewId
     f <- fof
     cf <- letify f
     reserved "."
     pos <- getPos
     return [(Statement id cf Assumed pos)]

lemma :: PS [Statement]
lemma =
  do pos <- getPos
     reserved "Lemma"
     id <- givenOrNewId
     goal  <- fof
     reserved "."
     -- let managment
     cgoal <- letify goal
     lets <- lets <$> getState
     let bvs = map show $ concat $ map getVarsOfFormula lets
     assumeId <- newId
     let assumeLets = Statement assumeId (bindVars (formulas2Conj lets) bvs) Assumed None
     -- end
     reserved "Proof:"
     derivation <- derive (bindVars goal bvs) bvs
     qed
     return [(Statement id cgoal (BySequence (assumeLets:derivation)) pos)]


-- derivations
 
derive :: Formula -> [String] -> PS [Statement]
derive goal bvs =     try (splitGoal goal bvs)
                  <|> try (cases goal bvs)
                  <|> try (unfold goal bvs) 
                  <|> try (enfold goal bvs) 
                  <|> try (extendContext goal bvs)
                  <|> finalProof goal bvs

qed = do
  reserved "qed."


finalProof goal bvs = 
  do id <- newId
     return [Statement id (bindVars goal bvs) ByContext None]

-- split

subProof :: [String] -> PS Statement
subProof bvs =
  do pos <- getPos
     reserved "Proof"
     goal <- fof
     traceM ("proof" ++ (show goal)) 
     reserved ":"
     derivation <- derive goal bvs
     qed
     id <- newId
     return $ Statement id (bindVars goal bvs) (BySequence derivation) pos

splitGoal :: Formula -> [String] -> PS [Statement]
splitGoal goal bvs = 
  do id <- newId
     soundnessId <- newId
     subProofs <- many1 $ subProof bvs
     let soundnessF = foldl And (head fs) (tail fs) `Impl` goal
          where fs = map (\(Statement _ f _ _) -> f) subProofs
     let soundness = Statement soundnessId (bindVars soundnessF bvs) ByContext None
     return [(Statement id goal (BySplit (soundness:subProofs)) None)]

-- cases

caseDistinction :: Formula -> [String] -> PS Statement
caseDistinction goal bvs =
  do pos <- getPos
     reserved "Case"
     dist <- fof
     reserved ":"
     derivation <- derive goal bvs
     qed
     id <- newId
     cid <- newId
     gid <- newId
     return $ Statement id (bindVars (dist `Impl` goal) bvs) (BySequence [
        (Statement cid (bindVars dist bvs) Assumed None),
        (Statement gid (bindVars goal bvs) (BySequence derivation) None)
      ]) pos

cases :: Formula -> [String] -> PS [Statement]
cases goal bvs = 
  do id <- newId
     soundnessId <- newId
     cases <- many1 $ caseDistinction goal bvs
     let soundnessF = foldl And (head fs) (tail fs) `Impl` goal
          where fs = map (\(Statement _ f _ _) -> f) cases
     let soundness = Statement soundnessId (bindVars soundnessF bvs) ByContext None
     return [(Statement id goal (BySplit (soundness:cases)) None)]


-- unfold the goal formula

unfold :: Formula -> [String] -> PS [Statement]
unfold (Forall v f) bvs = 
  do reserved "Let"
     var <- many alphaNum
     spaces
     reserved "be arbitrary."
     traceM ("unfold forall to " ++ show f)
     updateState $ addFixedVar var
     lId <- newId
     derivation <- derive (replaceVar f v var) bvs
     return derivation

unfold (Exists v f) bvs = 
  do reserved "Take"
     var <- many alphaNum
     reserved "."
     traceM ("unfold exists to " ++ show f)
     lId <- newId
     derivation <- derive f bvs
     return derivation

unfold (Impl l r) bvs =
  do lPos <- getPos
     reserved "Assume"
     l' <- fof
     if l /= (bindVars l' bvs)
       then trace ("Assume did not work out, expected " ++ show l ++ ", got " ++ show l') fail "narp"
       else do
         reserved "."
         lId <- newId
         traceM ("unfold implies " ++ show l) 
         derivation <- derive r bvs
         rPos <- getPos
         reserved "Hence"
         r' <- fof
         reserved "."
         nId <- newId
         rId <- newId
         return $ (Statement lId (bindVars l bvs) Assumed lPos) : derivation

unfold (Not (Impl l r)) bvs = unfold (And l (Not r)) bvs
unfold (Not (Forall v f)) bvs = unfold (Exists v (Not f)) bvs
unfold (Not (Exists v f)) bvs = unfold (Forall v (Not f)) bvs

unfold _ _ = fail "No proving method given"


-- something else is proved

enfold :: Formula -> [String] -> PS [Statement]
enfold oldGoal bvs = 
  do newGoal <- lookAhead $ enfoldGoal bvs
     let newVars =  nub (getVarsOfFormula newGoal) \\ strings2Vars bvs
     derivation <- derive newGoal (bvs ++ (vars2Strings newVars))
     oldId <- newId
     soundnessId <- newId
     newId <- newId
     trace ("Found enfold " ++ show newGoal ++ " | " ++ (show $ newVars)) return [Statement oldId (bindVars oldGoal bvs)  
          (BySplit [
              (Statement soundnessId (bindVars (universallyQuantify newVars newGoal `Impl` oldGoal) bvs) ByContext None),
              (Statement newId (bindVars newGoal (bvs++(vars2Strings newVars))) (BySequence derivation) None)
          ]) None
        ]

enfoldGoal bvs = try (enfoldImplies bvs) <|> try (enfoldForall bvs)

enfoldImplies bvs =
  do reserved "Assume"
     l <- fof
     reserved "."
     traceM ("Found left impl: " ++ show l)
     _ <- derive Top bvs -- TODO what happens here?
     reserved "Hence"
     r <- fof
     reserved "."
     traceM ("Found implies creation " ++ show l ++ " => " ++ show r)
     return (Impl l r)

enfoldForall bvs =
  do reserved "Let"
     var <- many alphaNum
     spaces
     reserved "be arbitrary."
     traceM ("Found forall creation " ++ var)
     f <- enfoldGoal bvs
     return (Forall var f)


-- User gives cornerstones to proof

extendContext :: Formula -> [String] -> PS [Statement]
extendContext goal bvs =
  do derivedStatement <- then' bvs <|> take' bvs
     actualDerivation <- derive goal bvs
     id <- newId
     return [(Statement id (bindVars goal bvs) (BySequence (derivedStatement:actualDerivation)) None)]



-- STATEMENT MARKERS

then' :: [String] -> PS Statement
then' bvs =
  do pos <- getPos
     reserved "Then"
     spaces
     f <- fof
     by <- optionMaybe subContext
     reserved "."
     id <- newId
     case by of
        Nothing -> return $ Statement id (bindVars f bvs) ByContext pos 
        Just ids -> return $ Statement id (bindVars f bvs) (BySubcontext ids) pos

take' :: [String] -> PS Statement
take' bvs = 
  do pos <- getPos
     reserved "Take"
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
                      (Statement proofId (enfoldExists vars (bindVars f bvs)) ByContext pos)
                    ]) None)
        Just ids -> return (Statement id (bindVars f bvs) (BySequence [
                      (Statement proofId (enfoldExists vars (bindVars f bvs)) (BySubcontext ids) pos)
                    ]) None)


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
level3 = (try atom <|> try parentheses <|> try not' <|> try bot) `chainl1` (try or')

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

forall :: PS Formula
forall =
  do reserved "for all"
     try forallRaw <|> forallAtom

forallRaw :: PS Formula
forallRaw = 
  do var <- eid 
     try spaces
     reserved "."
     f <- fof
     return (Forall var f)

forallAtom :: PS Formula
forallAtom = 
  do atom <- atom
     spaces
     reserved "."
     f <- fof
     return $ universallyQuantify (getVarsOfFormula atom) (atom `Impl` f) 

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


-- ATOM PARSING

atom :: PS Formula
atom = do
  seeNext 10
  (name,terms) <- try functionIs <|> try (function False)
  return $ Atom name terms

function :: Bool -> PS (String, [Term])
function False = do
    traceM ("Trying function, wrapped sugar is false")
    try functionSugared <|> try functionRaw
function True = do
    traceM ("Trying function, wrapped sugar is true")
    try functionWrapSugared <|> try functionRaw

functionRaw  :: PS (String, [Term])
functionRaw =
  do name <- try $ many1 alphaNum
     reservedOp "("
     traceM ("found raw function with name '" ++ name ++ "'")
     terms <- (term False) `sepBy` (do {char ','; spaces})
     reserved ")"
     return (name,terms)

-- TODO limit to meaningful terms
functionIs :: PS (String, [Term])
functionIs = 
  do term <- term False
     spaces
     reserved "is"
     name <- many alphaNum
     return (name, [term])

term :: Bool -> PS Term
term sugarWrap = try (cons sugarWrap) <|> var 

cons :: Bool -> PS Term
cons sugarWrap = do 
  traceM ("looking for cons")
  (name,terms) <- try (function sugarWrap)
  traceM ("found cons " ++ name ++ " with terms " ++ concat (map (\x -> show x ++ ", ") terms))
  return $ Cons name terms

var :: PS Term
var =
  do var <- eid
     traceM $ "found var " ++ var
     return (Var var)



functionWrapSugared :: PS (String, [Term])
functionWrapSugared = do
    traceM ("TRYING WRAPPED SUGAR")
    reservedOp "("
    s <- functionSugared
    reserved ")"
    traceM ("WRAPPED SUGAR WORKED")
    return s

functionSugared :: PS (String, [Term])
functionSugared =
  do traceM ("trying sugars")
     ss <- sugars <$> getState
     matched <- foldl (<|>) (fail "") (map (\s -> try $ applySugar s) ss)
     return matched

applySugar :: (String,[String]) -> PS (String,[Term])
applySugar (name, ps) = 
  do seeNext 10
     traceM ("trying sugar '" ++ name ++ "' with pattern " ++ show ps)
     let termsM = foldl (++) [] (map (\p -> return $ try (matches p)) ps)
     traceM ("matched terms ")
     terms <- foldr (liftM2 (:)) (return []) termsM
     traceM ("sugar successful! " ++ concat (map show terms))
     return (name,filter (/= Var "BULLSHIT") terms)

matches :: String -> PS Term
matches p | p == "" = do seeNext 10
                         term <- try (term True)
                         traceM ("found term '" ++ show term ++ "'")
                         return term
          | otherwise = do 
                         traceM ("search for pattern '" ++ trim p ++ "'")
                         try spaces
                         reserved $ trim p
                         traceM ("found pattern '" ++ p ++ "'")
                         try spaces
                         return $ Var "BULLSHIT"

trim :: String -> String
trim = f . f
   where f = reverse . dropWhile isSpace

