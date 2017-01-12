import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token


--data BExpr = BoolConst Bool
--           | Not BExpr
--           | BBinary BBinOp BExpr BExpr
--           | RBinary RBinOp AExpr AExpr
--            deriving (Show)

--data BBinOp = And | Or deriving (Show)

--data RBinOp = Greater | Less deriving (Show)

--data AExpr = Var String
--           | IntConst Integer
--           | Neg AExpr
--           | ABinary ABinOp AExpr AExpr
--             deriving (Show)

--data ABinOp = Add
--            | Subtract
--            | Multiply
--            | Divide
--              deriving (Show)

--data Stmt = Seq [Stmt]
--          | Assign String AExpr
--          | If BExpr Stmt Stmt
--          | While BExpr Stmt
--          | Skip
--            deriving (Show)

data EVar = EVar String
            deriving (Show)

data EProp = EProp String
            deriving (Show)

data ESentence = ELet EVar EProp | String
            deriving (Show)

data EStmt = ESeq [EStmt]
           | EDefinition ESentence 
           | EProposition ESentence
           | ELemma ESentence [ESentence]
            deriving (Show)

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.reservedNames   = [ "Definition"
                                     , "Proposition"
                                     , "Lemma"
                                     , "QED"
                                     ]
           , Token.reservedOpNames = ["Let", "be"
                                     ]
           }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
--integer    = Token.integer    lexer -- parses an integer
--semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace


elfeParser :: Parser EStmt
elfeParser = whiteSpace >> statement

statement :: Parser EStmt
statement =   parens statement
          <|> statement'

statement' :: Parser EStmt
statement' =   definitionSection
           <|> lemmaSection

definitionSection :: Parser EStmt
definitionSection =
  do reserved "Definition."
     sent  <- sentence
     return $ EDefinition sent

lemmaSection :: Parser EStmt
lemmaSection =
  do reserved "Lemma."
     sent  <- sentence
     reserved "Proof."
     proof <- sentence
     reserved "QED."
     return $ ELemma sent [proof]
 
--whileStmt :: Parser Stmt
--whileStmt =
--  do reserved "while"
--     cond <- bExpression
--     reserved "do"
--     stmt <- statement
--     return $ While cond stmt
 
--assignStmt :: Parser Stmt
--assignStmt =
--  do var  <- identifier
--     reservedOp ":="
--     expr <- aExpression
--     return $ Assign var expr
 
--skipStmt :: Parser Stmt
--skipStmt = reserved "skip" >> return Skip


sentence :: Parser ESentence
sentence = buildExpressionParser eOperators eTerm

eOperators = []

eTerm =  parens sentence
     <|> (reserved "Let"  >> return (ELet (EVar "x") (EProp "2") ))

letAssignment :: Parser ESentence
letAssignment =
  do reserved "Let"
     var  <- character
     reserved "be"
     prop <- character
     return $ ELet (EVar $ var) (EProp prop)

character :: Parser String
character = fmap return nonEscape <|> escape

escape :: Parser String
escape = do
    d <- char '\\'
    c <- oneOf "\\\"0nrvtbf" -- all the characters which can be escaped
    return [d, c]

nonEscape :: Parser Char
nonEscape = noneOf "\\\"\0\n\r\v\t\b\f"


--bExpression :: Parser BExpr
--bExpression = buildExpressionParser bOperators bTerm

--aOperators = [ [Prefix (reservedOp "-"   >> return (Neg             ))          ]
--             , [Infix  (reservedOp "*"   >> return (ABinary Multiply)) AssocLeft,
--                Infix  (reservedOp "/"   >> return (ABinary Divide  )) AssocLeft]
--             , [Infix  (reservedOp "+"   >> return (ABinary Add     )) AssocLeft,
--                Infix  (reservedOp "-"   >> return (ABinary Subtract)) AssocLeft]
--              ]
 
--bOperators = [ [Prefix (reservedOp "not" >> return (Not             ))          ]
--             , [Infix  (reservedOp "and" >> return (BBinary And     )) AssocLeft,
--                Infix  (reservedOp "or"  >> return (BBinary Or      )) AssocLeft]
--             ]

--aTerm =  parens aExpression
--     <|> liftM Var identifier
--     <|> liftM IntConst integer

--bTerm =  parens bExpression
--     <|> (reserved "true"  >> return (BoolConst True ))
--     <|> (reserved "false" >> return (BoolConst False))
--     <|> rExpression

--rExpression =
--  do a1 <- aExpression
--     op <- relation
--     a2 <- aExpression
--     return $ RBinary op a1 a2
 
--relation =   (reservedOp ">" >> return Greater)
--         <|> (reservedOp "<" >> return Less)

parseString :: String -> EStmt
parseString str =
  case parse elfeParser "" str of
    Left e  -> error $ show e
    Right r -> r

main :: IO()
main = do
  problem <- getContents
  print $ parseString problem 