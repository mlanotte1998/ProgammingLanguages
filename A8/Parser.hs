{-# LANGUAGE LambdaCase #-}
{-|
Module      : Parser
Description : S-expression parser for CS4400
Copyright   : (c) Ferd, 2020

Maintainer  : f.vesely@northeastern.edu

-}
module Parser 
    ( parseSExpression
    , parseSExpressions
    , fromFile
    , allTests
    ) where

import qualified SExpression as S

import Result


import Control.Applicative
import Data.Char (isDigit, isAlpha, isLower, isUpper, isSpace)

import SimpleTests (test, beginTests, endTests, testSection)

-- * Parse an s-expression:
parseSExpression :: String -> Result S.Expr
parseSExpression s = 
    case filter (null . snd) $ parse (only sexpr) (removeComments s) of
         (sexpr, "") : _ -> return sexpr
         _ -> fail "Couldn't parse s-expression."


-- | Parse one or more s-expressions and
parseSExpressions :: String -> Result [S.Expr]
parseSExpressions s = 
    case filter (null . snd) $ parse (only sexprs) (removeComments s) of
         (sexprs, "") : _ -> return sexprs
         _ -> fail "Couldn't parse s-expression."

-- | Parse a file of s-expressions
fromFile :: String -> IO (Result [S.Expr])
fromFile filename = parseSExpressions <$> readFile filename


-- | Remove comments, that is, ";" to the end of the line
removeComments :: String -> String
removeComments "" = ""
removeComments (';' : s) = removeComments $ dropWhile (/= '\n') s
removeComments ('"' : s) = '"' : s' ++ removeComments rest
  where 
    (s', rest) = skipQuote $ span (/= '"') s
    skipQuote (str, '"' : rest) = (str ++ "\"", rest)
    skipQuote x = x
removeComments (c : s) = c : removeComments s

-- * Parser details

-- |A type for parsers
-- A parser is a function that takes a string and retutns
-- a list of possible parses, each paired with what's left of the string.
newtype Parser a = Parser { parse :: String -> [(a, String)] }

-- |A Parser is a functor
instance Functor Parser where
    fmap f (Parser p) = Parser (fmap (\(r, s) -> (f r, s)) . p)

-- |A Parser is also an applicative functor
instance Applicative Parser where
    pure x = Parser (\s -> [(x, s)])
    Parser pf <*> px = 
        Parser $ \s -> 
            concat $ (\(f, s') -> parse (fmap f px) s') <$> pf s

-- |Parsers can be sequenced and form a monad
instance Monad Parser where
    return = pure
    px >>= f = Parser $ \s -> 
        concatMap (\(x, s') -> parse (f x) s') $ parse px s

-- |Parsers form alternatives
instance Alternative Parser where
    empty = Parser $ const []
    Parser pa <|> Parser pb =
        Parser $ \s -> case pa s of
                            [] -> pb s
                            vs -> vs

-- * Primitives and combinators

-- |Get the next character from the input
next :: Parser Char
next = Parser $ \case  
    c : s -> [(c, s)]
    _ -> []

-- |Succeed if the parsed item satisfied the given predicate
satisfy :: (a -> Bool) -> Parser a -> Parser a
satisfy p pa = do
    x <- pa
    if p x 
       then return x
       else empty

-- |Consume any spaces at the beginning of input
spaces :: Parser ()
spaces = do 
    many $ satisfy isSpace next
    return ()

-- |Consume the given token
token :: Parser a -> Parser a
token p = do
    spaces
    p
--    spaces
--    return r

-- Ignore trailing spaces
only :: Parser a -> Parser a
only p = do
    r <- token p
    spaces
    return r

-- |Zero or one
opt :: Monoid a => Parser a -> Parser a
opt p = p <|> return mempty

one :: Parser a -> Parser [a]
one p = do
    r <- p
    return [r]


followedBy :: Monoid a => Parser a -> Parser a -> Parser a
followedBy p1 p2 = do
    r1 <- p1
    r2 <- p2
    return $ r1 `mappend` r2

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sepp = opt (one p) `followedBy` many elems
  where
    elems = sepp >> p


-- |Consume the given character
char :: Char -> Parser Char
char c = satisfy (== c) next

-- |Consume a digit, a letter, a lower-case letter, an upper-case letter, or
-- a space
digit, alpha, lower, upper :: Parser Char
digit = satisfy isDigit next
alpha = satisfy isAlpha next
lower = satisfy isLower next
upper = satisfy isUpper next
space = satisfy isSpace next

-- |Consume the given string
exactly :: String -> Parser String
exactly "" = return ""
exactly (c : cs) = do
    char c
    exactly cs
    return $ c : cs

-- |Consume the given symbol
symbol :: String -> Parser String
symbol s = token $ exactly s

-- |Parse inbetween the given delimiters
between :: Parser a -> Parser b -> Parser c -> Parser b
between left p right = do
    left
    r <- p
    right
    return r

-- * S-expressions

-- |Parentheses, brackets
lparen, rparen, lbrack, rbrack :: Parser String
lparen = symbol "("
rparen = symbol ")"
lbrack = symbol "["
rbrack = symbol "]"

-- |Atoms
digits :: Parser String
digits = some digit

integral :: Parser String
integral = opt (exactly "-") `followedBy` digits

integer :: Parser S.Expr
integer = do
    s <- token integral
    return $ S.Integer $ read s


real :: Parser S.Expr
real = do 
    s <- token $ integral `followedBy` exactly "." `followedBy` digits
    return $ S.Real $ read s

boolean :: Parser S.Expr
boolean = token bool
  where
    bool =
          (exactly "#t" >> return (S.Boolean True))
        <|>
          (exactly "#f" >> return (S.Boolean False))

atom :: Parser S.Expr
atom = real <|> integer <|> boolean <|> identifier

dotted :: Parser S.Expr
dotted = do 
    token lparen
    left <- sexpr
    symbol "."
    right <- sexpr
    token rparen
    return $ S.Dotted left right

slist :: Parser S.Expr
slist = do
    sexprs <-     between lparen (sexpr `sepBy` some space) rparen
              <|> between lbrack (sexpr `sepBy` some space) rbrack
    return $ S.List sexprs

sexpr :: Parser S.Expr
sexpr = atom <|> slist <|> dotted

sexprs :: Parser [S.Expr]
sexprs = many sexpr

-- <identifier>	::= <initial> <subsequent>* | + | - | ...
-- <initial> ::= <letter> | ! | $ | % | & | * | / | : | < | = | > | ? | ~ | _ | ^
-- <subsequent> ::= <initial> | <digit> | . | + | -

identifier :: Parser S.Expr
identifier = do 
    s <- token $ (one initial `followedBy` many subsequent) <|> special
    return $ S.Symbol s
  where
    initial = lower <|> upper <|> initialSpecial
    subsequent = initial <|> digit <|> subsequentSpecial
    special = foldl1 (<|>) $ map exactly ["+", "-", "..."]
    initialSpecial = satisfy (`elem` "!$%&*/:<=>?~_^-") next
    subsequentSpecial = satisfy (`elem` ".+-") next

-- Tests
test_next = do
    test "next abcd" (parse next "abcd") [('a', "bcd")]
    test "next \"\"" (parse next "") []

test_satisfy = do
    test "satisfy: digit" 
        (parse (satisfy isDigit next) "1abc") 
        [('1', "abc")]
    test "satisfy: not digit" 
        (parse (satisfy isDigit next) "abc") 
        []

test_char = do
    test "char: match"
        (parse (char 'a') "abc")
        [('a', "bc")]
    test "char: no match"
        (parse (char 'b') "abc")
        []

test_charTypes = do
    test "digit: '1'" (parse digit "1abc") [('1', "abc")]
    test "digit: 'a'" (parse digit "abc") []
    test "alpha: 'a'" (parse alpha "abc") [('a', "bc")]
    test "alpha: '1'" (parse alpha "1abc") []
    test "lower: 'a'" (parse lower "abc") [('a', "bc")]
    test "lower: 'A'" (parse lower "Abc") []
    test "upper: 'A'" (parse upper "ABC") [('A', "BC")]
    test "upper: 'a'" (parse upper "abc") []
    test "space: ' '" (parse space " BC") [(' ', "BC")]
    test "space: '\\t'" (parse space "\tBC") [('\t', "BC")]
    test "space: '\\n'" (parse space "\nBC") [('\n', "BC")]
    test "space: 'a'" (parse space "a  ") []


test_symbol = do
    test "symbol: hello" 
        (parse (symbol "hello") " hello   world  ")
        [("hello", "   world  ")]
    test "symbol: hello" 
        (parse (symbol "hello") "\n\thello\n\t  \n   world\n")
        [("hello", "\n\t  \n   world\n")]

test_atoms = do
    testSection "Atoms"
    test "integer 1234" 
        (parse integer "1234 abc")
        [(S.Integer 1234, " abc")]
    test "integer -123454325" 
        (parse integer "-123454325 abc")
        [(S.Integer $ -123454325 , " abc")]
    test "real 1234.0" 
        (parse real "1234.0      abc")
        [(S.Real 1234, "      abc")]
    test "real 3.14" 
        (parse real "3.14\n1343")
        [(S.Real 3.14, "\n1343")]
    test "real -14.98" 
        (parse real "-14.98\n1343")
        [(S.Real (-14.98), "\n1343")]
    test "real 0.0" 
        (parse real "0.0\n1343")
        [(S.Real 0, "\n1343")]
    test "real 12.0" 
        (parse real "12.0\n1343")
        [(S.Real 12, "\n1343")]
    test "boolean #t" 
        (parse boolean "#t\n1343")
        [(S.Boolean True, "\n1343")]
    test "boolean #f" 
        (parse boolean "#f abcd")
        [(S.Boolean False, " abcd")]
    test "identifier: x"
        (parse identifier "x\n1343")
        [(S.Symbol "x", "\n1343")]
    test "identifier: x->y"
        (parse identifier "x->y\n1343")
        [(S.Symbol "x->y", "\n1343")]
    test "identifier: >"
        (parse identifier ">\n1343")
        [(S.Symbol ">", "\n1343")]
    test "identifier: ="
        (parse identifier "=\n1343")
        [(S.Symbol "=", "\n1343")]
    test "identifier: <="
        (parse identifier "<=\n1343")
        [(S.Symbol "<=", "\n1343")]
         
test_sexprs = do
    test "()" 
        (parse sexpr "()")
        [(S.List [], "")]
    test "(1)" 
        (parse sexpr "(1)")
        [(S.List [S.Integer 1], "")]
    test "(a b)" 
        (parse sexpr "(a b)")
        [(S.List [S.Symbol "a", S.Symbol "b"], "")]
    test "(+ 1 2.1)" 
        (parse sexpr "(+ 1 2.1)")
        [(S.List [S.Symbol "+", S.Integer 1, S.Real 2.1], "")]
    test "(+ 1 \n        #t\n\t#f \t3.14)" 
        (parse sexpr "(+ 1 \n        #t\n\t#f \t3.14)")
        [(S.List [S.Symbol "+", S.Integer 1, S.Boolean True, S.Boolean False, S.Real 3.14], "")]
    test "(a (b c) (d (e f (g h) (i)) j))"
        (parse sexpr "(a (b c) (d (e f (g h) (i)) j))")
        [( S.List [ S.Symbol "a"
                  , S.List [ S.Symbol "b"
                           , S.Symbol "c"
                           ]
                  , S.List [ S.Symbol "d"
                           , S.List [ S.Symbol "e"
                                    , S.Symbol "f"
                                    , S.List [ S.Symbol "g"
                                             , S.Symbol "h"
                                             ]
                                    , S.List [ S.Symbol "i" ]
                                    ]
                           , S.Symbol "j"
                           ]
                  ]
         , ""
         )]                               
    test "(a (b c) (d (e f (g h) (i)) j))"
        (parse (S.toString <$> sexpr) "(a (b c) (d (e f (g h) (i)) j))")
        [("(a (b c) (d (e f (g h) (i)) j))", "")]
    test "(a [b c] (d [e f [g h] (i)] j))"
        (parse (S.toString <$> sexpr) "(a [b c] (d [e f [g h] (i)] j))")
        [("(a (b c) (d (e f (g h) (i)) j))", "")]
    test "(1 . 2)"
        (parse sexpr "(1 . 2)")
        [(S.Dotted (S.Integer 1) (S.Integer 2), "")]
    test "(1 . (2 . 3))"
        (parse sexpr "(1 . (2 . 3))")
        [(S.Dotted (S.Integer 1) (S.Dotted (S.Integer 2) (S.Integer 3)), "")]
    test "(    (     1 .    2  )  .  3 )    "
        (parse sexpr "((1 . 2) . 3)")
        [(S.Dotted (S.Dotted (S.Integer 1) (S.Integer 2)) (S.Integer 3), "")]
      


scheme1 = "(define (segments-all-but-last nesegs)\n\
\  (cond ((empty? (rest nesegs)) empty)\n\
\        (else (cons (first nesegs)\n\
\                    (segments-all-but-last (rest nesegs))))))\n"

allTests = do
    beginTests
    testSection "Parser primitives and combinators"
    test_next
    test_satisfy
    test_charTypes
    test_symbol
    test_atoms
    test_sexprs
    endTests

