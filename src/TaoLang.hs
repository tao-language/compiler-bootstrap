module TaoLang where

import Parser
import Tao

-- TODO: Return an Env
parse :: [String] -> Either ParserError [Expr]
parse [] = Right []
parse (src : srcs) = case Parser.parse src (expression "") of
  Left err -> Left err
  Right a -> do
    bs <- TaoLang.parse srcs
    Right (a : bs)

variableName :: Parser String
variableName = do
  -- TODO: support `-` and other characters, maybe URL-like names
  c <- lowercase
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  succeed (c : cs)

constructorName :: Parser String
constructorName = do
  -- TODO: support `-` and other characters, maybe URL-like names, or keep types CamelCase?
  c <- uppercase
  cs <- zeroOrMore (oneOf [alphanumeric, char '_'])
  succeed (c : cs)

typeName :: Parser String
typeName = constructorName

comment :: Parser String
comment = do
  -- TODO: support multi-line comments
  _ <- text "--"
  _ <- maybe' space
  until' (== '\n') anyChar

emptyLine :: Parser String
emptyLine = do
  _ <- zeroOrMore space
  comment' <- oneOf [comment, succeed ""]
  _ <- char '\n'
  succeed comment'

newLine :: String -> Parser [String]
newLine indent = do
  _ <- char '\n'
  comments <- zeroOrMore emptyLine
  _ <- text indent
  succeed comments

continueLine :: String -> Parser String
continueLine indent =
  do
    _ <- newLine indent
    extra <- oneOrMore space
    succeed (indent ++ extra)
    |> orElse (succeed indent)

token :: Parser a -> Parser a
token parser = do
  x <- parser
  _ <- zeroOrMore space
  succeed x

delimiter :: String -> Parser a -> Parser [String]
delimiter indent parser =
  oneOf
    [ newLine indent,
      do _ <- token parser; succeed []
    ]

operator :: String -> Parser Expr
operator indent = do
  let ops =
        [ fmap (const eq') (text "=="),
          fmap (const add') (text "+"),
          fmap (const sub') (text "-"),
          fmap (const mul') (text "*")
        ]
  _ <- token (char '(')
  _ <- continueLine indent
  op <- token (oneOf ops)
  _ <- maybe' (newLine indent)
  _ <- token (char ')')
  succeed op

pattern :: Parser Pattern
pattern = do
  oneOf
    [ fmap (const PAny) (token (char '_')),
      do
        x <- token variableName
        p <- oneOf [do _ <- token (char '@'); pattern, succeed PAny]
        succeed (PAs p x),
      fmap (PEq . Int) (token integer),
      do
        ctr <- token constructorName
        succeed (PCtr ctr []),
      do
        let ctrWithArgs = do
              ctr <- token constructorName
              ps <- zeroOrMore pattern
              succeed (PCtr ctr ps)
        _ <- token (char '(')
        p <- oneOf [ctrWithArgs, pattern]
        _ <- token (char ')')
        succeed p
    ]

expression :: String -> Parser Expr
expression indent = do
  let definition = oneOf [exactly 1 (defineRules indent), unpackPattern indent]
  let define :: Parser Expr
      define = do
        def <- definition
        defs <- zeroOrMore (do _ <- delimiter indent (char ';'); definition)
        _ <- delimiter indent (char ';')
        expr <- expression indent
        succeed (Let (concat (def : defs)) expr)

  -- TODO: make prefix and infix operators into functions instead of lists
  -- TODO: make operators support newLines
  -- TODO: make parentheses support newLines
  withOperators
    [ atom Match (cases indent),
      atom id define,
      atom Var (token variableName),
      atom Int (token integer),
      atom id (token (operator indent)),
      inbetween (const id) (token (char '(')) (token (char ')'))
    ]
    [ infixL 1 (const eq) (token (text "==")),
      infixL 2 (const add) (token (char '+')),
      infixL 2 (const sub) (token (char '-')),
      infixL 3 (const mul) (token (char '*')),
      infixL 4 (const App) (succeed ())
    ]

case' :: String -> Parser Case
case' indent = do
  ps <- oneOrMore pattern
  indent <- continueLine indent
  _ <- token (text "->")
  indent <- continueLine indent
  expr <- expression indent
  succeed (ps, expr)

cases :: String -> Parser [Case]
cases indent = do
  c <- case' indent
  cs <- zeroOrMore (do _ <- delimiter indent (char '|'); case' indent)
  succeed (c : cs)

defineRules :: String -> Parser (String, Expr)
defineRules indent = do
  let rule :: Parser ([Pattern], Expr)
      rule = do
        ps <- zeroOrMore (do _ <- continueLine indent; pattern)
        indent <- continueLine indent
        _ <- token (char '=')
        indent <- continueLine indent
        expr <- expression indent
        succeed (ps, expr)
  name <- token variableName
  case' <- rule
  cases <- zeroOrMore (do _ <- newLine indent; _ <- token (text name); rule)
  succeed (name, Match (case' : cases))

unpackPattern :: String -> Parser [(String, Expr)]
unpackPattern indent = do
  p <- pattern
  indent <- continueLine indent
  _ <- token (char '=')
  indent <- continueLine indent
  expr <- expression indent
  succeed (unpack (p, expr))
