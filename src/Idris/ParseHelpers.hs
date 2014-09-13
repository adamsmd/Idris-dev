{-# LANGUAGE GeneralizedNewtypeDeriving, ConstraintKinds, PatternGuards, OverlappingInstances, StandaloneDeriving #-}
module Idris.ParseHelpers where

import Prelude hiding (pi)

import Text.Trifecta.Delta
import Text.Trifecta hiding (span, stringLiteral, charLiteral, natural, symbol, char, string, whiteSpace, semiSep)
import Text.Trifecta.Indentation as Ind
import Text.Parser.LookAhead
import Text.Parser.Expression
import qualified Text.Parser.Token as Tok
import qualified Text.Parser.Char as Chr
import qualified Text.Parser.Token.Highlight as Hi

import Idris.AbsSyntax

import Idris.Core.TT
import Idris.Core.Evaluate
import Idris.Delaborate (pprintErr)
import Idris.Docstrings
import Idris.Output (iWarn)

import qualified Util.Pretty as Pretty (text)

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict

import Data.Maybe
import qualified Data.List.Split as Spl
import Data.List
import Data.Monoid
import Data.Char
import qualified Data.Map as M
import qualified Data.HashSet as HS
import qualified Data.Text as T
import qualified Data.ByteString.UTF8 as UTF8

import System.FilePath

import Debug.Trace

-- | Idris parser with state used during parsing
type IdrisParser = StateT IState IdrisInnerParser

newtype IdrisInnerParser a = IdrisInnerParser { runInnerParser :: IndentationParserT Char Parser a }
  deriving (Monad, Functor, MonadPlus, Applicative, Alternative, CharParsing, LookAheadParsing, DeltaParsing, MarkParsing Delta, TokenParsing)

deriving instance Parsing IdrisInnerParser
deriving instance IndentationParsing IdrisInnerParser

instance TokenParsing IdrisParser where
  someSpace = ignoreAbsoluteIndentation (localTokenMode (const Ind.Any) (many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment))) *> pure ()
  token p = do s <- get
               (FC fn (sl, sc) _) <- getFC --TODO: Update after fixing getFC
               r <- p
               (FC fn _ (el, ec)) <- getFC
               ignoreAbsoluteIndentation (localTokenMode (const Ind.Any) whiteSpace)
               put (s { lastTokenSpan = Just (FC fn (sl, sc) (el, ec)) })
               return r
-- | Generalized monadic parsing constraint type
type MonadicParsing m = (DeltaParsing m, LookAheadParsing m, TokenParsing m, Monad m, IndentationParsing m)

-- | Helper to run Idris inner parser based stateT parsers
runparser :: Indentation -> Indentation -> Bool -> IndentationRel -> StateT st IdrisInnerParser res -> st -> String -> String -> Result res
runparser lo hi mode rel p i inputname =
  parseString (evalIndentationParserT (runInnerParser (evalStateT p i)) (mkIndentationState lo hi mode rel))
              (Directed (UTF8.fromString inputname) 0 0 0 0)

runparserStrict = runparser 1 1 False Gt
runparserLax = runparser 1 infIndentation False Ind.Any

noDocCommentHere :: String -> IdrisParser ()
noDocCommentHere msg =
  optional (do fc <- getFC
               docComment
               ist <- get
               put ist { parserWarnings = (fc, Msg msg) : parserWarnings ist}) *>
  pure ()

clearParserWarnings :: Idris ()
clearParserWarnings = do ist <- getIState
                         putIState ist { parserWarnings = [] }

reportParserWarnings :: Idris ()
reportParserWarnings = do ist <- getIState
                          mapM_ (uncurry iWarn)
                                (map (\ (fc, err) -> (fc, pprintErr ist err)) .
                                 reverse .
                                 nub $
                                 parserWarnings ist)
                          clearParserWarnings

{- * Space, comments and literals (token/lexing like parsers) -}

-- | Consumes any simple whitespace (any character which satisfies Char.isSpace)
simpleWhiteSpace :: MonadicParsing m => m ()
simpleWhiteSpace = satisfy isSpace *> pure ()

-- | Checks if a charcter is end of line
isEol :: Char -> Bool
isEol '\n' = True
isEol  _   = False

eol :: MonadicParsing m => m ()
eol = (satisfy isEol *> pure ()) <|> lookAhead eof <?> "end of line"

{- | Consumes a single-line comment

@
     SingleLineComment_t ::= '--' EOL_t
                        |     '--' ~DocCommentMarker_t ~EOL_t* EOL_t
                        ;
@
 -}
singleLineComment :: MonadicParsing m => m ()
singleLineComment =     try (string "--" *> eol *> pure ())
                    <|> try (string "--" *> many simpleWhiteSpace *>
                             many (satisfy (not . isEol)) *>
                             eol *> pure ())
                    <?> ""

{- | Consumes a multi-line comment

@
  MultiLineComment_t ::=
     '{ -- }'
   | '{ -' ~DocCommentMarker_t InCommentChars_t
  ;
@

@
  InCommentChars_t ::=
   '- }'
   | MultiLineComment_t InCommentChars_t
   | ~'- }'+ InCommentChars_t
  ;
@
-}
multiLineComment :: MonadicParsing m => m ()
multiLineComment =     try (string "{-" *> (string "-}") *> pure ())
                   <|> string "{-" *> inCommentChars
                   <?> ""
  where inCommentChars :: MonadicParsing m => m ()
        inCommentChars =     string "-}" *> pure ()
                         <|> try (multiLineComment) *> inCommentChars
                         <|> string "|||" *> many (satisfy (not . isEol)) *> eol *> inCommentChars
                         <|> skipSome (noneOf startEnd) *> inCommentChars
                         <|> oneOf startEnd *> inCommentChars
                         <?> "end of comment"
        startEnd :: String
        startEnd = "{}-"

{-| Parses a documentation comment (similar to haddoc) given a marker character

@
  DocComment_t ::=   '|||' ~EOL_t* EOL_t
                 ;
@
 -}
docComment :: IdrisParser (Docstring, [(Name, Docstring)])
docComment = do dcs <- some docCommentLine
                args <- many $ do (name, first) <- argDocCommentLine
                                  rest <- many docCommentLine
                                  return (name, concat (intersperse "\n" (first:rest)))
                return (parseDocstring $ T.pack (concat (intersperse "\n" dcs)),
                        map (\(n, d) -> (n, parseDocstring (T.pack d))) args)

  where docCommentLine :: MonadicParsing m => m String
        docCommentLine = try (localAbsoluteIndentation $
                              do string "|||"
                                 many (satisfy (==' '))
                                 contents <- option "" (do first <- satisfy (\c -> not (isEol c || c == '@'))
                                                           res <- many (satisfy (not . isEol))
                                                           return $ first:res)
                                 eol ; someSpace
                                 return contents)-- ++ concat rest))
                        <?> ""

        argDocCommentLine = localAbsoluteIndentation $
                            do string "|||"
                               many (satisfy isSpace)
                               char '@'
                               many (satisfy isSpace)
                               n <- name
                               many (satisfy isSpace)
                               docs <- many (satisfy (not . isEol))
                               eol ; someSpace
                               return (n, docs)



-- | Parses some white space
whiteSpace :: MonadicParsing m => m ()
whiteSpace = Tok.whiteSpace

-- | Parses a string literal
stringLiteral :: MonadicParsing m => m String
stringLiteral = Tok.stringLiteral -- TODO: handle string gaps

-- | Parses a char literal
charLiteral :: MonadicParsing m => m Char
charLiteral = Tok.charLiteral

-- | Parses a natural number
natural :: MonadicParsing m => m Integer
natural = Tok.natural

-- | Parses an integral number
integer :: MonadicParsing m => m Integer
integer = Tok.integer

-- | Parses a floating point number
float :: MonadicParsing m => m Double
float = Tok.double

{- * Symbols, identifiers, names and operators -}


-- | Idris Style for parsing identifiers/reserved keywords
idrisStyle :: MonadicParsing m => IdentifierStyle m
idrisStyle = IdentifierStyle _styleName _styleStart _styleLetter _styleReserved Hi.Identifier Hi.ReservedIdentifier
  where _styleName = "Idris"
        _styleStart = satisfy isAlpha
        _styleLetter = satisfy isAlphaNum <|> oneOf "_'."
        _styleReserved = HS.fromList ["let", "in", "data", "codata", "record", "Type",
                                      "do", "dsl", "import", "impossible",
                                      "case", "of", "total", "partial", "mutual",
                                      "infix", "infixl", "infixr", "rewrite",
                                      "where", "with", "syntax", "proof", "postulate",
                                      "using", "namespace", "class", "instance", "parameters",
                                      "public", "private", "abstract", "implicit",
                                      "quoteGoal"]

char :: MonadicParsing m => Char -> m Char
char = Chr.char

string :: MonadicParsing m => String -> m String
string = Chr.string

-- | Parses a character as a token
lchar :: MonadicParsing m => Char -> m Char
lchar = token . char

-- | Parses string as a token
symbol :: MonadicParsing m => String -> m String
symbol = Tok.symbol

-- | Parses a reserved identifier
reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve idrisStyle

-- Taken from Parsec (c) Daan Leijen 1999-2001, (c) Paolo Martini 2007
-- | Parses a reserved operator
reservedOp :: MonadicParsing m => String -> m ()
reservedOp name = token $ try $
  do string name
     notFollowedBy (operatorLetter) <?> ("end of " ++ show name)

-- | Parses an identifier as a token
identifier :: MonadicParsing m => m String
identifier = token $ Tok.ident idrisStyle

-- | Parses an identifier with possible namespace as a name
iName :: MonadicParsing m => [String] -> m Name
iName bad = maybeWithNS identifier False bad <?> "name"

-- | Parses an string possibly prefixed by a namespace
maybeWithNS :: MonadicParsing m => m String -> Bool -> [String] -> m Name
maybeWithNS parser ascend bad = do
  i <- option "" (lookAhead identifier)
  when (i `elem` bad) $ unexpected "reserved identifier"
  let transf = if ascend then id else reverse
  (x, xs) <- choice (transf (parserNoNS parser : parsersNS parser i))
  return $ mkName (x, xs)
  where parserNoNS :: MonadicParsing m => m String -> m (String, String)
        parserNoNS parser = do x <- parser; return (x, "")
        parserNS   :: MonadicParsing m => m String -> String -> m (String, String)
        parserNS   parser ns = do xs <- string ns; lchar '.';  x <- parser; return (x, xs)
        parsersNS  :: MonadicParsing m => m String -> String -> [m (String, String)]
        parsersNS parser i = [try (parserNS parser ns) | ns <- (initsEndAt (=='.') i)]

-- | Parses a name
name :: IdrisParser Name
name = (<?> "name") $ do
    keywords <- syntax_keywords <$> get
    aliases  <- module_aliases  <$> get
    unalias aliases <$> iName keywords
  where
    unalias :: M.Map [T.Text] [T.Text] -> Name -> Name
    unalias aliases (NS n ns) | Just ns' <- M.lookup ns aliases = NS n ns'
    unalias aliases name = name

{- | List of all initial segments in ascending order of a list.  Every
such initial segment ends right before an element satisfying the given
condition.
-}
initsEndAt :: (a -> Bool) -> [a] -> [[a]]
initsEndAt p [] = []
initsEndAt p (x:xs) | p x = [] : x_inits_xs
                    | otherwise = x_inits_xs
  where x_inits_xs = [x : cs | cs <- initsEndAt p xs]


{- | Create a `Name' from a pair of strings representing a base name and its
 namespace.
-}
mkName :: (String, String) -> Name
mkName (n, "") = sUN n
mkName (n, ns) = sNS (sUN n) (reverse (parseNS ns))
  where parseNS x = case span (/= '.') x of
                      (x, "")    -> [x]
                      (x, '.':y) -> x : parseNS y

opChars :: String
opChars = ":!#$%&*+./<=>?@\\^|-~"

operatorLetter :: MonadicParsing m => m Char
operatorLetter = oneOf opChars

-- | Parses an operator
operator :: MonadicParsing m => m String
operator = do op <- token . some $ operatorLetter
              when (op `elem` [":", "=>", "->", "<-", "=", "?=", "|"]) $ 
                   fail $ op ++ " is not a valid operator"
              return op

{- * Position helpers -}
{- | Get filename from position (returns "(interactive)" when no source file is given)  -}
fileName :: Delta -> String
fileName (Directed fn _ _ _ _) = UTF8.toString fn
fileName _                     = "(interactive)"

{- | Get line number from position -}
lineNum :: Delta -> Int
lineNum (Lines l _ _ _)      = fromIntegral l + 1
lineNum (Directed _ l _ _ _) = fromIntegral l + 1
lineNum _ = 0

{- | Get column number from position -}
columnNum :: Delta -> Int
columnNum pos = fromIntegral (column pos) + 1


{- | Get file position as FC -}
getFC :: MonadicParsing m => m FC
getFC = do s <- position
           let (dir, file) = splitFileName (fileName s)
           let f = if dir == addTrailingPathSeparator "." then file else fileName s
           return $ FC f (lineNum s, columnNum s) (lineNum s, columnNum s) -- TODO: Change to actual spanning

{-* Syntax helpers-}
-- | Bind constraints to term
bindList :: (Name -> PTerm -> PTerm -> PTerm) -> [(Name, PTerm)] -> PTerm -> PTerm
bindList b []          sc = sc
bindList b ((n, t):bs) sc = b n t (bindList b bs sc)

{- * Layout helpers -}

-- A close brace that may appear at the current indentation
pClose :: (MonadicParsing m) => m Char
pClose = localTokenMode (const Ge) (lchar '}')

{- Parses zero or more 'p' separated by one or more ';' and preceeded
or followed by zero or more ';'.  Not nullable so we can safely use it
in 'many' and 'some'.

The state machine for this is as follows:

    +-------------+
    |             |
    v             |
--> go -- ';' --> go' -+-->
    |             ^    |
    |             |    |
    +-> p - ';' --+    |
        |              |
        +--------------+
-}

semiSepNonNull p = liftM reverse $ go [] where
  go' xs = option xs (go xs)
  go xs = (lchar ';' >> go' xs)
       <|> (p >>= \x -> option (x:xs) (lchar ';' >> go' (x : xs)))

-- Fails if a parser returns an empty list
notNull m = m >>= \x -> case x of [] -> mzero; _ -> return x

-- Like semiSepNonNull but is nullable
semiSep  p = semiSepNonNull p <|> return []

-- Like semiSepNonNull but requires at least one 'p' be parsed
semiSep1 p = notNull (semiSepNonNull p)

-- An indentation sensitive block of zero or more 'p'
pBlock p =
  between (lchar '{') (pClose) (localIndentation (Ind.Const 0) (semiSep p))
  <|> (liftM concat $ localIndentation Gt $ many $ absoluteIndentation $ semiSepNonNull p)

-- An indentation sensitive block of one or more 'p'
pBlock1 p = notNull (pBlock p)

-- An indentation sensitive block of exactly one 'p'
-- TODO: is the use of optionTerm a bug?
pBlockS p = between (lchar '{') (pClose) (localIndentation (Ind.Const 0) (optionTerm p))
  <|> (localIndentation Gt $ absoluteIndentation (optionTerm p))

-- 'p' followed by an optional ';'
optionTerm p = do x <- p
                  option ';' (lchar ';')
                  return x

-- | Checks if the following character matches provided parser
lookAheadMatches :: MonadicParsing m => m a -> m Bool
lookAheadMatches p = do match <- lookAhead (optional p)
                        return $ isJust match

{- | Parses an accessibilty modifier (e.g. public, private) -}
accessibility :: IdrisParser Accessibility
accessibility = do reserved "public";   return Public
            <|> do reserved "abstract"; return Frozen
            <|> do reserved "private";  return Hidden
            <?> "accessibility modifier"

-- | Adds accessibility option for function
addAcc :: Name -> Maybe Accessibility -> IdrisParser ()
addAcc n a = do i <- get
                put (i { hide_list = (n, a) : hide_list i })

{- | Add accessbility option for data declarations
 (works for classes too - 'abstract' means the data/class is visible but members not) -}
accData :: Maybe Accessibility -> Name -> [Name] -> IdrisParser ()
accData (Just Frozen) n ns = do addAcc n (Just Frozen)
                                mapM_ (\n -> addAcc n (Just Hidden)) ns
accData a n ns = do addAcc n a
                    mapM_ (`addAcc` a) ns


{- * Error reporting helpers -}
{- | Error message with possible fixes list -}
fixErrorMsg :: String -> [String] -> String
fixErrorMsg msg fixes = msg ++ ", possible fixes:\n" ++ (concat $ intersperse "\n\nor\n\n" fixes)

-- | Collect 'PClauses' with the same function name
collect :: [PDecl] -> [PDecl]
collect (c@(PClauses _ o _ _) : ds)
    = clauses (cname c) [] (c : ds)
  where clauses :: Maybe Name -> [PClause] -> [PDecl] -> [PDecl]
        clauses j@(Just n) acc (PClauses fc _ _ [PClause fc' n' l ws r w] : ds)
           | n == n' = clauses j (PClause fc' n' l ws r (collect w) : acc) ds
        clauses j@(Just n) acc (PClauses fc _ _ [PWith fc' n' l ws r w] : ds)
           | n == n' = clauses j (PWith fc' n' l ws r (collect w) : acc) ds
        clauses (Just n) acc xs = PClauses (fcOf c) o n (reverse acc) : collect xs
        clauses Nothing acc (x:xs) = collect xs
        clauses Nothing acc [] = []

        cname :: PDecl -> Maybe Name
        cname (PClauses fc _ _ [PClause _ n _ _ _ _]) = Just n
        cname (PClauses fc _ _ [PWith   _ n _ _ _ _]) = Just n
        cname (PClauses fc _ _ [PClauseR _ _ _ _]) = Nothing
        cname (PClauses fc _ _ [PWithR _ _ _ _]) = Nothing
        fcOf :: PDecl -> FC
        fcOf (PClauses fc _ _ _) = fc
collect (PParams f ns ps : ds) = PParams f ns (collect ps) : collect ds
collect (PMutual f ms : ds) = PMutual f (collect ms) : collect ds
collect (PNamespace ns ps : ds) = PNamespace ns (collect ps) : collect ds
collect (PClass doc f s cs n ps pdocs ds : ds')
    = PClass doc f s cs n ps pdocs (collect ds) : collect ds'
collect (PInstance f s cs n ps t en ds : ds')
    = PInstance f s cs n ps t en (collect ds) : collect ds'
collect (d : ds) = d : collect ds
collect [] = []

