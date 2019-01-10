module JS where

import Control.Monad.State
import Data.Char (toLower)
import qualified Data.Map as Map
import Language.JavaScript.Parser.AST

import Ast (Unop(..), Binop(..), Term(..))
import Symtab (Id(..))


type JSState = Map.Map String String
type JSM = State JSState

runJSM :: JSM a -> JSState -> a
runJSM f s = evalState f s


-- JS reserved strings (not to be used as identifiers in the generated
-- program).
reserved :: [String]
reserved =
  ["_alloc", "_set", "_get", "undefined", "abstract", "arguments",
   "await", "boolean", "break", "byte", "case", "catch", "char",
   "class", "const", "continue", "debugger", "default", "delete", "do",
   "double", "else", "enum", "eval", "export", "extends", "false",
   "final", "finally", "float", "for", "function", "goto", "if",
   "implements", "import", "in", "instanceof", "int", "interface",
   "let", "long", "native", "new", "null", "package", "private",
   "protected", "public", "return", "short", "static", "super",
   "switch", "synchronized", "this", "throw", "throws", "transient",
   "true", "try", "typeof", "var", "void", "volatile", "while", "with",
   "yield"]

-- The following three functions are used to build up a string->string
-- mapping for identifiers during compilation. Most identifiers will
-- be identity mapped, but we ensure that none of them conflict with
-- reserved words or one another (e.g., the source program could
-- contain an identifier that happens to be the same as an
-- auto-mangled name we generated, so we check for that as well).
conflicts :: String -> JSState -> Bool
conflicts s m =
  s `elem` Map.elems m ++ reserved

freshen :: String -> JSState -> String
freshen s m =
  let s' = "_" ++ s in
    if conflicts s' m then
      freshen s' m
    else
      s'

process_ident :: String -> JSM String
process_ident ident = do
  m <- get
  case Map.lookup ident m of
    Just s -> return s
    Nothing -> do
      let s = if conflicts ident m then freshen ident m else ident
      put $ Map.insert ident s m
      return s


toJSCommaList :: [a] -> JSCommaList a
toJSCommaList [] = JSLNil
toJSCommaList [x] = JSLOne x
toJSCommaList l = JSLCons (toJSCommaList $ init l) nil $ last l

nil = JSNoAnnot
space = JSAnnotSpace
semi = JSSemi nil

mkReturn :: JSExpression -> JSStatement
mkReturn e =
  JSReturn nil (Just $ JSExpressionParen nil e nil) semi


-- data Unop =
--   UMinus
--   | UNot
--   | URef
--   | UDeref
--   deriving (Eq, Generic, Show)

unopToJS :: Unop -> JSUnaryOp
unopToJS UMinus = JSUnaryOpMinus nil
unopToJS UNot = JSUnaryOpNot nil
unopToJS URef = undefined
unopToJS UDeref = undefined

-- data Binop =
--   BPlus
--   | BMinus
--   | BMult
--   | BDiv
--   | BEq
--   | BNeq
--   | BLt
--   | BLe
--   | BGt
--   | BGe
--   | BAnd
--   | BOr
--   | BUpdate
--   deriving (Eq, Generic, Show)

binopToJS :: Binop -> JSBinOp
binopToJS = undefined

-- data Term α =
--   TmVar α Id
--   | TmAbs α Id Type (Term α)
--   | TmApp α (Term α) (Term α)
--   | TmUnit α
--   | TmBool α Bool
--   | TmInt α Integer
--   | TmChar α Char
--   | TmIf α (Term α) (Term α) (Term α)
--   | TmUnop α Unop (Term α)
--   | TmBinop α Binop (Term α) (Term α)
--   | TmLet α Id (Term α) (Term α)
--   | TmVariant α Id [Term α]
--   | TmMatch α (Term α) [(Pattern, Term α)]
--   | TmRecord α [(Id, Term α)]
--   -- info, class name, method name, type index
--   | TmPlaceholder α ClassNm Id Type -- for class methods
--   deriving (Eq, Foldable, Functor, Generic, Traversable)

termToJS :: Term α -> JSM JSExpression

termToJS (TmVar _ (Id x)) = do
  x' <- process_ident x
  return $ JSIdentifier space x'

termToJS (TmAbs _ (Id x) _ tm) = do
  x' <- process_ident x
  tm' <- termToJS tm
  return $ JSFunctionExpression space JSIdentNone nil
    (JSLOne $ JSIdentName nil x') nil
    (JSBlock nil [mkReturn tm'] nil)

termToJS (TmApp _ tm1 tm2) = do
  tm1' <- termToJS tm1
  tm2' <- termToJS tm2
  return $ JSCallExpression tm1' nil (JSLOne tm2') nil

termToJS (TmUnit _) = return $ JSLiteral nil $ "null"

termToJS (TmBool _ b) = return $ JSLiteral nil $ toLower <$> show b

termToJS (TmInt _ i) = return $ JSLiteral nil $ show i

termToJS (TmChar _ c) = return $ JSLiteral nil $ show c

termToJS (TmIf _ tm1 tm2 tm3) = do
  tm1' <- termToJS tm1
  tm2' <- termToJS tm2
  tm3' <- termToJS tm3
  return $ JSExpressionTernary tm1' nil tm2' nil tm3'

termToJS (TmUnop _ u tm) = do
  undefined

termToJS _ = undefined


-- data Pattern =
--   PVar Id
--   | PUnit
--   | PBool Bool
--   | PInt Integer
--   | PChar Char
--   | PPair Pattern Pattern
--   | PConstructor Id [Pattern]
--   | PRecord [(Id, Pattern)]
--   deriving (Eq, Show)
