module JS where

import Control.Monad.State
import Data.Bifunctor (first)
import Data.Char (toLower)
import Data.List (intercalate, intersperse)
import qualified Data.Map as Map
import Language.JavaScript.Parser.AST
import Language.JavaScript.Pretty.Printer

import Ast (Binop(..), Command(..), Pattern(..), Term(..), Unop(..))
import Symtab (Id(..))


type JSState = (Int, Map.Map String String)
type JSM = State JSState

runJSM :: JSM a -> JSState -> a
runJSM f s = evalState f s

nextSym :: String -> JSM String
nextSym prefix = do
  (i, m) <- get
  put (i + 1, m)
  return $ prefix ++ show i


-- JS reserved strings (not to be used as identifiers in the generated
-- program).
reserved :: [String]
reserved =
  ["_mkVariant", "undefined", "abstract", "arguments", "await",
   "boolean", "break", "byte", "case", "catch", "char", "class",
   "const", "continue", "debugger", "default", "delete", "do", "double",
   "else", "enum", "eval", "export", "extends", "false", "final",
   "finally", "float", "for", "function", "goto", "if", "implements",
   "import", "in", "instanceof", "int", "interface", "let", "long",
   "native", "new", "null", "package", "private", "protected", "public",
   "return", "short", "static", "super", "switch", "synchronized",
   "this", "throw", "throws", "transient", "true", "try", "typeof",
   "var", "void", "volatile", "while", "with", "yield"]

-- The following three functions are used to build up a string->string
-- mapping for identifiers during compilation. Most identifiers will
-- be identity mapped, but we ensure that none of them conflict with
-- reserved words or one another (e.g., the source program could
-- contain an identifier that happens to be the same as an
-- auto-mangled name we generated, so we check for that as well).
conflicts :: String -> Map.Map String String -> Bool
conflicts s m =
  s `elem` Map.elems m ++ reserved

freshen :: String -> Map.Map String String -> String
freshen s m =
  let s' = "_" ++ s in
    -- Also disallow "_x" prefix to avoid conflict with gensym.
    if conflicts s' m || (length s > 0 && s!!0 == 'x') then
      freshen s' m
    else s'

replace :: Eq a => a -> a -> [a] -> [a]
replace _ _ [] = []
replace x y (z:xs) = (if x == z then y else z) : replace x y xs

legalize :: String -> String
legalize = replace '\'' '_' . replace '?' '_'

process_ident :: String -> JSM String
process_ident ident = do
  let ident' = legalize ident
  (n, m) <- get
  case Map.lookup ident' m of
    Just s -> return s
    Nothing -> do
      let s = if conflicts ident' m then freshen ident' m else ident'
      put (n, Map.insert ident' s m)
      return s


toJSCommaList :: [a] -> JSCommaList a
toJSCommaList [] = JSLNil
toJSCommaList [x] = JSLOne x
toJSCommaList l = JSLCons (toJSCommaList $ init l) nil $ last l

nil :: JSAnnot
nil = JSNoAnnot

space :: JSAnnot
space = JSAnnotSpace

semi :: JSSemi
semi = JSSemi nil

mkReturn :: JSExpression -> JSStatement
mkReturn e =
  JSReturn nil (Just $ JSExpressionParen nil e nil) semi

indexJS :: JSExpression -> Integer -> JSExpression
indexJS e i = JSMemberSquare e nil (intToJS i) nil

propertyJS :: JSExpression -> String -> JSExpression
propertyJS e s = JSMemberDot e nil (identToJS s)

tagOfJS :: JSExpression -> JSExpression
tagOfJS = flip propertyJS "_tag"

eqJS :: JSBinOp
eqJS = JSBinOpEq nil

andJS :: JSBinOp
andJS = JSBinOpAnd nil

bigAndJS :: [JSExpression] -> JSExpression
bigAndJS [] = boolToJS True
bigAndJS [x] = x
bigAndJS (x:xs) = JSExpressionBinary x andJS $ bigAndJS xs

unopToJS :: Unop -> JSUnaryOp
unopToJS UMinus = JSUnaryOpMinus nil
unopToJS UNot = JSUnaryOpNot nil
unopToJS URef = error "unimplemented"
unopToJS UDeref = error "unimplemented"

binopToJS :: Binop -> JSBinOp
binopToJS BPlus = JSBinOpPlus nil
binopToJS BMinus = JSBinOpMinus nil
binopToJS BMult = JSBinOpTimes nil
binopToJS BDiv = JSBinOpDivide nil
binopToJS BEq = eqJS
binopToJS BNeq = JSBinOpNeq nil
binopToJS BLt = JSBinOpLt nil
binopToJS BLe = JSBinOpLe nil
binopToJS BGt = JSBinOpGt nil
binopToJS BGe = JSBinOpGe nil
binopToJS BAnd = andJS
binopToJS BOr = JSBinOpOr nil
binopToJS BUpdate = error "unimplemented"

unitJS :: JSExpression
unitJS = JSLiteral nil $ "null"

boolToJS :: Bool -> JSExpression
boolToJS b = JSLiteral nil $ toLower <$> show b

intToJS :: Integer -> JSExpression
intToJS i = JSLiteral nil $ show i

charToJS :: Char -> JSExpression
charToJS c = JSLiteral nil $ show c

stringToJS :: String -> JSExpression
stringToJS s = JSStringLiteral nil $ "'" ++ s ++ "'"

identToJS :: String -> JSExpression
identToJS s = JSIdentifier nil s

-- Translate a Term to a JSExpression.
termToJS :: Term α -> JSM JSExpression

termToJS (TmVar _ (Id x)) = do
  x' <- process_ident x
  return $ JSIdentifier space x'

termToJS (TmAbs _ (Id x) _ tm) = do
  x' <- process_ident x
  tm' <- termToJS tm
  return $ JSFunctionExpression space JSIdentNone nil
    (JSLOne $ JSIdentifier nil x') nil
    (JSBlock nil [mkReturn tm'] nil)

termToJS (TmApp _ tm1 tm2) = do
  tm1' <- termToJS tm1
  tm2' <- termToJS tm2
  return $ JSCallExpression tm1' nil (JSLOne tm2') nil

termToJS (TmUnit _) = return unitJS

termToJS (TmBool _ b) = return $ boolToJS b

termToJS (TmInt _ i) = return $ intToJS i

termToJS (TmChar _ c) = return $ charToJS c

termToJS (TmIf _ tm1 tm2 tm3) = do
  tm1' <- termToJS tm1
  tm2' <- termToJS tm2
  tm3' <- termToJS tm3
  return $ JSExpressionTernary tm1' nil tm2' nil tm3'

termToJS (TmUnop _ u tm) =
  pure (JSUnaryExpression $ unopToJS u) <*> termToJS tm

termToJS (TmBinop _ b tm1 tm2) = do
  tm1' <- termToJS tm1
  tm2' <- termToJS tm2
  let e = JSExpressionBinary tm1' (binopToJS b) tm2'
  case b of
    -- Use double tilde to do integer division.
    BDiv ->
      return $ JSUnaryExpression (JSUnaryOpTilde nil)
      (JSUnaryExpression (JSUnaryOpTilde nil) $ JSExpressionParen nil e nil)
    _ -> return e

termToJS (TmLet _ (Id x) tm1 tm2) = do
  x' <- process_ident x
  tm1' <- termToJS tm1
  tm2' <- termToJS tm2
  return $ JSCallExpression (JSFunctionExpression space JSIdentNone nil
                             (JSLOne $ JSIdentifier nil x') nil
                             (JSBlock nil [mkReturn tm2'] nil))
    nil (JSLOne tm1') nil


-- These don't appear in source programs, only in auto generated
-- constructor functions for the interpreter.
termToJS (TmVariant _ (Id x) tms) = error "termToJS: unexpected TmVariant"
  -- x' <- process_ident x
  -- tms' <- mapM termToJS tms
  -- return $ JSCallExpression (JSIdentifier nil "_mkVariant")
  --   nil (toJSCommaList $ (stringToJS x') : tms') nil


-- | TmMatch α (Term α) [(Pattern, Term α)]

-- patternJSBindings :: Pattern -> JSExpression -> [JSStatement]

termToJS (TmMatch _ discrim cases) = do
  x <- nextSym "_x"
  let patterns = fst <$> cases
  let predicates = patternJSPredicate <$> patterns
  bindings <- mapM (uncurry patternJSBindings) $
              zip patterns (repeat $ JSIdentifier nil x)
  discrim' <- termToJS discrim
  cases' <- mapM termToJS (snd <$> cases)

  return $ JSCallExpression
    (JSFunctionExpression space JSIdentNone nil
      (JSLOne $ JSIdentifier nil x) nil
      (JSBlock nil
       [
         mkCond discrim' $ zip3 predicates bindings cases'
       ]
       nil))
    nil (JSLOne discrim') nil
  where
    -- discriminee -> (predicate, binding statements, case body) ->
    -- if/else statement
    mkCond :: JSExpression ->
              [(JSExpression, [JSStatement], JSExpression)] ->
              JSStatement
    mkCond _ [] = mkReturn unitJS -- TODO: this should throw an error
    mkCond x ((predicate, bindings, body) : xs) =
      JSIfElse nil nil
      (JSCallExpression predicate nil (toJSCommaList [x]) nil) nil
      (JSStatementBlock nil (bindings ++ [mkReturn body]) nil JSSemiAuto) nil
      (JSStatementBlock nil [mkCond x xs] nil semi)


termToJS (TmRecord _ fields) = do
  fields' <- JSCTLNone . toJSCommaList <$>
    mapM (\(Id x, tm) -> do
             x' <- process_ident x
             tm' <- termToJS tm
             return $ JSPropertyNameandValue
               (JSPropertyIdent nil x') nil [tm']) fields
  return $ JSObjectLiteral nil fields' nil

termToJS tm@(TmPlaceholder _ _ _ _) =
  error $ "termToJS: unexpected placeholder: " ++ show tm


patternJSPredicate :: Pattern -> JSExpression
patternJSPredicate p =
  let body = go p (JSIdentifier nil "x") in
    JSFunctionExpression space JSIdentNone nil
    (JSLOne $ JSIdentifier nil "x") nil
    (JSBlock nil [mkReturn body] nil)
  where
    go :: Pattern -> JSExpression -> JSExpression
    go (PVar _) _ = JSLiteral nil $ "true"
    go PUnit e = JSExpressionBinary e eqJS unitJS
    go (PBool b) e = JSExpressionBinary e eqJS $ boolToJS b
    go (PInt i) e = JSExpressionBinary e eqJS $ intToJS i
    go (PChar c) e = JSExpressionBinary e eqJS $ charToJS c
    go (PPair p1 p2) e =
      JSExpressionBinary
      (JSExpressionBinary (tagOfJS e) eqJS (stringToJS "Pair"))
      andJS $
      JSExpressionBinary (go p1 $ indexJS e 0) andJS (go p2 $ indexJS e 1)
    go (PConstructor (Id x) ps) e =
      JSExpressionBinary
      (JSExpressionBinary (tagOfJS e) eqJS (stringToJS x))
      andJS $
      bigAndJS (uncurry go <$> zip ps (indexJS e <$> [0..]))
    go (PRecord fields) e =
      bigAndJS (uncurry (flip go) <$>
                first (propertyJS e . unId) <$> fields)


patternJSBindings :: Pattern -> JSExpression -> JSM [JSStatement]
patternJSBindings (PVar (Id x)) e = do
  x' <- process_ident x
  return [mkVarStmt x' e]
patternJSBindings PUnit _ = return []
patternJSBindings (PBool _) _ = return []
patternJSBindings (PInt _) _ = return []
patternJSBindings (PChar _) _ = return []
patternJSBindings (PPair p1 p2) e = do
  s1 <- patternJSBindings p1 $ indexJS e 0
  s2 <- patternJSBindings p2 $ indexJS e 1
  return $ s1 ++ s2
patternJSBindings (PConstructor _ ps) e =
  concat <$> (mapM (\(p, i) -> patternJSBindings p $ indexJS e i) $
              zip ps [0..])
patternJSBindings (PRecord fps) e = undefined
  -- concat $ (undefined) <$> fps


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

mkVarStmt :: String -> JSExpression -> JSStatement
mkVarStmt x e =
  JSVariable nil
  (toJSCommaList
    [JSVarInitExpression (JSIdentifier space x) (JSVarInit nil e)])
  semi

commandToJS :: Command α -> JSM [JSStatement]

commandToJS (CDecl _ _ _) = return []

commandToJS (CLet _ (Id x) tm) = do
  x' <- process_ident x
  tm' <- termToJS tm
  return [mkVarStmt x' tm']

commandToJS (CEval _ tm) = do
  tm' <- termToJS tm
  -- return [JSExpressionStatement tm' semi]
  return [JSExpressionStatement
          (JSCallExpression (JSMemberDot (JSIdentifier nil "console")
                             nil (JSIdentifier nil "log")) nil
            (JSLOne $ tm') nil) semi]

commandToJS (CCheck _ _) = return []

commandToJS (CData _ _ _ ctors) = do
  mapM (\((Id x), tys) -> do
           x' <- process_ident x
           if length tys > 0 then do
             let args = (:[]) <$> take (length tys) ['a'..]
             return $ mkVarStmt x'
               (mkCurriedJS args $
                 JSBlock nil
                 [mkVarStmt "x"
                  (JSArrayLiteral nil
                    (intersperse (JSArrayComma nil) $
                      JSArrayElement . JSIdentifier nil <$> args) nil),
                   JSAssignStatement (JSMemberDot (JSIdentifier nil "x")
                                      nil (JSIdentifier nil "_tag"))
                   (JSAssign nil) (stringToJS x') semi,
                   mkReturn $ JSIdentifier nil "x"] nil)
             else
             return $ mkVarStmt x'
             (JSObjectLiteral nil
               (JSCTLNone $ toJSCommaList
                [JSPropertyNameandValue (JSPropertyIdent nil "_tag") nil
                 [stringToJS x']]) nil)
       )
    ctors

commandToJS (CRecord _ _ _ fields) = do
  mapM (\(Id x, _) -> do
           x' <- process_ident x
           return $ mkVarStmt x' (  JSFunctionExpression space JSIdentNone nil
               (JSLOne $ JSIdentifier nil "x") nil
               (JSBlock nil [JSReturn nil
                             (Just $ JSMemberDot (JSIdentifier nil "x")
                              nil (JSIdentifier nil x'))
                              semi] nil)
                                 )) fields

commandToJS (CAssert _ tm) = undefined -- TODO

commandToJS (CClass _ _ _ _ _) = return []

commandToJS (CInstance _ _ _ _ _) = return []


-- Given a list of argument names and a function body, build a curried
-- JS function (a series of nested single-argument functions). Assumes
-- the strings have already been checked for hygiene.
mkCurriedJS :: [String] -> JSBlock -> JSExpression
mkCurriedJS [] _ = error "mkCurriedJS: expected at least one argument"
mkCurriedJS [x] body =
  JSFunctionExpression space JSIdentNone nil
  (JSLOne $ JSIdentifier nil x) nil body
mkCurriedJS (x:xs) body =
  JSFunctionExpression space JSIdentNone nil
    (JSLOne $ JSIdentifier nil x) nil
    (JSBlock nil [mkReturn $ mkCurriedJS xs body] nil)  


-- data Command α =
--   CDecl α Id Type
--   | CLet α Id (Term α)
--   | CEval α (Term α)
--   | CCheck α (Term α)
--   | CData α Id [Id] [(Id, [Type])]
--   | CRecord α Id [Id] [(Id, Type)]
--   | CAssert α (Term α)
--   -- constraints, class name, class type variable, method names and types
--   | CClass α [ClassNm] ClassNm Id [(Id, Type)]
--   -- constraints, class name, instance type, method names and definitions
--   | CInstance α [(Id, ClassNm)] ClassNm Type [(Id, Term α)]
--   deriving (Functor, Generic)


commandsToJS :: [Command α] -> JSM [JSStatement]
commandsToJS coms = do
  stmts <- mapM commandToJS coms
  return $ concat stmts


compileJS :: String -> [Command α] -> String
compileJS preamble coms =
  let js_prog = runJSM (commandsToJS coms) (0, Map.empty)
      out_src =
        intercalate "\n"
        (renderToString . (flip JSAstStatement JSNoAnnot) <$> js_prog)
  in
    preamble ++ out_src
