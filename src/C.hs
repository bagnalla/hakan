{-# LANGUAGE LambdaCase #-}

module C (compileProg) where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

import Data.Bifunctor (bimap, first, second)
import Data.Foldable (foldrM)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Sort (sortOn)
import Data.Tuple (swap)

import Text.PrettyPrint

import Language.C.Data.Ident hiding (mkIdent)
import Language.C.Data.Node
import Language.C.Syntax.AST as C
import Language.C.Syntax.Constants
import Language.C.Pretty

import Ast (Binop(..), Command(..), data_of_term, isAssertCommand, nameOfVariant,
             isEvalCommand, isTypeCommand, isSuperCombinator, tagOfConstructor,
             nameOfRecord, returnType, tysubst', mkTyVar, applyTypeConstructor,
             instantiated,
             Pattern(..), Prog(..), Term(..), Type(..), TypeConstructor(..),
             Unop(..))
import Context (normalize_ty)       
import LambdaLift (lambdaLiftProg)
import Symtab (Id(..))
import Tycheck (TyData(..))
import Util (debugPrint, dup, mapFstM, orf)

-- Mapping of hakan types to C types:
-- Lift all functions to top-level supercombinators. The runtime value of a function is a struct containing an array of arguments, the number of arguments already present, and a pointer to the compiled body.
-- unit goes to NULL
-- bool goes to int*
-- int goes to int*
-- char goes to char*
-- ref T goes to T*
-- variant goes to pointer to tagged union with integer tags
-- record goes to pointer to struct

-- All values are boxed to make polymorphism easy.

-- Type variables (polymorphic occurrences) map to uintptr_t and will
-- need to be casted when used.

-- Every user-declared type will be declared as a c struct at the top. Variant types have an integer tag associated with each constructor, and records have a fixed ordering of fields

----------------------------------
-- | Translation of variant types:

-- data T a =
--   | C1 Int Bool
--   | C2 a

-- =>

-- typedef struct {
--   int x0;
--   bool x1;
-- } T_C1;

-- typedef struct {
--   uintptr_t x0;
-- } T_C2;

-- typedef struct {
--   int tag;
--   union {
--     T_C1 C1;
--     T_C2 C2;
--   };
-- } T;

-- C[T] = T*

-- where the names T_C1 and T_C2 are guaranteed to be unique. Perhaps
-- we should just disallow underscores in hakan types to make this
-- easy. This is being checked in the typechecker for now (underscores
-- in variant and record type names).

---------------------------------
-- | Translation of record types:

-- record Person a =
--   { age  : Int
--   , male : Bool
--   , meta : a }

-- =>

-- typedef struct {
--   int age;
--   int bool male;
--   uintptr_t a;
-- } Person;

-- C[Person] = Person*

--------------------------------------
-- | Translation of mutable references

-- typedef struct {
--   uintptr_t *ptr;
-- } ref;

-- C[TyRef] = ref*

----------------------------------------
-- | Type of runtime value of functions.

-- typedef struct {
--   int n;
--   uintptr_t args[];
--   uintptr_t (*fun_ptr)(uintptr_t[]);
-- } thunk;

-- Easy way is to just use a uniform type interface for all functions
-- (using a single array argument) and perform casting wherever
-- necessary within the bodies of functions and at
-- call-sites. However, this is inefficient since it fails to take
-- advantage of register-passing calling conventions and requires
-- indirect access to arguments. We could maybe instead use some
-- inline assembly for our calling routine in order to circumvent C's
-- type system and let us call an arbitrary function passing the
-- arguments however we want, but maybe that would be more complicated
-- than I realize (starting to imagine now..).

-- Arguments are reversed so application can proceed by just writing
-- into args[0] and then calling fun_ptr (since all thunks are already
-- partially applied to all by one argument).

----------------------------------------

data CState =
  CState { gensym :: Int
         , names :: Map.Map String String
         , type_names :: Map.Map String String
         , main_coms :: [Command TyData]
         , ctor_tags :: Map.Map String Integer }

initCState :: CState
initCState = CState { gensym = 0
                    , names = Map.empty
                    , type_names = Map.empty
                    , main_coms = []
                    , ctor_tags = Map.empty }

data CContext =
  CContext { locals :: Map.Map String (Either Integer String) }

initCContext :: CContext
initCContext = CContext { locals = Map.empty }

type CM a = ReaderT CContext (StateT CState Identity) a

runCM :: CM a -> CContext -> CState -> a
runCM f ctx s = runIdentity $ evalStateT (runReaderT f ctx) s

getTag :: String -> CM Integer
getTag nm = do
  tags <- gets ctor_tags
  -- debugPrint ("tags: " ++ show tags) $
  case Map.lookup nm tags of
    Just i -> return i
    Nothing -> error $ "getTag: unbound tag " ++ nm

-- remove_underscores :: String -> String
-- remove_underscores = dropWhile (== '_')

nextSym :: String -> CM String
nextSym prefix = do
  i <- gets gensym
  modify $ \s -> s { gensym = i + 1 }
  return $ prefix ++ show i

freshVar :: CM String
freshVar = nextSym "_x"

-- C reserved strings (not to be used as identifiers in the generated program).
reserved :: [String]
reserved =
  ["printf", "exit", "thunk", "args", "ref",
    "GC_malloc", "uintptr_t", "auto", "break", "case", "char", "const",
   "continue", "default", "do", "double", "else", "enum", "extern",
   "float", "for", "goto", "if", "inline", "int", "long", "register",
   "restrict", "return", "short", "signed", "sizeof", "static",
   "struct", "switch", "typedef", "union", "unsigned", "void",
   "volatile", "while", "_Alignas", "_Alignof", "_Atomic", "_Bool",
   "_Complex", "_Generic", "_Imaginary", "_Noreturn", "_Static_assert",
   "_Thread_local", "_Pragma", "asm", "fortran"]

nil :: NodeInfo
nil = undefNode

mkIntConst :: Integer -> CExpr
mkIntConst i = CConst $ CIntConst (CInteger i DecRepr noFlags) nil

mkBoolConst :: Bool -> CExpr
mkBoolConst b = mkIntConst $ if b then 1 else 0

mkCharConst :: Char -> CExpr
mkCharConst c = CConst $ CCharConst (CChar c False) nil

mkStringConst :: String -> CExpr
mkStringConst s = CConst $ CStrConst (CString s False) nil

mkIdent :: String -> Ident
mkIdent x = Ident x 0 undefNode

mkVar :: String -> CExpr
mkVar x = CVar (mkIdent x) nil

varToC :: Id -> CExpr
varToC (Id x) = CVar (mkIdent x) nil

unopToC :: Unop -> CUnaryOp
unopToC UMinus = CMinOp
unopToC UNot   = CNegOp
unopToC _ = error "unimplemented unary operator"
-- TODO: treat URef and UDeref unary operations specially in the TmUnop case

binopToC :: Binop -> CBinaryOp
binopToC BPlus  = CAddOp
binopToC BMinus = CSubOp
binopToC BMult  = CMulOp
binopToC BDiv   = CDivOp
binopToC BEq    = CEqOp
binopToC BNeq   = CNeqOp
binopToC BLt    = CLeOp
binopToC BLe    = CLeqOp
binopToC BGt    = CGrOp
binopToC BGe    = CGeqOp
binopToC BAnd   = CLndOp
binopToC BOr    = CLorOp
binopToC BUpdate = error "unimplemented binary operator"
-- TODO: treat reference updates specially in the TmBinop case

typeToC :: Type -> (CTypeSpecifier NodeInfo, [CDerivedDeclarator NodeInfo])
typeToC = go . normalize_ty
  where go = \case
          TyVar _ _ _ _ -> (CTypeDef (mkIdent "uintptr_t") nil, [])
          TyAbs _ _ _ -> error "typeToC: unexpected TyAbs"
          TyApp (TyName _) t -> (CTypeDef (mkIdent "uintptr_t") nil, [])
          TyApp s t -> error $ "unexpected TyApp. s: " ++
                       show s ++ ", t: " ++ show t
          TyUnit -> (CIntType nil, [])
          TyBool -> (CIntType nil, [])
          TyInt -> (CIntType nil, [])
          TyChar -> (CCharType nil, [])
          TyArrow s t ->
            (CTypeDef (mkIdent "thunk") nil, [CPtrDeclr [] nil])
          TyRef t ->
            -- let (ct, ds) = typeToC t in (ct, ds ++ [CPtrDeclr [] nil])
            (CTypeDef (mkIdent "ref") nil, [CPtrDeclr [] nil])
          TyName (Id nm) -> (CTypeDef (mkIdent nm) nil, [CPtrDeclr [] nil])
          TyVariant (Id nm) _ _ -> (CTypeDef (mkIdent nm) nil,
                                     [CPtrDeclr [] nil])
          TyRecord (Id nm) _ _ -> (CTypeDef (mkIdent nm) nil, [CPtrDeclr [] nil])
          TyConstructor (TypeConstructor { tycon_instantiated = ty }) ->
            typeToC ty
  

-- Declare a variable with no initial value.
mkVarDecl :: Type -> String -> CDeclaration NodeInfo
mkVarDecl ty x =
  let (ct, ds) = typeToC ty in
    C.CDecl [(CTypeSpec ct)]
    [(Just $ CDeclr (Just $ mkIdent x) ds Nothing [] nil,
       Nothing, Nothing)] nil

-- Declare and initialize a variable.
mkVarDeclAssign :: Type -> String -> CExpr -> CDeclaration NodeInfo
mkVarDeclAssign ty x e =
  let (ct, ds) = typeToC ty in
    C.CDecl [(CTypeSpec ct)]
    [(Just $ CDeclr (Just $ mkIdent x) ds Nothing [] nil,
      Just $ CInitExpr e nil, Nothing)] nil

mkAssign :: CExpr -> CExpr -> CStatement NodeInfo
mkAssign e1 e2 = CExpr (Just $ CAssign CAssignOp e1 e2 nil) nil

-- Assign to an already declared variable.
mkVarAssign :: String -> CExpr -> CStatement NodeInfo
mkVarAssign x e = mkAssign (mkVar x) e

mkMalloc :: CExpr -> CExpr
mkMalloc e = CCall (mkVar "GC_malloc") [e] nil

mkMalloc' :: Type -> CExpr
mkMalloc' ty =
  let (ct, ds) = typeToC ty in
    mkMalloc $ CSizeofType (C.CDecl [CTypeSpec ct]
                            [(Just $ CDeclr Nothing ds Nothing [] nil,
                              Nothing, Nothing)] nil) nil

mkBigAnd :: [CExpr] -> CExpr
mkBigAnd [] = mkBoolConst True
mkBigAnd [e] = e
mkBigAnd (e:es) = CBinary CLndOp e (mkBigAnd es) nil

argsDecl :: CDeclaration NodeInfo
argsDecl = C.CDecl [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil]
           [(Just $ CDeclr (Just $ mkIdent "args")
             [CArrDeclr [] (CNoArrSize False) nil] Nothing [] nil,
             Nothing, Nothing)] nil

fnTypeDecl :: CDeclaration NodeInfo
fnTypeDecl = C.CDecl [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil]
             [(Just $ CDeclr Nothing
               [CPtrDeclr [] nil,
                 CFunDeclr (Left [mkIdent "uintptr_t[]"]) [] nil]
                Nothing [] nil,
                Nothing, Nothing)] nil

mkTypeDecl :: CTypeSpecifier NodeInfo
           -> [CDerivedDeclarator NodeInfo]
           -> CDeclaration NodeInfo
mkTypeDecl ct ds =
  C.CDecl [CTypeSpec ct]
  [(Just $ CDeclr Nothing ds Nothing [] nil, Nothing, Nothing)] nil
  
thunkDecl :: String -> CDeclaration NodeInfo
thunkDecl s = 
  let decl1 = C.CDecl [CTypeSpec $ CTypeDef (mkIdent "thunk") nil]
              [] nil in
    C.CDecl [CTypeSpec $ CTypeDef (mkIdent "thunk") nil]
    [(Just $ CDeclr (Just $ mkIdent s) [CPtrDeclr [] nil] Nothing [] nil,
       Nothing, Nothing)] nil

thunkDeclMalloc :: String -> CDeclaration NodeInfo
thunkDeclMalloc s = 
  let decl1 = C.CDecl [CTypeSpec $ CTypeDef (mkIdent "thunk") nil]
              [] nil in
    C.CDecl [CTypeSpec $ CTypeDef (mkIdent "thunk") nil]
    [(Just $ CDeclr (Just $ mkIdent s) [CPtrDeclr [] nil] Nothing [] nil,
       Just $ CInitExpr (mkMalloc $ CSizeofType decl1 nil) nil,
       Nothing)] nil

genericDecl :: CDeclaration NodeInfo
genericDecl = C.CDecl [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil] [] nil

-- Deep copy.
copyThunk :: CExpr -> CExpr -> [CStatement NodeInfo]
copyThunk s t =
  [CExpr (Just $ CCall (mkVar "memcpy")
          [t, s,
           CSizeofType
           (C.CDecl [CTypeSpec $ CTypeDef (mkIdent "thunk") nil] [] nil) nil]
           nil) nil,
   mkAssign (CMember t (mkIdent "args") True nil)
    (mkMalloc $ CBinary CMulOp
      (CSizeofType
        (C.CDecl
          [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil] [] nil) nil)
      (CMember s (mkIdent "n") True nil) nil),
    CExpr (Just $ CCall (mkVar "memcpy")
           [CMember t (mkIdent "args") True nil,
            CMember s (mkIdent "args") True nil,
            CBinary CMulOp
            (CSizeofType
             (C.CDecl
              [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil] [] nil) nil)
            (CMember s (mkIdent "n") True nil) nil] nil) nil
    ]

lookupVar :: String -> CM CExpr
lookupVar x = do
  ctx <- asks locals
  case Map.lookup x ctx of
    Just (Left ix) -> return $ CIndex (mkVar "args") (mkIntConst ix) nil
    Just (Right y) -> return $ mkVar y
    Nothing -> return $ mkVar x

-- compileTerm t e generates a list of statements that assigns the
-- value of t to expression e.
compileTerm :: Term TyData -> CExpr -> CM ([CCompoundBlockItem NodeInfo])
compileTerm (TmVar (TyData ty) (Id x)) res = do
  e <- lookupVar x
  let (ct, ds) = typeToC ty
  return [CBlockStmt $ mkAssign res $ CCast (mkTypeDecl ct ds) e nil]
  
compileTerm (TmAbs _ _ _ _) _ = error "compileTerm: unexpected TmAbs"

compileTerm (TmApp (TyData ty) t1 t2) res = do
  new_thunk <- freshVar
  (x1, x2) <- liftM2 (,) freshVar freshVar
  s1 <- compileTerm t1 $ mkVar x1
  s2 <- compileTerm t2 $ mkVar x2
  let (ct, ds) = typeToC ty
  return $
    [CBlockDecl $ mkVarDecl (unTyData $ data_of_term t1) x1,
     CBlockDecl $ mkVarDecl (unTyData $ data_of_term t2) x2] ++
    s1 ++ s2 ++
    [CBlockDecl $ thunkDeclMalloc new_thunk] ++
    (CBlockStmt <$> (copyThunk (mkVar x1) $ mkVar new_thunk)) ++
    [CBlockStmt $ mkAssign
      (CIndex (CMember (mkVar new_thunk) (mkIdent "args") True nil)
        (mkIntConst 0) nil) (CCast genericDecl (mkVar x2) nil),
     CBlockStmt $ mkAssign res
      (CCast (mkTypeDecl ct ds)
        (CCall (CMember (mkVar new_thunk) (mkIdent "fun_ptr") True nil)
          [CMember (mkVar new_thunk) (mkIdent "args") True nil] nil) nil)]

compileTerm (TmUnit _) res = return [CBlockStmt $ mkAssign res $ mkIntConst 0]
compileTerm (TmBool _ b) res = return [CBlockStmt $ mkAssign res $ mkBoolConst b]
compileTerm (TmInt _ i) res = return [CBlockStmt $ mkAssign res $ mkIntConst i]
compileTerm (TmChar _ c) res = return [CBlockStmt $ mkAssign res $ mkCharConst c]
compileTerm (TmIf _ t1 t2 t3) res = do
  x1 <- freshVar
  x2 <- freshVar
  x3 <- freshVar
  s1 <- compileTerm t1 $ mkVar x1
  s2 <- compileTerm t2 $ mkVar x2
  s3 <- compileTerm t3 $ mkVar x3
  let TyData ty2 = data_of_term t2
  return $
    (CBlockDecl $ mkVarDecl (unTyData $ data_of_term t1) x1) :
    s1 ++
    [CBlockStmt $
      CIf (mkVar x1) (CCompound []
               ((CBlockDecl $ mkVarDecl (unTyData $ data_of_term t2) x2) :
                 s2 ++ [CBlockStmt $ mkAssign res $ mkVar x2]) nil)
      (Just $ (CCompound []
                ((CBlockDecl $ mkVarDecl (unTyData $ data_of_term t3) x3) :
                  s3 ++ [CBlockStmt $ mkAssign res $ mkVar x3]) nil)) nil]
  
    
compileTerm (TmUnop (TyData ty) u tm) res = do
  s <- compileTerm tm res
  case u of
    URef ->
      return $ s ++
      [CBlockStmt $ mkAssign res $ mkMalloc' ty]
    UDeref -> undefined
    _ -> return $ s ++ [CBlockStmt $ mkAssign res $ CUnary (unopToC u) res nil]
compileTerm (TmBinop ty b t1 t2) res = do
  (x1, x2) <- liftM2 (,) freshVar freshVar
  s1 <- compileTerm t1 $ mkVar x1
  s2 <- compileTerm t2 $ mkVar x2
  case b of
    BUpdate -> undefined
    _ -> return $ [CBlockDecl $ mkVarDecl (unTyData $ data_of_term t1) x1,
                   CBlockDecl $ mkVarDecl (unTyData $ data_of_term t2) x2] ++
         s1 ++ s2 ++
         [CBlockStmt $ mkAssign res $
          CBinary (binopToC b) (mkVar x1) (mkVar x2) nil]
compileTerm (TmLet ty (Id x) t1 t2) res = do
  s1 <- compileTerm t1 $ mkVar x
  local (\ctx -> ctx { locals = Map.insert x (Right x) $ locals ctx }) $ do
    s2 <- compileTerm t2 res
    let TyData ty1 = data_of_term t1
    return $ (CBlockDecl $ mkVarDecl ty1 x) : s1 ++ s2

compileTerm (TmVariant (TyData ty) (Id nm) tms) res = do
  xs <- mapM (const freshVar) tms
  let es = mkVar <$> xs
  ss <- mapM (uncurry compileTerm) $ zip tms es
  debugPrint "\ncompiling TmVariant" $
    debugPrint ("nm: " ++ show nm) $ do
    return $
      -- Declare xs.
      (map (\(x, TyData tp) ->
              CBlockDecl $ mkVarDecl tp x) $
       zip xs (data_of_term <$> tms)) ++
      -- Assign values to xs.
      concat ss ++
      -- Allocate memory for result.
      [CBlockStmt $ mkAssign res $ mkMalloc' ty,
       -- Assign its constructor tag.
       CBlockStmt $ mkAssign (CMember res (mkIdent "tag") True nil)
       (mkIntConst $ toInteger $ tagOfConstructor (instantiated ty) $
         Id nm),
       -- Assign fields of member struct for constructor.
       CBlockStmt $ mkAssign (CMember res (mkIdent nm) True nil)
       (CCompoundLit (C.CDecl
                       [CTypeSpec $
                        CTypeDef (mkIdent $ unId
                                  (nameOfVariant $ instantiated ty) ++ nm) nil]
                       [] nil)
         (map (\(i, e) -> ([CMemberDesig (mkIdent $ "x" ++ show i) nil],
                            CInitExpr e nil)) $ zip [0..] es)
         nil)]

compileTerm (TmMatch (TyData ty) tm cases) res = do
  discrim_x <- freshVar
  let discrim_e = mkVar discrim_x
  discrim_s <- compileTerm tm discrim_e
  let variant_ty = instantiated $ unTyData $ data_of_term tm
  -- Build nested conditionals for all of the cases, with the final
  -- default case being an empty compound statement.
  if_stmt <- foldrM
    (\(p, t) acc -> do
        condition_expr <- patternPred p discrim_e
        bindings <- patternBindings variant_ty p discrim_e
        debugPrint ("\npattern: " ++ show p) $
          debugPrint ("variant_ty: " ++ show variant_ty) $
          debugPrint ("bindings: " ++ show bindings) $ do
          s <- compileTerm t res
          return $ CIf condition_expr
            (CCompound [] (bindings ++ s) nil)
            (Just acc) nil)
    (CCompound [] [] nil) cases
  return $ (CBlockDecl $ mkVarDecl variant_ty discrim_x) :
    discrim_s ++ [CBlockStmt if_stmt]

compileTerm (TmRecord (TyData ty) fields) res = do
  xs <- mapM (const freshVar) fields
  let es = mkVar <$> xs
  ss <- mapM (uncurry compileTerm) $ zip (snd <$> fields) es
  return $
    -- Declare xs.
    (map (\(x, TyData tp) ->
             CBlockDecl $ mkVarDecl tp x) $
      zip xs (data_of_term . snd <$> fields)) ++
    concat ss ++
      -- Allocate memory for res.
      [CBlockStmt $ mkAssign res $ mkMalloc' ty,
       -- Assign struct literal to res.
       CBlockStmt $ mkAssign (CUnary CIndOp res nil)
        (CCompoundLit (C.CDecl [CTypeSpec $
                                CTypeDef (mkIdent $ unId $
                                          nameOfRecord $ instantiated ty) nil
                               ]
                        [] nil)
          (map (\(Id x, e) -> ([CMemberDesig (mkIdent x) nil],
                                CInitExpr e nil)) $
            zip (fst <$> fields) es)
          nil)]

compileTerm (TmThunk _ (Id nm) args) res = do
  -- debugPrint ("\ncompiling TmThunk " ++ nm) $
  -- debugPrint ("args: " ++ show args) $ do
  x <- freshVar
  arg_assigns <- mapM (\(i, (Id arg, _)) -> do
                         e <- lookupVar arg
                         return $ CBlockStmt $ mkAssign
                           (CIndex (CMember res (mkIdent "args") True nil)
                            (mkIntConst i) nil)
                           (CCast genericDecl e nil)) $
                 zip [1..] args
  return $ [CBlockDecl $ thunkDeclMalloc x,
            CBlockStmt $ mkAssign res (mkVar x),
            CBlockStmt $ mkAssign (CUnary CIndOp res nil)
             (CCompoundLit
              (C.CDecl [CTypeSpec $
                        CTypeDef (mkIdent "thunk") nil] [] nil)
              [([], CInitExpr (mkIntConst $ toInteger $ length args + 1) nil),
               ([], CInitExpr (mkMalloc $ CBinary CMulOp
                               (CSizeofType
                                (C.CDecl
                                 [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil] [] nil) nil)
                               (mkIntConst $ toInteger $ length args + 1) nil) nil),
               ([], CInitExpr (CCast fnTypeDecl (CUnary CAdrOp (mkVar nm) nil) nil) nil)]
              nil)] ++ arg_assigns

compileTerm tm _ = error $ "compileTerm: unsupported term " ++ show tm

-- Given pattern p and C expression e, generate a boolean expression
-- that evaluates to true whenever p matches e.
patternPred :: Pattern -> CExpr -> CM CExpr
patternPred (PVar _) _ = return $ mkBoolConst True
patternPred PUnit _ = return $ mkBoolConst True -- always true if well-typed
patternPred (PBool b) e = return $ CBinary CEqOp (mkBoolConst b) e nil
patternPred (PInt i) e = return $ CBinary CEqOp (mkIntConst i) e nil
patternPred (PChar c) e = return $ CBinary CEqOp (mkCharConst c) e nil
patternPred (PPair p1 p2) e =
  pure (CBinary CLndOp) <*>
  patternPred p1 (CMember (CMember e (mkIdent "x0") True nil)
                   (mkIdent "x0") False nil) <*>
  patternPred p2 (CMember (CMember e (mkIdent "x0") True nil)
                   (mkIdent "x1") False nil) <*>
  pure nil
patternPred (PConstructor (Id nm) ps) e = do
  tag <- getTag nm
  conds <- forM (zip [0..] ps) $ \(i, p) -> patternPred p $
    CMember e (mkIdent $ "x" ++ show i) False nil
  return $ mkBigAnd $ CBinary CEqOp (CMember e (mkIdent "tag") True nil)
    (mkIntConst tag) nil : conds
patternPred (PRecord fields) e = do
  mkBigAnd <$> (forM fields $ \(Id x, p) ->
                   patternPred p $ CMember e (mkIdent x) True nil)

-- Given a pattern p and expression e, generate a list of statements
-- that bind variables occurring in the pattern to their corresponding
-- constituent parts of e.
patternBindings :: Type -- Type of pattern expression
                -> Pattern
                -> CExpr
                -> CM [CCompoundBlockItem NodeInfo]
patternBindings _ (PVar (Id "_")) _ = return []
patternBindings ty (PVar (Id x)) e = debugPrint ("\nPVar " ++ show x) $ do
  let (ct, ds) = typeToC ty
  return [CBlockDecl $ mkVarDeclAssign ty x $ CCast (mkTypeDecl ct ds) e nil]
patternBindings (TyVariant _ [s, t] _) (PPair p1 p2) e = do
  cs1 <- patternBindings s p1 $
    CMember (CMember e (mkIdent "Pair") True nil) (mkIdent "x0") False nil
  cs2 <- patternBindings t p2 $
    CMember (CMember e (mkIdent "Pair") True nil) (mkIdent "x1") False nil
  return $ cs1 ++ cs2  
patternBindings (TyVariant _ _ ctors) (PConstructor (Id nm) ps) e = do
  tag <- getTag nm
  let tys = fromJust $ lookup (Id nm) ctors
  cs <- forM (zip3 [0..] tys ps) $ \(i, ty, p) ->
    patternBindings ty p $ CMember (CMember e (mkIdent $ nm) True nil)
    (mkIdent ("x" ++ show i)) False nil
  return $ concat cs
patternBindings (TyRecord _ _ field_tys) (PRecord fields) e =
  concat <$> (forM (zip fields $ snd <$> field_tys) $ \((Id x, p), ty) ->
                 patternBindings ty p $ CMember e (mkIdent x) True nil)
patternBindings _ _ _ = return []

mkCFun :: String -- function name
       -> CStatement NodeInfo -- function body
       -> CFunDef
mkCFun nm body =
    CFunDef [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil]
    (CDeclr (Just $ mkIdent nm)
      ([CFunDeclr (Right $ ([argsDecl], False)) [] nil]) Nothing [] nil)
    [] body nil

-- Generate declarations and definitions for supercombinators and type
-- definitions for variant and record commands, doing nothing for
-- other commands but storing eval and assert commands in main_coms to
-- be run in the main. For any supercombinator with zero parameters (a
-- CAF), create an uninitialized declaration and store the command in
-- main_coms so the RHS can be evaluated in the main.
compileCommand :: Command TyData -> CM [CExternalDeclaration NodeInfo]
compileCommand = \case
  c@(CEval _ _) -> do
    modify $ \s -> s { main_coms = main_coms s ++ [c] }
    return []
  
  c@(CSuperCombinator (TyData ty) (Id nm) [] body) -> do
    modify $ \s -> s { main_coms = main_coms s ++ [c] }
    let (ct, ds) = typeToC ty
    -- Uninitialized declaration.
    return [CDeclExt $ C.CDecl [CTypeSpec ct]
            [(Just $ CDeclr (Just $ mkIdent nm) ds Nothing [] nil,
              Nothing, Nothing)] nil]
  CSuperCombinator (TyData ty) (Id nm) params body ->
    -- debugPrint ("compiling supercombinator " ++ show nm) $
    --   debugPrint ("params: " ++ show params) $
    --   debugPrint ("body: " ++ show body) $
      local (\ctx -> ctx { locals =
                         Map.union (Map.fromList $ zip (unId . fst <$> params)
                                     (Left <$> [0..])) $
                         locals ctx }) $ do
      res <- freshVar
      s <- compileTerm body $ mkVar res
      let (ct, ds) = typeToC $ returnType ty
      -- debugPrint ("compiling supercombinator " ++ show nm) $
      --   debugPrint ("ty: " ++ show ty) $
      --   debugPrint ("ct: " ++ show ct) $
      --   debugPrint ("ds: " ++ show ds) $
      --   debugPrint ("params: " ++ show params) $ do
      return
          [CDeclExt $ C.CDecl [CTypeSpec $ CTypeDef (mkIdent "uintptr_t") nil]
           [(Just $ CDeclr (Just $ mkIdent nm)
              ([CFunDeclr (Right ([argsDecl], False))
                  [] nil]) Nothing [] nil, Nothing, Nothing)] nil,
            -- Definition.
            CFDefExt $ mkCFun nm
            (CCompound [] ((CBlockDecl $ mkVarDecl (returnType ty) res) :
                           s ++ [CBlockStmt $ CReturn
                                 (Just $ CCast genericDecl (mkVar res) nil) nil]) nil)]

  CData (TyData ty) (Id nm) typarams ctors -> do
    -- Register constructor tags.
    modify $ \s -> s { ctor_tags =
                       Map.union (Map.fromList $
                                  zip (unId . fst <$> ctors) [0..]) $
                       ctor_tags s }

    let constructorDecls = map (uncurry mkConstructorStructDecl) $
                           first ((nm ++) . unId) <$> ctors

    return $
      (CDeclExt $
       mkStructOrUnionDecl True CStructTag (Just nm) (Just nm) Nothing) :
      constructorDecls ++
      [CDeclExt $ mkVariantDeclaration nm $
        first (nm ++) . dup . unId . fst <$> ctors]

  CRecord (TyData ty) (Id nm) typarams fields ->
    debugPrint "compiling CRecord" $
    debugPrint ("ty: " ++ show ty) $ do
    return $ [CDeclExt $ mkStructOrUnionDecl True CStructTag Nothing (Just nm)
               (Just $ map (\(Id x, ty) -> mkVarDecl ty x) fields)]
  _ -> return []

mkConstructorStructDecl :: String -- qualified name
                        -> [Type] -- argument types
                        -> CExternalDeclaration NodeInfo
mkConstructorStructDecl nm arg_tys =
  CDeclExt $
  (mkStructOrUnionDecl True CStructTag Nothing (Just nm) $ Just $
   map (\(i, ty) ->
          let (ct, ds) = typeToC ty in
            -- debugPrint "mkConstructorStructDecl" $
            -- debugPrint ("ty: " ++ show ty) $
            -- debugPrint ("ct: " ++ show ct) $
            -- debugPrint ("ds: " ++ show ds) $
            C.CDecl [CTypeSpec ct]
            [(Just $ CDeclr (Just $ mkIdent $ "x" ++ show i) ds Nothing [] nil,
              Nothing, Nothing)] nil) $ zip [0..] arg_tys)

-- mkConstructorFunction :: Type -- variant type
--                       -> String -- constructor name
--                       -> [Type] -- argument types
--                       -> CM ([CExternalDeclaration NodeInfo])
-- mkConstructorFunction variant_ty ctor_nm [] = do
--   modify $ \s -> s { main_coms = main_coms s ++
--                      [CSuperCombinator (TyData variant_ty) (Id ctor_nm) [] $
--                        TmVariant (TyData variant_ty) (Id ctor_nm) []] }
--   return [CDeclExt $ mkVarDecl variant_ty ctor_nm]
-- mkConstructorFunction variant_ty ctor_nm arg_tys =
--   let (variant_ct, variant_ds) = typeToC variant_ty in do
--     nm <- nextSym "_C"
--     modify $ \s -> s { main_coms = main_coms s ++
--                        [CSuperCombinator (TyData variant_ty) (Id ctor_nm) [] $
--                         TmThunk (TyData variant_ty) (Id nm) []] }
--     res <- freshVar
--     arg_vars <- mapM (const freshVar) arg_tys
--     local (\ctx -> ctx { locals =
--                          Map.union (Map.fromList $ zip arg_vars (Left <$> [0..])) $
--                          locals ctx }) $ do
--       s <- compileTerm (TmVariant (TyData variant_ty) (Id ctor_nm) $
--                         map (\(arg, ty) -> TmVar (TyData ty) $ Id arg) $
--                         zip arg_vars arg_tys) $ mkVar res
--       return [CFDefExt $ mkCFun nm $
--               CCompound []
--               (CBlockDecl (mkVarDecl variant_ty res) : s ++
--                [CBlockStmt $ CReturn
--                 (Just $ CCast genericDecl (mkVar res) nil) nil]) nil,
--               CDeclExt $ thunkDecl ctor_nm]

-- mkFieldProjection :: Type -- record type
--                   -> Id  -- field name
--                   -> Type -- field type
--                   -> CM ([CExternalDeclaration NodeInfo])
-- mkFieldProjection record_ty (Id field_nm) field_ty =
--   let (record_ct, record_ds) = typeToC record_ty
--       (field_ct, field_ds) = typeToC field_ty in do
--     nm <- nextSym "_P"
--     modify $ \s -> s {
--       main_coms = main_coms s ++
--         [CSuperCombinator (TyData field_ty) (Id field_nm) [] $
--           TmThunk (TyData field_ty) (Id nm) []] }
--     return
--       [CFDefExt $ mkCFun nm $
--         CCompound []
--         [CBlockStmt $ CReturn (Just $ CMember (CCast (mkTypeDecl record_ct record_ds)
--                                                 (CIndex (CVar (mkIdent "args") nil)
--                                                  (mkIntConst 0) nil) nil)
--                                (mkIdent field_nm) True nil) nil]
--         nil,
--        CDeclExt $ thunkDecl field_nm]

mkStructOrUnionDecl :: Bool -- typedef or no?
                    -> CStructTag -- struct or union?
                    -> Maybe String -- struct/union name
                    -> Maybe String -- typedef name
                    -> Maybe [CDeclaration NodeInfo] -- field declarations
                    -> CDeclaration NodeInfo
mkStructOrUnionDecl td cstag struct_nm typedef_nm decls = C.CDecl
  ((if td then [CStorageSpec $ CTypedef nil] else []) ++
    [CTypeSpec $ CSUType (CStruct cstag (mkIdent <$> struct_nm)
                          decls [] nil) nil])
  [(Just $ CDeclr (mkIdent <$> typedef_nm) [] Nothing [] nil,
    Nothing, Nothing)] nil

mkVariantDeclaration :: String -- variant name
                     -> [(String, String)] -- constructor typedef
                                           -- names and ident names
                     -> CDeclaration NodeInfo
mkVariantDeclaration variant_nm ctors =
  mkStructOrUnionDecl False CStructTag (Just variant_nm) Nothing
  (Just [C.CDecl [CTypeSpec $ CIntType nil]
         [(Just $ CDeclr (Just $ mkIdent "tag") [] Nothing [] nil,
           Nothing, Nothing)] nil,
         mkStructOrUnionDecl False CUnionTag Nothing Nothing $ Just $
          map (\(tp_nm, nm) ->
                 C.CDecl [CTypeSpec $ CTypeDef (mkIdent tp_nm) nil]
                [(Just $ CDeclr (Just $ mkIdent nm) [] Nothing [] nil,
                  Nothing, Nothing)] nil) ctors])
  


-- Let's just disallow shadowing of top-level definitions (good idea
-- for supporting mutual recursion within a module anyway) so then we
-- can safely group all of the type declarations together at the top,
-- then forward declarations for all functions, then all of the
-- function definitions.

mkCall :: CExpr -> [CExpr] -> CExpr
mkCall f args = CCall f args nil

mkPrintf :: String -> [CExpr] -> CExpr
mkPrintf fmt args = mkCall (CVar (mkIdent "printf") nil) (mkStringConst fmt : args)

mkExit :: Integer -> CExpr
mkExit exit_code = mkCall (CVar (mkIdent "exit") nil) [mkIntConst exit_code]

-- | Compile an eval, assert, or supercombinator command (CAF, not an
-- abstraction) that was deferred during the first pass to a list of
-- instructions to be executed in the main.
compileMainCommand :: Command TyData -> CM [CCompoundBlockItem NodeInfo]
compileMainCommand (CEval (TyData ty) tm) =
  debugPrint ("compileMainCommand: eval " ++ show tm) $ do
  x <- freshVar
  s <- compileTerm tm $ mkVar x
  -- return $ s ++ [CBlockStmt $ CExpr (Just e) nil]
  return $ (CBlockDecl $ mkVarDecl ty x) :
    s ++ [CBlockStmt $ CExpr (Just $ mkPrintf "%d\n" [mkVar x]) nil]
compileMainCommand (CAssert (TyData ty) tm) = do
  x <- freshVar
  s <- compileTerm tm $ mkVar x
  return $ (CBlockDecl $ mkVarDecl ty x) :
    s ++ [CBlockStmt $ CIf (CUnary CNegOp (mkVar x) nil)
           (CCompound [] [CBlockStmt $ CExpr 
                           (Just $ mkPrintf "failed assertion: %d\n"
                             [mkStringConst $ show tm]) nil,
                           CBlockStmt $ CExpr (Just $ mkExit $ -1) nil] nil)
           Nothing nil]
compileMainCommand (CSuperCombinator _ (Id nm) [] body) = do
  -- debugPrint ("compileMainCommand: CAF " ++ show nm) $
  -- debugPrint ("body: " ++ show body) $ do
  s <- compileTerm body $ mkVar nm
  -- return $ s ++ [CBlockStmt $ CExpr (Just $ CAssign CAssignOp (mkVar nm) e nil) nil]
  return s
compileMainCommand c =
  error $ "compileMainCommand: unexpected command: " ++ show c

-- Run the provided list of statements and then return 0.
compileMain :: [CCompoundBlockItem NodeInfo] -> CFunDef
compileMain s =
  CFunDef [CTypeSpec $ CIntType nil]
  (CDeclr (Just $ mkIdent "main") [CFunDeclr (Left []) [] nil] Nothing [] nil)
  [] (CCompound [] (s ++ [CBlockStmt $ CReturn (Just $ mkIntConst 0) nil]) nil) nil

compileProg' :: Prog TyData -> CM CTranslUnit
compileProg' (Prog { prog_of = cs }) = do
  -- First pass.
  decls <- concat <$> (mapM compileCommand cs)

  -- Reorder so that all type definitions come first, then forward
  -- declares of functions, then definitions of functions.
  let decls' = sortOn (\case
                          CDeclExt (C.CDecl (CStorageSpec _ : _) _ _) -> 0
                          CDeclExt _ -> 1
                          _ -> 2) decls

  -- Second pass.
  main_commands <- gets main_coms
  main_instrs <- concat <$> (mapM compileMainCommand main_commands)

  -- debugPrint ("main_commands: " ++ show main_commands) $
  --   debugPrint ("main_instrs: " ++ show main_instrs) $ do

  -- Build the main function.
  let main = compileMain main_instrs

  -- Put it all together into a single translation unit.
  return $ CTranslUnit (decls ++ [CFDefExt main]) nil

preamble :: String
preamble = "#include <stdint.h>\n\
\#include <stdio.h>\n\
\#include <stdlib.h>\n\
\#include <string.h>\n\
\#include \"include/gc.h\"\n\
\typedef struct {\n\
\  int n;\n\
\  uintptr_t *args;\n\
\  uintptr_t (*fun_ptr)(uintptr_t[]);\n\
\} thunk;\n\
\typedef struct {\n\
\   uintptr_t *ptr;\n\
\ } ref;\n"

compileProg :: Prog TyData -> String
compileProg p =
  debugPrint ("compileProg p: " ++ show p) $
  (preamble ++) .
  render . pretty $
  runCM (compileProg' $ lambdaLiftProg p) initCContext initCState


-- Mapping of terms (assumed to contain no abstractions) to pairs of
-- lists of instructions and expressions (where the instructions are
-- required to be run for the expression to be well-defined).

-- C[TmVar x] = return ([], lookup(x))
-- C[TmAbs ...] = error
-- C[TmApp t1 t2] = do
--   (f_stmts, f_expr) <- C[t1]
--   (arg_stmts, arg_expr) <- C[t2]
--   let arity = get_arity t1 -- how many lambdas on the left? use type information
--   if arity = 1 then
--     -- x <- fresh_ident
--     -- write $ "fun x = f"
--     return (f_stmts ++ arg_stmts, call(f.fun, f.arg1, f.arg2, ..., arg))
--   else
--     return (f_stmts ++ arg_stmts ++ ["f.args[f.n] = arg", "f.n++"], f)

-- C[TmUnit] = return ([], NULL)
-- C[TmBool b] = return ([], b)
-- C[TmInt i] = return ([], i)
-- C[TmChar c] = return ([], c)
-- C[TmIf t1 t2 t3] = do
--   (s1, e1) <- C[t1]
--   (s2, e2) <- C[t2]
--   (s3, e3) <- C[t3]
--   x <- fresh_ident
--   res <- fresh_ident
--   return (s1 ++ ["val x = e2", "val res", "if e1 { s2; res = e2 } else { s3; res = s3 }"], res)
-- C[TmUnop u t] = second u <$> C[t]
-- C[TmBinop b t1 t2] = do
--   (s1, e1) <- C[t1]
--   (s2, e2) <- C[t2]
--   return (s1 ++ s2, b(e1, e2))
-- C[TmLet x t1 t2) = do
--   (s1, e1) <- C[t1]
--   let x' = legalize(x)
--   local (x |-> x') $ do
--     (s2, e2) <- C[t1]
--     return (s1 ++ ["val x' = e1"] ++ s2, e2)
-- C[TmVariant x ts] = do
--   let (ss, es) = zip $ C <$> ts
--   ...
  

-- data Term Î± =
--   TmVar Î± Id
--   | TmAbs Î± Id Type (Term Î±)
--   | TmApp Î± (Term Î±) (Term Î±)
--   | TmUnit Î±
--   | TmBool Î± Bool
--   | TmInt Î± Integer
--   | TmChar Î± Char
--   | TmIf Î± (Term Î±) (Term Î±) (Term Î±)
--   | TmUnop Î± Unop (Term Î±)
--   | TmBinop Î± Binop (Term Î±) (Term Î±)
--   | TmLet Î± Id (Term Î±) (Term Î±)
--   | TmVariant Î± Id [Term Î±]
--   | TmMatch Î± (Term Î±) [(Pattern, Term Î±)]
--   | TmRecord Î± [(Id, Term Î±)]
--   -- info, class name, method name, type index
--   | TmPlaceholder Î± ClassNm Id Type -- for class methods
--   deriving (Eq, Foldable, Functor, Generic, Traversable)


-- How to compile pattern matching? Preferably using switch statements..

-- destruct s as
--   | Inl x → f x
--   | Inr y → g y

-- ==>

-- stmts:
-- s.stmts
-- val res;
-- switch s.expr.tag {
-- case 0:
--   val x = s.expr.x0;
--   C[f x].stmts
--   res = C[f x].expr
-- case 1:
--   val y = s.expr.x0;
--   C[g y].stmts
--   res = C[g y].expr
-- }

-- expr:
-- res

-- Or perhaps we can use a strategy similar to what was done for the JS backend. Each pattern has 1) a corresponding predicate that is just a boolean expression that makes use of short-circuiting boolean operators, and 2) a corresponding list of variable binding statements that we know are safe when the predicate yields true.

-- pred (PVar x) (v) = true
-- pred PUnit v = true -- seems like an equality test isn't necessary since it would only typecheck if there will ultimately be a value of unit type, of which there is only one
-- pred (PBool b)(v) = v.b == b
-- pred (PInt i)(v) = v.i == i
-- pred (PChar c)(v) = v.c == c
-- pred (PPair p1 p2)(v) = pred p1 v.x0 && pred p2 v.x1
-- pred (PConstructor x ps) = v.tag == ix(x) && big_and ()
  
-- -- We provide special pattern syntax for pairs even though they are
-- -- implemented as variants.
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
