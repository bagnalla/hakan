-- This grammar file is based on the template from
-- https://github.com/dagit/happy-plus-alex

-- TODO: syntax sugar for n-tuples (terms and patterns).

{
{-# OPTIONS -w #-}
module Parser( parseProg ) where

import Lexer
import qualified Ast
import Data.Tuple (swap)
import Symtab (Id(..))
import Ast (data_of_term)
}

%name parse
%tokentype { Token }
%monad { Alex }
%lexer { lexwrap } { Token _ TokenEOF }
-- Without this we get a type error
%error { happyError }

%token
  arrow        { Token $$ TokenArrow }
  fatarrow     { Token $$ TokenFatArrow }
  '.'          { Token $$ TokenDot }
  bool         { Token $$ TokenBoolTy }
  int          { Token $$ TokenIntTy }
  char         { Token $$ TokenCharTy }
  unit         { Token $$ TokenUnitTy }
  refty        { Token $$ TokenRefTy }
  tt           { Token $$ TokenTT }
  true         { Token $$ (TokenBool True) }
  false        { Token $$ (TokenBool False) }
  intVal       { Token _ (TokenInt _) }
  fix          { Token $$ TokenFix }
  if           { Token $$ TokenIf }
  then         { Token $$ TokenThen }
  else         { Token $$ TokenElse }
  evaluate     { Token $$ TokenEval }
  check        { Token $$ TokenCheck }
  id           { Token _ (TokenId _) }
  capid        { Token _ (TokenCapId _) }
  charVal      { Token _ (TokenChar _) }
--  fst          { Token $$ TokenFst }
--  snd          { Token $$ TokenSnd }
  "π₁"         { Token $$ TokenPi1 }
  "π₂"         { Token $$ TokenPi2 }
  inl          { Token $$ TokenInl }
  inr          { Token $$ TokenInr }
  case         { Token $$ TokenCase }
  of           { Token $$ TokenOf }
  ref          { Token $$ TokenRef }
  let          { Token $$ TokenLet }
  def          { Token $$ TokenDef }
--  letrec       { Token $$ TokenLetrec }
--  val          { Token $$ TokenVal }
  in           { Token $$ TokenIn }
  '!'          { Token $$ TokenBang }
  ":="         { Token $$ TokenUpdate }
  ','          { Token $$ TokenComma }
  '|'          { Token $$ TokenBar }
  '='          { Token $$ TokenEq }
  '\\'         { Token $$ TokenLambda }
  '('          { Token $$ TokenLParen }
  ')'          { Token $$ TokenRParen }
  ':'          { Token $$ TokenColon }
  ';'          { Token $$ TokenSemicolon }
  '+'          { Token $$ TokenPlus }
  '-'          { Token $$ TokenMinus }
  '*'          { Token $$ TokenMult }
  '/'          { Token $$ TokenDiv }
  '<'          { Token $$ TokenLt }
  "<="         { Token $$ TokenLe }
  '>'          { Token $$ TokenGt }
  ">="         { Token $$ TokenGe }
  "<>"         { Token $$ TokenNeq }
  '~'          { Token $$ TokenNot }
  "&&"         { Token $$ TokenAnd }
  "||"         { Token $$ TokenOr }
  '_'          { Token $$ TokenWildcard }
  '〚'         { Token $$ TokenLLBracket }
  '〛'         { Token $$ TokenRRBracket }
  '['          { Token $$ TokenLBracket }
  ']'          { Token $$ TokenRBracket }
  '{'          { Token $$ TokenLBrace }
  '}'          { Token $$ TokenRBrace }
  '⟨'          { Token $$ TokenLAngle }
  '⟩'          { Token $$ TokenRAngle }
  '∘'          { Token $$ TokenCompose }
  '×'          { Token $$ TokenTimes }
  '⊗'          { Token $$ TokenTimes }
  '₁'          { Token $$ TokenSmall1 }
  '₂'          { Token $$ TokenSmall2 }
  '∥'          { Token $$ TokenDoubleBar }
  '▵'          { Token $$ TokenTriangle }
  '▿'          { Token $$ TokenTriangleDown }
  '?'          { Token $$ TokenQuestion }
  data         { Token $$ TokenData }
  destruct     { Token $$ TokenDestruct }
  as           { Token $$ TokenAs }
  end           { Token $$ TokenEnd }
  record       { Token $$ TokenRecord }
  assert       { Token $$ TokenAssert }
  pure         { Token $$ TokenPure }
  impure       { Token $$ TokenImpure }
  io           { Token $$ TokenIO }
  class        { Token $$ TokenClass }
  instance     { Token $$ TokenInstance }
  where        { Token $$ TokenWhere }
  -- eof          { Token $$ TokenEOF }

%nonassoc ':'
%right arrow '.'
%nonassoc in
%right ';'
%left else
%nonassoc ":="
%nonassoc '=' "<>" '<' '>' "<=" ">="
%left "||"
%left "&&"
%left '+' '-'
%left '*' '/' '×' '⊗'
%left '∘'
%left '▵' '▿'
%nonassoc fix true false intVal id unit bool int char refty
%left APP
%nonassoc UNOP
%nonassoc '-'
%nonassoc '₁' '₂' '?'
%nonassoc '(' ')' '[' ']'
%%

Prog :
  Commands { Ast.Prog { Ast.pdata_of = AlexPn 0 0 0, Ast.prog_of = $1 } }

opt(p) :
  p { Just $1 }
  | { Nothing }

-- Atomic types
AType :
  unit { Ast.TyUnit }
  | bool { Ast.TyBool }
  | int { Ast.TyInt }
  | char { Ast.TyChar }
  | '(' Type ')' { $2 }
  | id { Ast.TyVar False [] $ idFromToken $1 } -- TODO
  | capid { Ast.TyName (idFromToken $1) }
  | '[' Type ']'
    { Ast.TyApp (Ast.TyName $ Id "List") $2 }

AppType :
  AType { $1 }
  | AppType AType { Ast.TyApp $1 $2 }

Type :
  AppType { $1 }
  | Type arrow Type { Ast.TyArrow $1 $3 }
  | Type '×' Type
    { Ast.TyApp (Ast.TyApp (Ast.TyName $ Id "Pair") $1) $3 }
  | Type '+' Type
    { Ast.TyApp (Ast.TyApp (Ast.TyName $ Id "Sum") $1) $3 }
  | Type '?' { Ast.TyApp (Ast.TyName $ Id "Option") $1 }
  | refty Type { Ast.TyRef $2 }

Id :
  '_' { Token $1 (TokenId (Id "_")) }
  | id { $1 }

Term :
  AppTerm { $1 }
  | if Term then Term else Term { Ast.TmIf $1 $2 $4 $6 }
  | '\\' Id opt(TyBinder) '.' Term {
        Ast.TmAbs $1 (idFromToken $2) (case $3 of
			 Nothing -> Ast.mkTyVar (Id "")
			 Just ty -> ty) $5 }
  | '-' Term %prec UNOP { Ast.TmUnop $1 Ast.UMinus $2 }
  | '~' Term %prec UNOP { Ast.TmUnop $1 Ast.UNot $2 }
  | ref Term %prec UNOP { Ast.TmUnop $1 Ast.URef $2 }
  | '!' Term %prec UNOP { Ast.TmUnop $1 Ast.UDeref $2 }
  | Term '+' Term { Ast.TmBinop $2 Ast.BPlus $1 $3 }
  | Term '-' Term { Ast.TmBinop $2 Ast.BMinus $1 $3 }
  | Term '*' Term { Ast.TmBinop $2 Ast.BMult $1 $3 }
  | Term '/' Term { Ast.TmBinop $2 Ast.BDiv $1 $3 }
  | Term '<' Term { Ast.TmBinop $2 Ast.BLt $1 $3 }
  | BExp { $1 }
  | Term ":=" Term { Ast.TmBinop $2 Ast.BUpdate $1 $3 }
  | Term '∘' Term
    { Ast.TmApp $2 (Ast.TmApp $2  (Ast.TmVar $2 (Id "compose")) $3) $1 }
  | Term ';' Term { Ast.TmApp $2 (Ast.TmAbs $2 (Id "_") Ast.TyUnit $3) $1 }
  | let id '=' Term in Term { Ast.TmLet $1 (idFromToken $2) $4 $6 }
  | Term '▿' Term
    { Ast.TmApp $2 (Ast.TmApp $2 (Ast.TmVar $2 (Id "cotuple")) $1) $3 }
  | Term '▵' Term
    { Ast.TmApp $2 (Ast.TmApp $2 (Ast.TmVar $2 (Id "tuple")) $1) $3 }
--  | destruct Term as barlist(Case) end { Ast.TmMatch $1 $2 $4 }
  | destruct Term as barlist(Case) { Ast.TmMatch $1 $2 $4 }

BExp :
  Term "<=" Term { Ast.TmBinop $2 Ast.BLe $1 $3 }
  | Term '>' Term { Ast.TmBinop $2 Ast.BGt $1 $3 }
  | Term ">=" Term { Ast.TmBinop $2 Ast.BGe $1 $3 }
  | Term '=' Term { Ast.TmBinop $2 Ast.BEq $1 $3 }
  | Term "<>" Term { Ast.TmBinop $2 Ast.BNeq $1 $3 }
  | Term "&&" Term { Ast.TmBinop $2 Ast.BAnd $1 $3 }
  | Term "||" Term { Ast.TmBinop $2 Ast.BOr $1 $3 }

AppTerm :
  ATerm { $1 }
  | AppTerm ATerm { Ast.TmApp (data_of_term $1) $1 $2 }
  | fix ATerm { Ast.TmUnop $1 Ast.UFix $2 }

-- Atomic terms
ATerm :
  tt { Ast.TmUnit $1 }
  | true { Ast.TmBool $1 True }
  | false { Ast.TmBool $1 False }
  | intVal { Ast.TmInt (infoFromToken $1) (intFromToken $1) }
  | charVal { Ast.TmChar (infoFromToken $1) (charFromToken $1) }
  | id { Ast.TmVar (infoFromToken $1) (idFromToken $1) }
  | capid { Ast.TmVar (infoFromToken $1) (idFromToken $1) }
  | "π₁" { Ast.TmVar $1 (Id "proj1") }
  | "π₂" { Ast.TmVar $1 (Id "proj2") }
  | '(' Term ')' { $2 }
  | '(' Term ',' Term ')' { Ast.mkPair $1 $2 $4 }
  | '[' Term ',' Term ']'
    { Ast.TmApp $1 (Ast.TmApp $1 (Ast.TmVar $1 (Id "cotuple")) $2) $4 }
  | '⟨' Term ',' Term '⟩'
    { Ast.TmApp $1 (Ast.TmApp $1 (Ast.TmVar $1 (Id "tuple")) $2) $4 }
  | ATerm '₁' { Ast.mkProj1 $2 $1 }
  | ATerm '₂' { Ast.mkProj2 $2 $1 }
  | '{' seplist(Field, ',') '}' { Ast.TmRecord $1 $2 }

Field :
  id '=' Term { (idFromToken $1, $3) }

Case :
  Pattern arrow Term { ($1, $3) }

Pattern :
  APattern { $1 }
  | capid list(APattern) { Ast.PConstructor (idFromToken $1) $2 }

APattern :
  tt { Ast.PUnit }
  | true { Ast.PBool True }
  | false { Ast.PBool False }
  | intVal { Ast.PInt (intFromToken $1) }
  | charVal { Ast.PChar (charFromToken $1) }
  | Id { Ast.PVar (idFromToken $1) }
  | '(' Pattern ')' { $2 }
  | '(' Pattern ',' Pattern ')' { Ast.PPair $2 $4 }
  | '{' seplist(FieldPattern, ',') '}' { Ast.PRecord $2 }

FieldPattern :
  id '=' Pattern { (idFromToken $1, $3) }

list(p) :
  p list(p) { $1 : $2 }
  | { [] }

seplist(p, sep) :
  p { [$1] }
  | p sep seplist(p, sep) { $1 : $3 }

barlist(p) :
  '|' p barlist(p) { $2 : $3 }
  | { [] }

-- Here we parse the constructor types as a single big type application
-- and use deApp to turn it into a list of types.
Ctor :
  capid opt(Type) { (idFromToken $1, case $2 of
                                       Just ty -> deApp ty
                                       Nothing -> []) }

Command :
  pure id TyDeclBinder { Ast.CDecl (infoFromToken $2) (idFromToken $2) $3 }
  | def id Binder {
      let (fi, x) = (infoFromToken $2, idFromToken $2) in
        Ast.CLet fi x (Ast.TmUnop fi Ast.UFix (Ast.TmAbs fi x
                 (Ast.mkTyVar (Id "")) $3)) }
  | evaluate Term { Ast.CEval $1 $2 }
  | '〚' Term '〛' { Ast.CEval $1 $2 }
  | data ClassConstraints fatarrow capid list(id) '=' barlist(Ctor)
      { Ast.propagateClassConstraintsCom $2 $
          Ast.CData $1 (idFromToken $4) (map idFromToken $5) $7 }
  | data capid list(id) '=' barlist(Ctor)
      { Ast.CData $1 (idFromToken $2) (map idFromToken $3) $5 }
  | record ClassConstraints fatarrow capid list(id) '=' '{'
    seplist(FieldDecl, ',') '}'
      { Ast.propagateClassConstraintsCom $2 $
          Ast.CRecord $1 (idFromToken $4) (map idFromToken $5) $8 }
  | record capid list(id) '=' '{' seplist(FieldDecl, ',') '}'
      { Ast.CRecord $1 (idFromToken $2) (map idFromToken $3) $6 }
  | assert BExp { Ast.CAssert $1 $2 }
  | check Term { Ast.CCheck $1 $2 }
  | class ClassConstraints fatarrow capid id where barlist(FieldDecl)
      { Ast.CClass $1 (map snd $2) (Ast.ClassNm $ idFromToken $4) (idFromToken $5) $7 }
  | class capid id where barlist(FieldDecl)
      { Ast.CClass $1 [] (Ast.ClassNm $ idFromToken $2) (idFromToken $3) $5 }
  | instance ClassConstraints fatarrow capid Type
    where barlist(InstanceMethod)
--      { Ast.CInstance $1 (map swap $2) (Ast.ClassNm $ idFromToken $4) $5 $7 }
      { Ast.CInstance $1 $2 (Ast.ClassNm $ idFromToken $4) $5 $7 }
  | instance capid Type where barlist(InstanceMethod)
      { Ast.CInstance $1 [] (Ast.ClassNm $ idFromToken $2) $3 $5 }

FieldDecl :
  id TyBinder { (idFromToken $1, $2) }

ClassConstraint :
  capid id { (idFromToken $2, Ast.ClassNm (idFromToken $1)) }

ClassConstraints :
  ClassConstraint { [$1] }
  | '(' seplist(ClassConstraint, ',') ')' { $2 }

TyBinder :
  ':' Type { $2 }

TyDeclBinder :
  -- Propagate class constraints to type variables. Doesnt avoid capture.
  -- Assumes there are no type abstractions.
--  ':' ClassConstraints fatarrow Type
--    { Ast.propagateClassConstraints $2 $4 }
-- TODO: fix this so that we can have class constraints without a conflict
-- with type application syntax :(
  ':' Type { $2 }

Binder :
  '=' Term { $2 }

InstanceMethod :
  id '=' Term { (idFromToken $1, $3) }

Commands :
--  Commands ';' Commands { $1 ++ $3 }
  Command Commands { $1 : $2 }
--  | Command { [$1] }
  | {- empty -} { [] }

{
lexwrap :: (Token -> Alex a) -> Alex a
lexwrap = (alexMonadScan' >>=)

happyError :: Token -> Alex a
happyError (Token p t) =
  alexError' p ("parse error at token '" ++ unLex t ++ "'")

parseProg :: FilePath -> String -> Either String (Ast.Prog AlexPosn)
parseProg = runAlex' parse

idFromToken :: Token -> Id
idFromToken tok = case tok of
  Token _ (TokenId x) -> x
  Token _ (TokenCapId x) -> x

intFromToken :: Token -> Integer
intFromToken tok = case tok of
  Token _ (TokenInt i) -> i

charFromToken :: Token -> Char
charFromToken tok = case tok of
  Token _ (TokenChar c) -> c

infoFromToken :: Token -> AlexPosn
infoFromToken tok = case tok of
  Token fi _ -> fi

-- This is such a hack.
deApp :: Ast.Type -> [Ast.Type]
deApp (Ast.TyApp s t) = deApp s ++ [t]
deApp ty = [ty]
}
