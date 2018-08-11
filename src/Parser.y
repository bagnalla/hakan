-- This grammar file is based on the template from
-- https://github.com/dagit/happy-plus-alex

{
{-# OPTIONS -w #-}
module Parser( parseProg ) where

import Lexer
import qualified Ast
import Symtab (Id(..))
import Core (data_of_term)
}

%name parse
%tokentype { Token }
%monad { Alex }
%lexer { lexwrap } { Token _ TokenEOF }
-- Without this we get a type error
%error { happyError }

%token
  arrow        { Token $$ TokenArrow }
  '.'          { Token $$ TokenDot }
  bool         { Token $$ TokenBoolTy }
  int          { Token $$ TokenIntTy }
  unit         { Token $$ TokenUnitTy }
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
  letrec       { Token $$ TokenLetrec }
  val          { Token $$ TokenVal }
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
  data         { Token $$ TokenData }
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
%nonassoc fix true false intVal id
%left APP
%nonassoc UNOP
%nonassoc '-'
--%nonassoc '₁' '₂'
%nonassoc '(' ')'
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
  | '(' Type ')' { $2 }

-- Atomic types including type variables
VType :
  unit { Ast.TyUnit }
  | bool { Ast.TyBool }
  | int { Ast.TyInt }
  | '(' DeclType ')' { $2 }
  | id { Ast.TyVar True $ idFromToken $1 }

Type :
  AType { $1 }
  | Type arrow Type { Ast.TyArrow $1 $3 }
  | Type '×' Type { Ast.TyPair $1 $3 }
  | Type '+' Type { Ast.TySum $1 $3 }

DeclType :
  VType { $1 }
  | DeclType arrow DeclType { Ast.TyArrow $1 $3 }
  | DeclType '×' DeclType { Ast.TyPair $1 $3 }
  | DeclType '+' DeclType { Ast.TySum $1 $3 }

Id :
  '_' { Token $1 (TokenId (Id "_")) }
  | id { $1 }

Term :
  AppTerm { $1 }
  | if Term then Term else Term { Ast.TmIf $1 $2 $4 $6 }
  | '\\' Id opt(TyBinder) '.' Term {
        Ast.TmAbs $1 (idFromToken $2) (case $3 of
			 Nothing -> Ast.TyVar False (Id "")
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
  | Term "<=" Term { Ast.TmBinop $2 Ast.BLe $1 $3 }
  | Term '>' Term { Ast.TmBinop $2 Ast.BGt $1 $3 }
  | Term ">=" Term { Ast.TmBinop $2 Ast.BGe $1 $3 }
  | Term '=' Term { Ast.TmBinop $2 Ast.BEq $1 $3 }
  | Term "<>" Term { Ast.TmBinop $2 Ast.BNeq $1 $3 }
  | Term "&&" Term { Ast.TmBinop $2 Ast.BAnd $1 $3 }
  | Term "||" Term { Ast.TmBinop $2 Ast.BOr $1 $3 }
  | Term ":=" Term { Ast.TmBinop $2 Ast.BUpdate $1 $3 }
  | Term '∘' Term
    { Ast.TmApp $2 (Ast.TmApp $2  (Ast.TmVar $2 (Id "compose")) $3) $1 }
  | case Term of '|' inl id arrow Term '|' inr id arrow Term
    { case ($6, $11) of
	(Token _ (TokenId nm1), Token _ (TokenId nm2)) ->
	  Ast.TmCase $1 $2 nm1 $8 nm2 $13 }
  | Term ';' Term { Ast.TmApp $2 (Ast.TmAbs $2 (Id "_") Ast.TyUnit $3) $1 }
  | let id '=' Term in Term { Ast.TmLet $1 (idFromToken $2) $4 $6 }
  | Term '▿' Term
    { Ast.TmApp $2 (Ast.TmApp $2 (Ast.TmVar $2 (Id "cotuple")) $1) $3 }
  | Term '▵' Term
    { Ast.TmApp $2 (Ast.TmApp $2 (Ast.TmVar $2 (Id "tuple")) $1) $3 }

AppTerm :
  ATerm { $1 }
  | AppTerm ATerm { Ast.TmApp (data_of_term $1) $1 $2 }
  | fix ATerm { Ast.TmUnop $1 Ast.UFix $2 }
  | inl ATerm TyBinder { Ast.TmInl $1 $2 $3 }
  | inr ATerm TyBinder { Ast.TmInr $1 $2 $3 }

-- Atomic terms
ATerm :
  tt { Ast.TmUnit $1 }
  | true { Ast.TmBool $1 True }
  | false { Ast.TmBool $1 False }
  | intVal { Ast.TmInt (infoFromToken $1) (intFromToken $1) }
  | id { Ast.TmVar (infoFromToken $1) (idFromToken $1) }
  | "π₁" { Ast.TmVar $1 (Id "proj1") }
  | "π₂" { Ast.TmVar $1 (Id "proj2") }
  | '(' Term ')' { $2 }
  | '(' Term ',' Term ')' { Ast.TmPair $1 $2 $4 }
  | '[' Term ',' Term ']'
    { Ast.TmApp $1 (Ast.TmApp $1 (Ast.TmVar $1 (Id "cotuple")) $2) $4 }
  | '⟨' Term ',' Term '⟩'
    { Ast.TmApp $1 (Ast.TmApp $1 (Ast.TmVar $1 (Id "tuple")) $2) $4 }
  | ATerm '₁' { Ast.TmUnop $2 Ast.UFst $1 }
  | ATerm '₂' { Ast.TmUnop $2 Ast.USnd $1 }

list(p) :
--  p { [$1] }
  p list(p) { $1 : $2 }
  | { [] }

barlist(p) :
--  p { [$1] }
  '|' p barlist(p) { $2 : $3 }
  | { [] }

Ctor :
  capid list(Type) { (capidFromToken $1, $2) }

Command :
  val id TyDeclBinder { Ast.CDecl (infoFromToken $2) (idFromToken $2) $3 }
  | let id Binder { Ast.CLet (infoFromToken $2) (idFromToken $2) $3 }
  | letrec id Binder {
      let (fi, x) = (infoFromToken $2, idFromToken $2) in
        Ast.CLet fi x (Ast.TmUnop fi Ast.UFix (Ast.TmAbs fi x
                 (Ast.TyVar False (Id "")) $3)) }
  | evaluate Term { Ast.CEval $1 $2 }
  | '〚' Term '〛' { Ast.CEval $1 $2 }
  | data capid list(id) '=' barlist(Ctor)
      { case $2 of
          Token fi (TokenCapId x) -> 
            Ast.CData fi x (map capidFromToken $3) $5 }

TyBinder :
  ':' Type { $2 }

TyDeclBinder :
  ':' DeclType { $2 }

Binder :
  '=' Term { $2 }

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

capidFromToken :: Token -> Id
capidFromToken tok = case tok of
  Token _ (TokenCapId x) -> x

intFromToken :: Token -> Integer
intFromToken tok = case tok of
  Token _ (TokenInt i) -> i

infoFromToken :: Token -> AlexPosn
infoFromToken tok = case tok of
  Token fi _ -> fi
}
