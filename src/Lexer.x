-- This file is based on the template from
-- https://github.com/dagit/happy-plus-alex

{
{-# OPTIONS -w  #-}
module Lexer
  ( Token(..)
  , AlexPosn(..)
  , TokenClass(..)
  , unLex
  , Alex(..)
  , runAlex'
  , alexMonadScan'
  , alexError'
  ) where
import Prelude hiding (lex)
import Data.Char (chr)
import Control.Monad ( liftM )
import Symtab (Id(..))
}
%wrapper "monadUserState"
$digit = 0-9
$alpha = [A-Za-z]
$capital = [A-Z]
tokens :-

  "#".*                         ;
  "--".*                         ;
  $white+                       ;
  "->"                          { lex' TokenArrow }
  \→                            { lex' TokenArrow }
  "=>"                          { lex' TokenFatArrow }
  "."                           { lex' TokenDot }
  ","                           { lex' TokenComma }
  Bool                          { lex' TokenBoolTy }
  Int                           { lex' TokenIntTy }
  \ℤ                            { lex' TokenIntTy }
  Char                          { lex' TokenCharTy }
  Unit                          { lex' TokenUnitTy }
  Ref                           { lex' TokenRefTy }
  tt                            { lex' TokenTT }
  true                          { lex' $ TokenBool True }
  \⊤                            { lex' $ TokenBool True }
  false                         { lex' $ TokenBool False }
  \⊥                            { lex' $ TokenBool False }
  fix                           { lex' TokenFix }
  \μ                            { lex' TokenFix }
  if                            { lex' TokenIf }
  then                          { lex' TokenThen }
  else                          { lex' TokenElse }
  evaluate                      { lex' TokenEval }
  run                           { lex' TokenEval }
  check                         { lex' TokenCheck }
--  fst                           { lex' TokenFst }
--  snd                           { lex' TokenSnd }
  π₁                            { lex' TokenPi1 }
  π₂                            { lex' TokenPi2 }
  ₁                             { lex' TokenSmall1 }
  ₂                             { lex' TokenSmall2 }
  inl                           { lex' TokenInl }
  inr                           { lex' TokenInr }
  case                          { lex' TokenCase }
  of                            { lex' TokenOf }
  ref                           { lex' TokenRef }
  let                           { lex' TokenLet }
--  letrec                        { lex' TokenLetrec }
  def                           { lex' TokenDef }
--  val                           { lex' TokenVal }
  in                            { lex' TokenIn }
  ":="                          { lex' TokenUpdate }
  \←                            { lex' TokenUpdate }
  "!"                           { lex' TokenBang }
  $digit+                       { lex (TokenInt . read) }
  \=                            { lex' TokenEq }
  \(                            { lex' TokenLParen }
  \)                            { lex' TokenRParen }
  \:                            { lex' TokenColon }
  \;                            { lex' TokenSemicolon }
  \+                            { lex' TokenPlus }
  \-                            { lex' TokenMinus }
  \*                            { lex' TokenMult }
  \×                            { lex' TokenTimes }
  \⊗                            { lex' TokenOTimes }
  \/                            { lex' TokenDiv }
  "&&"                          { lex' TokenAnd }
  \∧                            { lex' TokenAnd }
  "||"                          { lex' TokenOr }
  \∨                            { lex' TokenOr }
  \~                            { lex' TokenNot }
  \¬                            { lex' TokenNot }
  \<                            { lex' TokenLt }
  \>                            { lex' TokenGt }
  "<="                          { lex' TokenLe }
  \≤                            { lex' TokenLe }
  ">="                          { lex' TokenGe }
  \≥                            { lex' TokenGe }
  "<>"                          { lex' TokenNeq }
  \|                            { lex' TokenBar }
  \_                            { lex' TokenWildcard }
  \\                            { lex' TokenLambda }
  \λ                            { lex' TokenLambda }
  \∘                            { lex' TokenCompose }
  \〚                           { lex' TokenLLBracket }
  \〛                           { lex' TokenRRBracket }
  \[                            { lex' TokenLBracket }
  \]                            { lex' TokenRBracket }
  \{                            { lex' TokenLBrace }
  \}                            { lex' TokenRBrace }
  \⟨                            { lex' TokenLAngle }
  \⟩                            { lex' TokenRAngle }
  \∥                            { lex' TokenDoubleBar }
  \▵                            { lex' TokenTriangle }
  \▿                            { lex' TokenTriangleDown }
  \?                            { lex' TokenQuestion }
  data                          { lex' TokenData }
  destruct                      { lex' TokenDestruct }
  as                            { lex' TokenAs }
  end                           { lex' TokenEnd }
  record                        { lex' TokenRecord }
  assert                        { lex' TokenAssert }
  pure                          { lex' TokenPure }
  impure                        { lex' TokenImpure }
  io                            { lex' TokenIO }
  class                         { lex' TokenClass }
  instance                      { lex' TokenInstance }
  where                         { lex' TokenWhere }
  -- eof                        { lex' TokenEOF }
  \'.\'                         { lex (TokenChar . head . tail) }
  $capital [$alpha $digit \_ \']* { lex (TokenCapId . Id) }
  $alpha [$alpha $digit \_ \']*   { lex (TokenId . Id) }

{
-- To improve error messages, We keep the path of the file we are
-- lexing in our own state.
data AlexUserState = AlexUserState { filePath :: FilePath }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "<unknown>"

getFilePath :: Alex FilePath
getFilePath = liftM filePath alexGetUserState

setFilePath :: FilePath -> Alex ()
setFilePath = alexSetUserState . AlexUserState

-- The token type, consisting of the source code position and a token class.
data Token = Token AlexPosn TokenClass
  deriving ( Show )

data TokenClass =
  TokenId Id
  | TokenCapId Id
  | TokenChar Char
  | TokenLParen
  | TokenRParen
  | TokenColon
  | TokenSemicolon
  | TokenLambda
  | TokenBoolTy
  | TokenIntTy
  | TokenCharTy
  | TokenUnitTy
  | TokenRefTy
  | TokenTT
  | TokenArrow
  | TokenFatArrow
  | TokenDot
  | TokenBool Bool
  | TokenInt Integer
  | TokenEq
  | TokenSucc
  | TokenPred
  | TokenIszero
  | TokenFix
  | TokenIf
  | TokenThen
  | TokenElse
  | TokenEval
  | TokenCheck
  | TokenPlus
  | TokenMinus
  | TokenMult
  | TokenDiv
  | TokenAnd
  | TokenOr
  | TokenLt
  | TokenGt
  | TokenLe
  | TokenGe
  | TokenNeq
  | TokenNot
  | TokenComma
  | TokenInl
  | TokenInr
  | TokenCase
  | TokenOf
  | TokenBar
  | TokenWildcard
  | TokenEOF
  | TokenRef
  | TokenBang
  | TokenUpdate
  | TokenLet
  | TokenDef
--  | TokenLetrec
--  | TokenVal
  | TokenIn
  | TokenCompose
  | TokenLLBracket
  | TokenRRBracket
  | TokenLBracket
  | TokenRBracket
  | TokenLBrace
  | TokenRBrace
  | TokenLAngle
  | TokenRAngle
  | TokenTimes
  | TokenOTimes
--  | TokenFst
--  | TokenSnd
  | TokenPi1
  | TokenPi2
  | TokenSmall1
  | TokenSmall2
  | TokenDoubleBar
  | TokenTriangle
  | TokenTriangleDown
  | TokenData
  | TokenDestruct
  | TokenAs
  | TokenEnd
  | TokenRecord
  | TokenQuestion
  | TokenAssert
  | TokenPure
  | TokenImpure
  | TokenIO
  | TokenClass
  | TokenInstance
  | TokenWhere
    deriving (Eq,Show)

-- For nice parser error messages.
unLex :: TokenClass -> String
unLex (TokenId x)          = show x
unLex (TokenCapId x)       = show x
unLex (TokenChar c)        = show c
unLex TokenLParen          = "("
unLex TokenRParen          = ")"
unLex TokenColon           = ":"
unLex TokenSemicolon       = ";"
unLex TokenBar             = "|"
unLex TokenLambda          = "\\"
unLex TokenBoolTy          = "Bool"
unLex TokenIntTy           = "Int"
unLex TokenCharTy          = "Char"
unLex TokenUnitTy          = "Unit"
unLex TokenRefTy           = "Ref"
unLex TokenTT              = "tt"
unLex TokenArrow           = "->"
unLex TokenFatArrow        = "=>"
unLex TokenDot             = "."
unLex (TokenBool b)        = show b
unLex (TokenInt i)         = show i
unLex TokenEq              = "="
unLex TokenSucc            = "succ"
unLex TokenPred            = "pred"
unLex TokenIszero          = "iszero"
unLex TokenFix             = "fix"
unLex TokenIf              = "if"
unLex TokenThen            = "then"
unLex TokenElse            = "else"
unLex TokenEval            = "evaluate"
unLex TokenCheck           = "check"
unLex TokenPlus            = "plus"
unLex TokenMinus           = "minus"
unLex TokenMult            = "mult"
unLex TokenDiv             = "div"
unLex TokenLt              = "<"
unLex TokenLe              = "<="
unLex TokenGt              = ">"
unLex TokenGe              = ">="
unLex TokenNeq             = "<>"
unLex TokenNot             = "~"
unLex TokenComma           = ","
--unLex TokenFst             = "fst"
--unLex TokenSnd             = "snd"
unLex TokenPi1             = "π₁"
unLex TokenPi2             = "π₂"
unLex TokenInl             = "inl"
unLex TokenInr             = "inr"
unLex TokenCase            = "case"
unLex TokenOf              = "of"
unLex TokenWildcard        = "_"
unLex TokenRef             = "ref"
unLex TokenBang            = "!"
unLex TokenUpdate          = ":="
unLex TokenLet             = "let"
unLex TokenDef             = "def"
--unLex TokenLetrec          = "letrec"
--unLex TokenVal             = "val"
unLex TokenIn              = "in"
unLex TokenCompose         = "∘"
unLex TokenLLBracket       = "〚"
unLex TokenRRBracket       = "〛"
unLex TokenLBracket        = "["
unLex TokenRBracket        = "]"
unLex TokenLBrace          = "{"
unLex TokenRBrace          = "}"
unLex TokenLAngle          = "⟨"
unLex TokenRAngle          = "⟩"
unLex TokenTimes           = "×"
unLex TokenOTimes          = "⊗"
unLex TokenSmall1          = "₁"
unLex TokenSmall2          = "₂"
unLex TokenDoubleBar       = "∥"
unLex TokenTriangle        = "▵"
unLex TokenTriangleDown    = "▿"
unLex TokenData            = "data"
unLex TokenDestruct        = "destruct"
unLex TokenAs              = "as"
unLex TokenEnd             = "end"
unLex TokenRecord          = "record"
unLex TokenQuestion        = "?"
unLex TokenAssert          = "assert"
unLex TokenPure            = "pure"
unLex TokenImpure          = "impure"
unLex TokenIO              = "io"
unLex TokenClass           = "class"
unLex TokenInstance        = "instance"
unLex TokenWhere           = "where"
unLex TokenEOF             = "<EOF>"

alexEOF :: Alex Token
alexEOF = do
  (p,_,_,_) <- alexGetInput
  return $ Token p TokenEOF

-- Unfortunately, we have to extract the matching bit of string
-- ourselves...
lex :: (String -> TokenClass) -> AlexAction Token
lex f = \(p,_,_,s) i -> return $ Token p (f (take i s))

-- For constructing tokens that do not depend on
-- the input
lex' :: TokenClass -> AlexAction Token
lex' = lex . const

-- We rewrite alexMonadScan' to delegate to alexError' when lexing fails
-- (the default implementation just returns an error message).
alexMonadScan' :: Alex Token
alexMonadScan' = do
  inp <- alexGetInput
  sc <- alexGetStartCode
  case alexScan inp sc of
    AlexEOF -> alexEOF
    AlexError (p, _, _, s) ->
        alexError' p ("lexical error at character '" ++ take 1 s ++ "'")
    AlexSkip  inp' len -> do
        alexSetInput inp'
        alexMonadScan'
    AlexToken inp' len action -> do
        alexSetInput inp'
        action (ignorePendingBytes inp) len

-- Signal an error, including a commonly accepted source code position.
alexError' :: AlexPosn -> String -> Alex a
alexError' (AlexPn _ l c) msg = do
  fp <- getFilePath
  alexError (fp ++ ":" ++ show l ++ ":" ++ show c ++ ": " ++ msg)

-- A variant of runAlex, keeping track of the path of the file we are lexing.
runAlex' :: Alex a -> FilePath -> String -> Either String a
runAlex' a fp input = runAlex input (setFilePath fp >> a)
}
