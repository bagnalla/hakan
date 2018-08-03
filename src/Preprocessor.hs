-- | This module provides functions for preprocessing an input file
-- before passing it to the main parser.
module Preprocessor (substImports, importLines) where

import Data.List (splitAt)
import Text.ParserCombinators.Parsec

-- Replace imports by inlining their corresponding source code
substImports :: String -> [(Int, [String])] -> String
substImports s imports = unlines $
        foldr (\(lnum, srcs) acc ->
                  let (front, back) = splitAt lnum acc in
                    front ++ srcs ++ drop 1 back) (lines s)
        imports

-- Find all import commands and return a mapping (assoc list) from
-- line number to lists of module names imported by the command at
-- that line.
importLines :: [String] -> [(Int, [String])]
importLines ls = aux 0 [] ls
  where
    aux _ acc [] = acc
    aux i acc (x:xs) = do
      let imp = parse parseImport "" x
      case imp of
        Left _   -> aux (i+1) acc xs
        Right ss -> aux (i+1) ((i, ss):acc) xs

-- Parse an import command
parseImport :: Parser [String]
parseImport = spaces >> (string "import " <|> string "∃") >> spaces >> imports
  where
    imports = paren <|> bare
    paren = try $ char '(' >> bare >>= \res -> char ')' >> return res
    bare = sepBy name ((oneOf ", ") >> spaces)
    name = many (noneOf ",()\n ")
