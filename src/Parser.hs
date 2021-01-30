{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase   #-}
-- {-# LANGUAGE Strict       #-}

module Parser where

import           Control.Applicative
import           Data.Char
import           Data.Function
import           Data.Functor
import           Data.Maybe                       (fromJust)
import           Data.String
import qualified Data.Text                as Text
import           LambdaCalculusEssentials

newtype Parser s a 
  = Parser { runParser :: [s] -> Maybe (a, [s]) -- ^ Function that takes a stream of elements of the type
                                                -- @s@ and returns a pair of the result and the rest of 
                                                -- the stream, wrapped in the @Maybe@ context
           }

instance Functor (Parser s) where
  fmap :: (a -> b) -> Parser s a -> Parser s b
  fmap f (Parser p) = Parser $ \l -> case p l of
    Nothing      -> Nothing
    Just (a, l') -> Just (f a, l')

instance Applicative (Parser s) where
  pure :: a -> Parser s a
  pure x = Parser $ \l -> Just (x, l)

  (<*>) :: Parser s (a -> b) -> Parser s a -> Parser s b
  Parser pf <*> Parser pa = Parser $ \l -> case pf l of
    Nothing      -> Nothing
    Just (f, l') -> case pa l' of
      Nothing       -> Nothing
      Just (a, l'') -> Just (f a, l'') 

instance Monad (Parser s) where
  (>>=) :: Parser s a -> (a -> Parser s b) -> Parser s b
  Parser p >>= f = Parser $ \l -> case p l of
    Nothing      -> Nothing
    Just (a, l') -> runParser (f a) l'

instance Alternative (Parser s) where
  empty :: Parser s a
  empty = Parser $ \_ -> Nothing

  (<|>) :: Parser s a -> Parser s a -> Parser s a
  Parser x <|> Parser y = Parser $ \l -> case x l of
    Nothing      -> y l
    Just (a, l') -> Just (a, l')

-- | Return the resulting value after parsing the initial given stream of values of the type @s@,
-- if the parsing was successful.
evalParser :: Parser s a -> [s] -> Maybe a
evalParser p ss = fmap fst (runParser p ss)

-- | Return the remaining stream of values of the type @s@ after parsing the initial given stream of values,
-- if the parsing was successful.
execParser :: Parser s a -> [s] -> Maybe [s]
execParser p ss = fmap snd (runParser p ss)

-- | Return a parser that doesn't consume any of the elements from the given stream of values
-- and always returns a guaranteed successful parsing denoted by the 'unit' data type.
ok :: Parser s ()
ok = pure ()

-- | Return a parser that checks whether the input stream of values is empty or not, and returns the
-- corresponding result based on that speculation; the successful parsing is denoted by the 'unit' data type.
eof :: Parser s ()
eof = Parser $ \l -> case l of
  [] -> Just ((), [])
  _  -> Nothing

-- | Return a parser that checks if the first element of the input stream of values satisfies the
-- given predicate and returns the pair of the first element and the rest of the stream wrapped
-- in a @Just@ data constructor; in any other case returns @Nothing@.
satisfy :: (s -> Bool) -> Parser s s
satisfy predicate = Parser $ \l -> case l of
  []       -> Nothing
  (x : xs) -> if predicate x then Just (x, xs) else Nothing

-- | Check if the given element of the type @s@ is the first element of the input stream of values
-- inside a parser.
element :: Eq s => s -> Parser s s
element c = satisfy (== c)

-- | Check if the given stream of values of the type @s@ is the prefix of the input stream of values
-- inside a parser. 
stream :: Eq s => [s] -> Parser s [s]
stream []       = return []
stream (x : xs) = element x >>= \x' -> stream xs >>= \xs' -> return (x' : xs')

-- =========================================== --

data Token = LPar
           | RPar
           | BackSlash
           | Dot
           | Identifier String
           deriving (Eq, Ord, Show, Read)

tokenize :: String -> [Token]
tokenize   []          = []
tokenize   ('('  : xs) = LPar : tokenize xs 
tokenize   (')'  : xs) = RPar : tokenize xs
tokenize   ('\\' : xs) = BackSlash : tokenize xs
tokenize   ('.'  : xs) = Dot : tokenize xs
tokenize s@(x    : xs)
  | isSpace x = tokenize xs
  | isAlpha x = span (\c -> isAlphaNum c || c == '\'') s & \(satisfied, rest) -> 
    Identifier satisfied : tokenize rest

variable :: Parser Token String 
variable = satisfy (\case 
  Identifier _ -> True
  _            -> False) <&> \(Identifier x) -> x

parseLambdaTerm :: Parser Token LambdaTerm
parseLambdaTerm = foldl1 (:@:) <$> (some $ Var <$> variable 
              <|> L <$> (element BackSlash *> variable) <*> (element Dot *> parseLambdaTerm)
              <|> element LPar *> parseLambdaTerm <* element RPar)

-- =========================================== --

parse :: String -> LambdaTerm
parse = fst
      . fromJust
      . runParser (parseLambdaTerm <* eof)
      . tokenize