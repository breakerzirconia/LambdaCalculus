module LambdaCalculusEssentials where

import Data.List ( (\\)
                 , union
                 )

data LambdaTerm = Var    String 
                | Apply  LambdaTerm LambdaTerm 
                | Lambda String     LambdaTerm 
                deriving Eq

instance Show LambdaTerm where
    show (Var s) = s
    show (Apply p q) = "(" ++ show p ++ " " ++ show q ++ ")"
    show (Lambda x p) = "(\\" ++ x ++ ". " ++ show p ++ ")"

infix 4 =@=
(=@=) :: LambdaTerm -> LambdaTerm -> Bool
(Var x) =@= (Var y) = x == y
(Apply p q) =@= (Apply r s) = (p =@= r) && (q =@= s)
(Lambda x p) =@= (Lambda y q) = substitute p x (Var "_RESERVED") =@= substitute q y (Var "_RESERVED")
_ =@= _ = False

substitute :: LambdaTerm -> String -> LambdaTerm -> LambdaTerm
substitute p@(Var y) x q = if x == y then q else p
substitute (Apply r s) x q = Apply (substitute r x q) (substitute s x q)
substitute p@(Lambda y r) x q = if x == y then p else Lambda y (substitute r x q)

linkers :: LambdaTerm -> [String]
linkers (Var _) = []
linkers (Apply p q) = linkers p ++ linkers q
linkers (Lambda x p) = [x] ++ linkers p

free :: LambdaTerm -> [String]
free (Var x) = [x]
free (Apply p q) = free p `union` free q
free (Lambda x p) = free p \\ [x]

eval :: LambdaTerm -> LambdaTerm
eval v@(Var x) = v
eval (Lambda x p) = Lambda x (eval p)
eval (Apply p@(Lambda x p') q) = substitute p' x q
eval (Apply p q) = Apply (eval p) (eval q)

i :: LambdaTerm
i = Lambda "x" (Var "x")

k :: LambdaTerm
k = Lambda "x" (Lambda "y" (Var "x"))

s :: LambdaTerm
s = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Var "x") (Var "z")) (Apply (Var "y") (Var "z")))))

reduce :: LambdaTerm -> LambdaTerm
reduce a = let a' = eval a
           in if a == a'
              then a' 
              else reduce a'

reduceVerbose :: LambdaTerm -> IO ()
reduceVerbose a = go a [a]
  where
    go a acc = let a' = eval a
               in if a == a'
                  then putStrLn . unlines . reverse . map show $ acc
                  else go a' (a' : acc)

reduceVerbose' :: LambdaTerm -> IO ()
reduceVerbose' a = let a' = eval a
                   in if a == a'
                      then print a'
                      else print a >> reduceVerbose' a'

churchNumeral :: Int -> LambdaTerm
churchNumeral n
    | n < 0 = error "church numerals can only be non-negative"
    | otherwise = Lambda "f" (Lambda "x" (construct n))
  where
    construct :: Int -> LambdaTerm
    construct 0 = Var "x"
    construct n = Apply (Var "f") $ construct (n - 1)

true :: LambdaTerm
true = Lambda "a" (Lambda "b" (Var "a"))

false :: LambdaTerm
false = Lambda "a" (Lambda "b" (Var "b"))

skk :: LambdaTerm
skk = Apply (Apply s k) k

switch :: LambdaTerm
switch = Apply (Apply s (Apply k (Apply s i))) (Apply (Apply s (Apply k k)) i)

y = Lambda "f" (Apply (Lambda "x" (Apply (Var "f") (Apply (Var "x") (Var "x")))) 
                      (Lambda "x" (Apply (Var "f") (Apply (Var "x") (Var "x")))))