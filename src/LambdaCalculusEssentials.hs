module LambdaCalculusEssentials where

import Data.List ( (\\)
                 , union
                 )

infixl 5 :@:

data LambdaTerm = Var String 
                | LambdaTerm :@: LambdaTerm 
                | L String LambdaTerm 
                deriving Eq

instance Show LambdaTerm where
  show (Var s) = s
  show (p :@: q) = "(" ++ show p ++ " " ++ show q ++ ")"
  show (L x p) = "(\\" ++ x ++ ". " ++ show p ++ ")"

infix 4 =@=
(=@=) :: LambdaTerm -> LambdaTerm -> Bool
p =@= q = go p q 0
  where
    go (Var x) (Var y) _ = x == y
    go (p :@: q) (r :@: s) n = (go p q n) && (go r s n)
    go (L x p) (L y q) n = go (substitute p x (Var $ "_RESERVED" ++ show n)) 
                                        (substitute q y (Var $ "_RESERVED" ++ show n)) (n + 1)
    go _ _ _ = False

substitute :: LambdaTerm -> String -> LambdaTerm -> LambdaTerm
substitute p@(Var y) x q = if x == y then q else p
substitute (r :@: s) x q = (substitute r x q) :@: (substitute s x q)
substitute p@(L y r) x q = if x == y 
                                then p 
                                else L y (substitute r x q)

substituteLiterally :: LambdaTerm -> String -> String -> LambdaTerm
substituteLiterally p@(Var y) x q = if x == y then Var q else p
substituteLiterally (r :@: s) x q = (substituteLiterally r x q) :@: (substituteLiterally s x q)
substituteLiterally p@(L y r) x q = if x == y 
                                         then L q (substituteLiterally r x q)
                                         else L y (substituteLiterally r x q)

linkers :: LambdaTerm -> [String]
linkers (Var _) = []
linkers (p :@: q) = linkers p ++ linkers q
linkers (L x p) = x : linkers p

free :: LambdaTerm -> [String]
free (Var x) = [x]
free (p :@: q) = free p `union` free q
free (L x p) = free p \\ [x]

eval :: LambdaTerm -> LambdaTerm
eval v@(Var x) = v
eval (L x p) = L x (eval p)
eval (p@(L x p') :@: q) 
  = let p'Linkers = linkers p'
        qEverything = linkers q ++ free q
        newp'Linkers = (\(a, b, c) -> reverse a)
                     $ foldl (\(acc, qE, n) x -> if x `elem` qE
                                                 then ((x ++ show n) : acc, qE, n + 1)
                                                 else (x : acc, qE, n + 1)
                             ) ([], qEverything, 0) p'Linkers
        newP = L x $ helperSub p' p'Linkers newp'Linkers
    in if newP == p
       then substitute p' x q
       else newP :@: q
  where
    helperSub p []     []     = p
    helperSub p (x:xs) (y:ys) = helperSub (substituteLiterally p x y) xs ys

eval (p :@: q) = (eval p) :@: (eval q)

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
  | otherwise = L "f" (L "x" (construct n))
  where
    construct :: Int -> LambdaTerm
    construct 0 = Var "x"
    construct n = (Var "f") :@: construct (n - 1)

-- examples --

i :: LambdaTerm
i = L "x" (Var "x")

k :: LambdaTerm
k = L "x" (L "y" (Var "x"))

s :: LambdaTerm
s = L "x" (L "y" (L "z" ((Var "x") :@: (Var "z") :@: ((Var "y") :@: (Var "z")))))

i' :: LambdaTerm
i' = Var "I"

k' :: LambdaTerm
k' = Var "K"

s' :: LambdaTerm
s' = Var "S"

true :: LambdaTerm
true = L "a" (L "b" (Var "a"))

false :: LambdaTerm
false = L "a" (L "b" (Var "b"))

skk :: LambdaTerm
skk = s :@: k :@: k

skk' :: LambdaTerm
skk' = Var "S" :@: Var "K" :@: Var "K"

switch :: LambdaTerm
switch = (s :@: (k :@: (s :@: i))) :@: (s :@: (k :@: k) :@: i)

y = L "f" ((L "x" ((Var "f") :@: ((Var "x") :@: (Var "x")))) :@:
           (L "x" ((Var "f") :@: ((Var "x") :@: (Var "x")))))

turing :: LambdaTerm
turing = (L "x" (L "y" ((Var "y") :@: ((Var "x") :@: (Var "x") :@: (Var "y")))))
     :@: (L "x" (L "y" ((Var "y") :@: ((Var "x") :@: (Var "x") :@: (Var "y")))))

mkPair :: LambdaTerm
mkPair = L "a" (L "b" (L "x" ((Var "x") :@: (Var "a") :@: (Var "b"))))

prL :: LambdaTerm
prL = L "p" ((Var "p") :@: true)

prR :: LambdaTerm
prR = L "p" ((Var "p") :@: false)

case' :: LambdaTerm
case' = L "l" (L "r" (L "c" ((Var "c") :@: (Var "l") :@: (Var "r"))))

inL :: LambdaTerm
inL = L "l" (L "x" (L "y" ((Var "x") :@: (Var "l"))))

inR :: LambdaTerm
inR = L "r" (L "x" (L "y" ((Var "y") :@: (Var "r"))))

-- SK-basis constructor --

toSK :: LambdaTerm -> LambdaTerm
toSK (Var x) = Var x
toSK (p :@: q) = (toSK p) :@: (toSK q)
toSK (L x (Var p)) = if x == p
                     then skk
                     else k :@: (Var p)
toSK (L x (l@(L _ _))) = toSK (L x (toSK l))
toSK (L x (p :@: q)) = s :@: (toSK (L x p)) :@: (toSK (L x q))

toSK' :: LambdaTerm -> LambdaTerm
toSK' (Var x) = Var x
toSK' (p :@: q) = (toSK' p) :@: (toSK' q)
toSK' (L x (Var p)) = if x == p
                      then skk'
                      else k' :@: (Var p)
toSK' (L x (l@(L _ _))) = toSK' (L x (toSK' l))
toSK' (L x (p :@: q)) = s' :@: (toSK' (L x p)) :@: (toSK' (L x q))