module TypeDeducer where

import LambdaCalculusEssentials         hiding (reduce)
import Data.Map.Strict          as Map
import Data.Set                 as Set
import Data.List                as List

infixr 1 :->

data Type = T Int 
          | Type :-> Type deriving (Eq, Ord)

instance Show Type where
  show (T x)       = "t" ++ show x
  show (t1 :-> t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")" 

infixl 5 :<@>:

data TypedLambdaTerm = TypedVar String Type
                     | (:<@>:) TypedLambdaTerm TypedLambdaTerm Type
                     | TypedL String TypedLambdaTerm Type
                     deriving (Eq, Ord)

instance Show TypedLambdaTerm where
  show (TypedVar s _)  = s
  show ((:<@>:) p q _) = "("   ++ show p ++ " " ++ show q ++ ")"
  show (TypedL x p _)  = "(\\" ++ x ++ ". " ++ show p ++ ")" 

retrieveType :: TypedLambdaTerm -> Type
retrieveType (TypedVar _ t)   = t
retrieveType ((:<@>:) _ _ t)  = t
retrieveType (TypedL _ _ t)   = t

infix 4 :=:

data EqRow = Type :=: Type deriving (Eq, Ord)

instance Show EqRow where
  show (t1 :=: t2) = show t1 ++ " = " ++ show t2

-- ================ --

rightInclusion :: [EqRow] -> Bool
rightInclusion []               = False
rightInclusion (eqRow : eqRows) = case eqRow of
  (T i :=: (t1 :-> t2)) -> go t1 i || go t2 i || rightInclusion eqRows
  _                     -> rightInclusion eqRows
  where
    go :: Type -> Int -> Bool
    go (t1 :-> t2) i = go t1 i || go t2 i
    go (T i)       j = i == j

unificationAlgorithm :: [EqRow] -> Maybe [EqRow]
unificationAlgorithm eqRows
  | rightInclusion eqRows    = Nothing
  | sort next == sort eqRows = Just eqRows
  | otherwise                = unificationAlgorithm next
  where
    next = step2shorten (step1reduce eqRows) Set.empty

step1reduce :: [EqRow] -> [EqRow]
step1reduce [] = []
step1reduce (eqRow : eqRows) = case eqRow of
  (t1 :-> t2) :=: (T i)       -> (T i :=: (t1 :-> t2)) : step1reduce eqRows
  (T i)       :=: (T j)       -> if i == j
                                 then step1reduce eqRows
                                 else eqRow : step1reduce eqRows
  (t1 :-> t2) :=: (t3 :-> t4) -> step1reduce $ (t1 :=: t3) : (t2 :=: t4) : eqRows
  _                           -> eqRow : step1reduce eqRows


step2shorten :: [EqRow] -> Set Int -> [EqRow]
step2shorten eqRows set = case List.find (filterSet set) eqRows of
  Nothing            -> eqRows
  Just f@(T i :=: _) -> step2shorten (f : go (List.delete f eqRows) 
                                             (uncurry Map.singleton $ (\e -> case e of (T i :=: t) -> (i, t)) f))
                                     (Set.insert i set) 
  where
    go :: [EqRow] -> Map Int Type -> [EqRow]
    go []                 _ = []
    go ((t1 :=: t2) : ts) m = (substituteType t1 m :=: substituteType t2 m) : go ts m

    filterSet :: Set Int -> EqRow -> Bool
    filterSet set (T i :=: _) | not $ Set.member i set = True
    filterSet _   _                                    = False

substituteType :: Type -> Map Int Type -> Type
substituteType    (t1 :-> t2) m = substituteType t1 m :-> substituteType t2 m
substituteType me@(T i)       m = if Map.member i m then m Map.! i else me

preliminaryPreparation :: LambdaTerm 
                       -> ( [EqRow]
                          , TypedLambdaTerm
                          , Map.Map String Type
                          )
preliminaryPreparation lt = (\(a, b, c, _, _) -> (a, b, c)) $ go lt 1 Map.empty
  where
    go :: LambdaTerm
       -> Int 
       -> Map String Int 
       -> ( [EqRow]
          , TypedLambdaTerm
          , Map String Type
          , Map String Int
          , Int
          )
    go (Var x) n msi =
      let (t, msi', n') = if x `Map.member` msi
                          then (T $ msi Map.! x, msi, n)
                          else (T n, Map.insert x n msi, n + 1)
      in ( []
         , TypedVar x t
         , Map.singleton x t
         , msi'
         , n'
         )
    go (p :@: q) n msi =
      let (rows , tlt , mst , msi' , n' ) = go p n  msi
          (rows', tlt', mst', msi'', n'') = go q n' msi'
      in ((retrieveType tlt :=: (retrieveType tlt' :-> T n'')) : rows ++ rows'
         , tlt :<@>: tlt' $ T n''
         , mst `Map.union` mst'
         , msi''
         , n'' + 1
         )
    go (L x p) n msi =
      let (rows, tlt, mst, msi', n') = go p (n + 1) (Map.insert x n msi)
      in ( rows
         , TypedL x tlt (T n :-> retrieveType tlt)
         , Map.delete x mst
         , msi'
         , n'
         )