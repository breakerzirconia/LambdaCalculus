module Main where

import Data.Foldable                    (forM_)
import Data.List                as List
import Data.Map                 as Map
import LambdaCalculusEssentials
import Parser
import TypeDeducer

-- given the lambda term represented by a string, 
-- parse the string, and deduce its type via the unification algorithm
main :: IO ()
main = getLine >>= \rawLambdaTerm ->
         let (eqRows, tlt, context) = preliminaryPreparation (parse rawLambdaTerm)
         in case unificationAlgorithm eqRows of
              Nothing     -> putStrLn "Expression has no type"
              Just eqRows -> let eqPairs = Map.fromList $ fmap (\e -> case e of (T i :=: t) -> (i, t)) eqRows
                                 proof = construct tlt 
                                                   eqPairs 
                                                   (Map.map (flip substituteType eqPairs) context) 
                                                   0
                             in forM_ proof putStrLn

construct :: TypedLambdaTerm 
           -> Map Int Type 
           -> Map String Type 
           -> Int 
           -> [String]
construct tlt@(TypedVar x t) eqPairs context indentationLevel = 
  let contextBody = provideContext context indentationLevel
      tltBody = show tlt  ++ " : " ++ show (substituteType t eqPairs) ++ " [rule #1]"
  in [contextBody ++ tltBody]
construct tlt@((:<@>:) p q t) eqPairs context indentationLevel = 
  let contextBody = provideContext context indentationLevel
      tltBody = show tlt  ++ " : " ++ show (substituteType t eqPairs) ++ " [rule #2]"
      pBody = construct p eqPairs context $ succ indentationLevel
      qBody = construct q eqPairs context $ succ indentationLevel
  in [contextBody ++ tltBody] ++ pBody ++ qBody
construct tlt@(TypedL x p t@(t1 :-> _)) eqPairs context indentationLevel = 
  let contextBody = provideContext context indentationLevel
      tltBody = show tlt  ++ " : " ++ show (substituteType t eqPairs) ++ " [rule #3]"
      pBody = construct p eqPairs (Map.insert x (substituteType t1 eqPairs) context) $ succ indentationLevel
  in [contextBody ++ tltBody] ++ pBody

provideContext :: Map.Map String Type -> Int -> String
provideContext context indentationLevel =  
     (List.take (4 * indentationLevel) $ cycle "*   ") 
  ++ (intercalate ", " . fmap (\(k, v) -> k ++ " : " ++ show v) $ Map.toList context)
  ++ (if List.null context then "|- " else " |- ")
