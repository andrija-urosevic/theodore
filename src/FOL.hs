module FOL 
    ( Term (Var, Fun)
    , Assigment
    , Interp
    , mkConst
    , substTerm
    , evalTerm
    ) where

import qualified Data.List as List
import qualified Data.Map as Map

data Term 
    = Var String
    | Fun String [Term]
    deriving (Eq, Ord)

type Assigment a = Map.Map String a
type Interp a = Assigment ([a] -> a)

instance Show Term where
    show (Var p)    = p
    show (Fun f []) = f
    show (Fun f ts) = f 
                   ++ "(" 
                   ++ (List.intercalate ", " . map show) ts 
                   ++ ")"

mkConst :: String -> Term
mkConst c = Fun c []

substTerm :: Assigment Term -> Term -> Term
substTerm sigma (Var p)     = Map.findWithDefault (Var p) p sigma
substTerm sigma (Fun f ts)  = Fun f (map (substTerm sigma) ts)

evalTerm :: Interp a -> Assigment a -> Term -> a
evalTerm fn sigma (Var p)       = sigma Map.! p
evalTerm fn sigma (Fun f ts)    = fn Map.! f 
                                $ map (evalTerm fn sigma) 
                                $ ts

