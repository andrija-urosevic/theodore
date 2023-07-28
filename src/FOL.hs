module FOL
    ( Term ( Var, Fun )
    , Formula ( Rel, Top, Bot, Neg, Conj, Disj
              , Impl, Eqiv, Exis, Alls )
    , Assigment
    , FnInterp
    , RelInterp
    , Model ( Model )
    , mkConstTerm
    , substTerm
    , evalTerm
    , evalFormula
    ) where

import qualified Data.List as List
import qualified Data.Map as Map

data Term
    = Var String
    | Fun String [Term]
    deriving (Eq, Ord)

data Formula
    = Top
    | Bot
    | Rel String [Term]
    | Neg Formula
    | Conj Formula Formula
    | Disj Formula Formula
    | Impl Formula Formula
    | Eqiv Formula Formula
    | Alls String Formula
    | Exis String Formula
    deriving (Eq, Ord)

type Assigment a    = Map.Map String a
type FnInterp a     = Assigment ([a] -> a)
type RelInterp a    = Assigment ([a] -> Bool)

data Model a =
    Model { univ :: [a]
          , fn :: FnInterp a
          , rel :: RelInterp a }

instance Show Term where
    show (Var x)    = x
    show (Fun f []) = f
    show (Fun f ts) = f ++ "(" ++ (List.intercalate ", " . map show) ts ++ ")"

instance Show Formula where
    show Top            = "⊤"
    show Bot            = "⊥"
    show (Rel r ts)     = r ++ "(" ++ (List.intercalate ", " . map show) ts ++ ")"
    show (Neg f)        = "(¬ " ++ show f ++ ")"
    show (Conj f1 f2)   = "(" ++ show f1 ++ " ∧ " ++ show f2 ++ ")"
    show (Disj f1 f2)   = "(" ++ show f1 ++ " ∨ " ++ show f2 ++ ")"
    show (Impl f1 f2)   = "(" ++ show f1 ++ " → " ++ show f2 ++ ")"
    show (Eqiv f1 f2)   = "(" ++ show f1 ++ " ↔ " ++ show f2 ++ ")"
    show (Alls x f)     = "∀" ++ x ++ "." ++ show f
    show (Exis x f)     = "∃" ++ x ++ "." ++ show f

mkConstTerm :: String -> Term
mkConstTerm c = Fun c []

substTerm :: Assigment Term -> Term -> Term
substTerm sigma (Var p)     = Map.findWithDefault (Var p) p sigma
substTerm sigma (Fun f ts)  = Fun f (map (substTerm sigma) ts)

evalTerm :: FnInterp a -> Assigment a -> Term -> a
evalTerm _  sigma (Var p)       = sigma Map.! p
evalTerm fn sigma (Fun f ts)    = fn Map.! f
                                $ map (evalTerm fn sigma)
                                $ ts

evalFormula :: Model a -> Assigment a -> Formula -> Bool
evalFormula _     _     Top             = True
evalFormula _     _     Bot             = False
evalFormula model sigma (Rel r ts)      = (rel model) Map.! r
                                        $ map (evalTerm (fn model) sigma) ts
evalFormula model sigma (Neg f)         = not (evalFormula model sigma f)
evalFormula model sigma (Conj f1 f2)    = (evalFormula model sigma f1) && (evalFormula model sigma f2)
evalFormula model sigma (Disj f1 f2)    = (evalFormula model sigma f1) || (evalFormula model sigma f2)
evalFormula model sigma (Impl f1 f2)    = not (evalFormula model sigma f1) || (evalFormula model sigma f2)
evalFormula model sigma (Eqiv f1 f2)    = not (evalFormula model sigma f1) || (evalFormula model sigma f2) && (evalFormula model sigma f1) || not (evalFormula model sigma f2)
evalFormula model sigma (Alls x f)      = all (\val -> evalFormula model (Map.insert x val sigma) f)
                                        $ univ model
evalFormula model sigma (Exis x f)      = any (\val -> evalFormula model (Map.insert x val sigma) f)
                                        $ univ model

