module FOL
    ( Funs
    , Term ( Var, Fun )
    , Formula ( Rel, Top, Bot, Neg, Conj, Disj
              , Impl, Eqiv, Exis, Alls )
    , Assigment
    , FnInterp
    , RelInterp
    , Model ( Model )
    , mkConstTerm
    , mkVar
    , substTerm
    , substVar
    , evalTerm
    , evalFormula
    , freeVars
    , unify
    , unifyAndApply
    ) where

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

type Funs = [(String, Int)]

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
    show (Rel r [])     = r
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

mkVar :: String -> Formula
mkVar p = Rel p []

substTerm :: Assigment Term -> Term -> Term
substTerm sigma (Var p)     = Map.findWithDefault (Var p) p sigma
substTerm sigma (Fun f ts)  = Fun f (map (substTerm sigma) ts)

substVar :: String -> String -> Formula -> Formula
substVar x y Top = Top
substVar x y Bot = Bot
substVar x y (Neg f) = Neg (substVar x y f)
substVar x y (Conj f1 f2) = Conj (substVar x y f1) (substVar x y f2)
substVar x y (Disj f1 f2) = Disj (substVar x y f1) (substVar x y f2)
substVar x y (Impl f1 f2) = Impl (substVar x y f1) (substVar x y f2)
substVar x y (Eqiv f1 f2) = Eqiv (substVar x y f1) (substVar x y f2)
substVar x y (Alls z f) = if x == z 
                            then Alls z f 
                            else Alls z (substVar x y f)
substVar x y (Exis z f) = if x == z 
                            then Alls z f
                            else Exis z (substVar x y f)
substVar x y (Rel r ts) = Rel r (map (substVarTerm x y) ts)
    where substVarTerm x y (Var z) = if x == z then Var y else Var z
          substVarTerm x y (Fun f ts) = Fun f (map (substVarTerm x y) ts)

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
evalFormula model sigma (Eqiv f1 f2)    = (not (evalFormula model sigma f1) || (evalFormula model sigma f2)) && ((evalFormula model sigma f1) || not (evalFormula model sigma f2))
evalFormula model sigma (Alls x f)      = all (\val -> evalFormula model (Map.insert x val sigma) f)
                                        $ univ model
evalFormula model sigma (Exis x f)      = any (\val -> evalFormula model (Map.insert x val sigma) f)
                                        $ univ model

freeVars :: Formula -> [String]
freeVars f = freeVars' Set.empty f
    where
        freeVars' :: Set.Set String -> Formula -> [String]
        freeVars' bound (Rel _ ts)   = filter (\t -> Set.notMember t bound) 
                                     $ foldl (++) []
                                     $ map freeVarsTerm ts
        freeVars' bound (Neg f)      = freeVars' bound f
        freeVars' bound (Conj f1 f2) = freeVars' bound f1 ++ freeVars' bound f2
        freeVars' bound (Disj f1 f2) = freeVars' bound f1 ++ freeVars' bound f2
        freeVars' bound (Impl f1 f2) = freeVars' bound f1 ++ freeVars' bound f2
        freeVars' bound (Eqiv f1 f2) = freeVars' bound f1 ++ freeVars' bound f2
        freeVars' bound (Alls x f)   = freeVars' (Set.insert x bound) f
        freeVars' bound (Exis x f)   = freeVars' (Set.insert x bound) f
        freeVars' bound _            = []

        freeVarsTerm :: Term -> [String]
        freeVarsTerm (Var x) = [x]
        freeVarsTerm (Fun _ ts) = foldl1 (++) 
                                $ map freeVarsTerm ts

value :: [(String, Term)] -> String -> Maybe Term
value [] x              = Nothing
value ((x, t) : env) v  = if x == v then Just t else value env x

isTriv :: [(String, Term)] -> String -> Term -> Maybe Bool
isTriv env x (Var y) =
    if x == y then Just True
    else case value env y of
        Just t -> isTriv env x t
        Nothing -> Just False
isTriv env x (Fun f []) = Just False
isTriv env x (Fun f (arg : args)) =
    case isTriv env x arg of
        Just True   -> Nothing
        Just False  -> isTriv env x (Fun f args)
        Nothing     -> Nothing

unify' :: [(String, Term)] -> [(Term, Term)] -> Maybe [(String, Term)]
unify' env [] = Just env
unify' env ((Fun f1 args1, Fun f2 args2) : eqs) =
    if f1 == f2 && length args1 == length args2
        then unify' env $ (zip args1 args2) ++ eqs
        else Nothing
unify' env ((Var x, t) : eqs) =
    case value env x of
        Just s  -> unify' env $ (s, t) : eqs
        Nothing -> case isTriv env x t of
            Just True   -> Nothing
            Just False  -> unify' ((x, t) : env) eqs
            Nothing     -> Nothing
unify' env ((t, Var x) : eqs) = unify' env ((Var x, t) : eqs)

usolve :: [(String, Term)] -> [(String, Term)]
usolve env =
    let sigma   = Map.fromList env
        env'    = map (\(x, t) -> (x, substTerm sigma t)) env
     in if env == env' then env else usolve env'

unify :: [(Term, Term)] -> Maybe [(String, Term)]
unify eqs = case unify' [] eqs of
    Just env    -> Just $ usolve env
    Nothing     -> Nothing

unifyAndApply :: [(Term, Term)] -> Maybe [(Term, Term)]
unifyAndApply eqs = case unify eqs of
    Just env    -> let sigma = Map.fromList env
                    in Just
                     $ map (\(s, t) -> (substTerm sigma s, substTerm sigma t)) eqs
    Nothing     -> Nothing
