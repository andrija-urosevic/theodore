module Propositional
    ( Vars
    , PropFormula (Top, Bot, Var, Neg, Conj, Disj, Impl, Eqiv)
    , PartialValuation
    , complexity
    , depth
    , vars
    , subformulas
    , eval
    , truthTable
    , isSat
    , isValid
    ) where

import qualified Data.List as List
import qualified Data.Map as Map

type Vars = [String]

type PartialValuation = Map.Map String Bool

data PropFormula 
    = Top
    | Bot
    | Var String
    | Neg PropFormula
    | Conj PropFormula PropFormula
    | Disj PropFormula PropFormula
    | Impl PropFormula PropFormula
    | Eqiv PropFormula PropFormula
    deriving (Eq, Ord)

toString :: PropFormula -> String
toString Top            = "⊤"
toString Bot            = "⊥"
toString (Var p)        = p
toString (Neg f)        = "(¬ " ++ toString f ++ ")"
toString (Conj f1 f2)   = "(" ++ toString f1 ++ " ∧ " ++ toString f2 ++ ")"
toString (Disj f1 f2)   = "(" ++ toString f1 ++ " ∨ " ++ toString f2 ++ ")"
toString (Impl f1 f2)   = "(" ++ toString f1 ++ " → " ++ toString f2 ++ ")"
toString (Eqiv f1 f2)   = "(" ++ toString f1 ++ " ↔ " ++ toString f2 ++ ")"

instance Show PropFormula where
    show = toString

-- TODO: instance Read PropFormula ...

mkPartialValuation :: [String] -> PartialValuation
mkPartialValuation xs = let pairs = map (\x -> (x, True)) xs
                         in Map.fromList pairs

evalVar :: String -> PartialValuation -> Bool
evalVar p v = Map.findWithDefault False p v

complexity :: PropFormula -> Int
complexity Top          = 0
complexity Bot          = 0
complexity (Var _)      = 0
complexity (Neg f)      = 1 + complexity f
complexity (Conj f1 f2) = 1 + complexity f1 + complexity f2
complexity (Disj f1 f2) = 1 + complexity f1 + complexity f2
complexity (Impl f1 f2) = 1 + complexity f1 + complexity f2
complexity (Eqiv f1 f2) = 1 + complexity f1 + complexity f2

depth :: PropFormula -> Int
depth Top           = 0
depth Bot           = 0
depth (Var _)       = 0
depth (Neg f)       = 1 + depth f
depth (Conj f1 f2)  = 1 + max (depth f1) (depth f2)
depth (Disj f1 f2)  = 1 + max (depth f1) (depth f2)
depth (Impl f1 f2)  = 1 + max (depth f1) (depth f2)
depth (Eqiv f1 f2)  = 1 + max (depth f1) (depth f2)

vars :: PropFormula -> Vars
vars Top            = []
vars Bot            = []
vars (Var p)        = [p]
vars (Neg f)        = vars f
vars (Conj f1 f2)   = List.union (vars f1) (vars f2)
vars (Disj f1 f2)   = List.union (vars f1) (vars f2)
vars (Impl f1 f2)   = List.union (vars f1) (vars f2)
vars (Eqiv f1 f2)   = List.union (vars f1) (vars f2)

subformulas :: PropFormula -> [PropFormula]
subformulas Top             = [Top]
subformulas Bot             = [Bot]
subformulas (Var p)         = [Var p]
subformulas (Neg f)         = (Neg f) : subformulas f
subformulas (Conj f1 f2)    = (Conj f1 f2) : subformulas f1 ++ subformulas f2
subformulas (Disj f1 f2)    = (Disj f1 f2) : subformulas f1 ++ subformulas f2
subformulas (Impl f1 f2)    = (Impl f1 f2) : subformulas f1 ++ subformulas f2
subformulas (Eqiv f1 f2)    = (Eqiv f1 f2) : subformulas f1 ++ subformulas f2

eval :: PropFormula -> PartialValuation -> Bool
eval Top _          = True
eval Bot _          = False
eval (Var p) v      = Map.findWithDefault False p v
eval (Neg f) v      = not (eval f v)
eval (Conj f1 f2) v = (eval f1 v) && (eval f2 v)
eval (Disj f1 f2) v = (eval f1 v) || (eval f2 v)
eval (Impl f1 f2) v = not (eval f1 v) || (eval f2 v)
eval (Eqiv f1 f2) v = (not (eval f1 v) || (eval f2 v)) && ((eval f1 v) || not (eval f2 v))

sublists :: [a] -> [[a]]
sublists [] = [[]]
sublists (x : xs) = let sub = sublists xs
                     in map (\a -> x : a) sub ++ sub

truthTable :: PropFormula -> [([Bool], Bool)]
truthTable f = let varSet       = vars f
                   valuations   = map mkPartialValuation (sublists varSet)
                   evaluate     = \v -> (map (\p -> evalVar p v) varSet, eval f v)
                in map evaluate valuations

isSat :: PropFormula -> Bool
isSat f = any snd (truthTable f)

isValid :: PropFormula -> Bool
isValid f = all snd (truthTable f)
