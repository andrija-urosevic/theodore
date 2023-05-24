module NormalForm
    ( Literal (Top, Bot, Pos, Neg)
    , NnfForm (Lit, Conj, Disj)
    , Clause
    , CnfForm
    , negateLit
    , negateNnf
    , fromNnfToCnf
    , toNnfForm
    , toCnfForm
    , evalLiteral
    , evalClause
    , evalCnf
    , evalNnf
    ) where

import qualified Propositional as Prop
import qualified Data.List as List

data Literal
    = Top
    | Bot
    | Pos String
    | Neg String
    deriving (Eq, Ord)

data NnfForm
    = Lit Literal
    | Conj NnfForm NnfForm
    | Disj NnfForm NnfForm
    deriving (Eq, Ord)

type Clause = [Literal]
type CnfForm = [Clause]

instance Show Literal where
    show Top        = "⊤"
    show Bot        = "⊥"
    show (Pos p)    = p
    show (Neg p)    = "¬" ++ p

instance Show NnfForm where
    show (Lit l)        = show l
    show (Conj f1 f2)   = "(" ++ show f1 ++ " ∧ " ++ show f2 ++ ")"
    show (Disj f1 f2)   = "(" ++ show f1 ++ " ∨ " ++ show f2 ++ ")"

instance {-# OVERLAPS #-} Show Clause where
    show []     = ""
    show (l:[]) = show l 
    show (l:ls) = show l ++ " ∨ " ++ show ls

instance {-# OVERLAPS #-} Show CnfForm where
    show []     = ""
    show (c:[]) = "(" ++ show c ++ ")"
    show (c:cs) = "(" ++ show c ++ ")" ++ " ∧ " ++ show cs

negateLit :: Literal -> Literal
negateLit Top       = Bot
negateLit Bot       = Top
negateLit (Pos p)   = Neg p
negateLit (Neg p)   = Pos p

negateNnf :: NnfForm -> NnfForm
negateNnf (Lit l)       = Lit (negateLit l)
negateNnf (Conj f1 f2)  = Disj (negateNnf f1) (negateNnf f2)
negateNnf (Disj f1 f2)  = Conj (negateNnf f1) (negateNnf f2)

toNnfForm :: Prop.PropFormula -> NnfForm
toNnfForm Prop.Top          = Lit Top
toNnfForm Prop.Bot          = Lit Bot
toNnfForm (Prop.Var p)      = Lit (Pos p)
toNnfForm (Prop.Neg f)      = negateNnf (toNnfForm f)
toNnfForm (Prop.Conj f1 f2) = Conj (toNnfForm f1) (toNnfForm f2)
toNnfForm (Prop.Disj f1 f2) = Disj (toNnfForm f1) (toNnfForm f2)
toNnfForm (Prop.Impl f1 f2) = Disj (negateNnf (toNnfForm f1)) (toNnfForm f2)
toNnfForm (Prop.Eqiv f1 f2) = Conj (Disj (negateNnf (toNnfForm f1)) (toNnfForm f2))
                                   (Disj (negateNnf (toNnfForm f2)) (toNnfForm f1))

disjCnf :: CnfForm -> CnfForm -> CnfForm
disjCnf cnf1 cnf2 = foldr List.union [] 
                  $ map (\cls -> map (List.union cls) cnf2) cnf1

conjCnf :: CnfForm -> CnfForm -> CnfForm
conjCnf = List.union

fromNnfToCnf :: NnfForm -> CnfForm
fromNnfToCnf (Lit Top)      = []
fromNnfToCnf (Lit Bot)      = [[]]
fromNnfToCnf (Lit (Pos p))  = [[Pos p]]
fromNnfToCnf (Lit (Neg p))  = [[Neg p]]
fromNnfToCnf (Conj f1 f2)   = conjCnf (fromNnfToCnf f1) (fromNnfToCnf f2)
fromNnfToCnf (Disj f1 f2)   = disjCnf (fromNnfToCnf f1) (fromNnfToCnf f2)

toCnfForm :: Prop.PropFormula -> CnfForm
toCnfForm = fromNnfToCnf . toNnfForm

evalLiteral :: Literal -> Prop.PartialValuation -> Bool
evalLiteral Top _       = True
evalLiteral Bot _       = False
evalLiteral (Pos p) v   = Prop.evalVar p v
evalLiteral (Neg p) v   = not $ Prop.evalVar p v

evalClause :: Clause -> Prop.PartialValuation -> Bool
evalClause [] _         = False
evalClause (l : ls) v   = evalLiteral l v || evalClause ls v

evalCnf :: CnfForm -> Prop.PartialValuation -> Bool
evalCnf [] _        = True
evalCnf (c : cs) v  = evalClause c v && evalCnf cs v

evalNnf :: NnfForm -> Prop.PartialValuation -> Bool
evalNnf (Lit l) v       = evalLiteral l v
evalNnf (Conj f1 f2) v  = evalNnf f1 v && evalNnf f2 v
evalNnf (Disj f1 f2) v  = evalNnf f1 v || evalNnf f2 v


