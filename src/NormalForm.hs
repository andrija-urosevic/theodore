module NormalForm
    ( Literal (Top, Bot, Pos, Neg)
    , NnfForm (Lit, Conj, Disj)
    , negateLit
    , negateNnf
    ) where

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

instance Show Literal where
    show Top = "⊤"
    show Bot = "⊥"
    show (Pos p) = p
    show (Neg p) = "¬" ++ p

instance Show NnfForm where
    show (Lit l) = show l
    show (Conj f1 f2) = "(" ++ show f1 ++ " ∧ " ++ show f2 ++ ")"
    show (Disj f1 f2) = "(" ++ show f1 ++ " ∨ " ++ show f2 ++ ")"

negateLit :: Literal -> Literal
negateLit Top = Bot
negateLit Bot = Top
negateLit (Pos p) = Neg p
negateLit (Neg p) = Pos p

negateNnf :: NnfForm -> NnfForm
negateNnf (Lit l) = Lit (negateLit l)
negateNnf (Conj f1 f2) = Disj (negateNnf f1) (negateNnf f2)
negateNnf (Disj f1 f2) = Conj (negateNnf f1) (negateNnf f2)

