module Theodore 
    ( Assumption ( Assumption )
    , Assumptions
    , Subgoal ( Subgoal )
    , Goal
    , Proof ( ToDo
            , Exact 
            , ImplI 
            , ConjI 
            , DisjlI
            , DisjrI
            , EqivI
            , NegI  
            , AllsI 
            , ExisI 
            , ImplE
            , ConjE 
            , DisjE 
            , EqivE
            , NegE  
            , AllsE 
            , ExisE )
    , mkGoal
    , apply
    , genLatexTree
    ) where

import FOL

import qualified Data.List as List

data Assumption = Assumption { name     :: String 
                             , formula  :: Formula }

type Assumptions = [Assumption]

type MetaVars = [String]

data Subgoal = Subgoal { mvars :: MetaVars
                       , assms :: Assumptions 
                       , cncls :: Formula }

type Goal = [Subgoal]

data Proof = ToDo
           | Exact  { assmName  :: String }
           | ImplI  { assmName  :: String
                    , proof     :: Proof }
           | ConjI  { proofA    :: Proof 
                    , proofB    :: Proof }
           | DisjlI { proof     :: Proof }
           | DisjrI { proof     :: Proof }
           | EqivI  { assmName  :: String 
                    , proofA    :: Proof 
                    , proofB    :: Proof }
           | NegI   { assmName  :: String
                    , proof     :: Proof }
           | AllsI  { mvar      :: String
                    , proof     :: Proof }
           | ExisI  { mvar      :: String
                    , proof     :: Proof }
           | ImplE  { assmName  :: String
                    , proofA    :: Proof 
                    , proofB    :: Proof }
           | ConjE  { assmName  :: String
                    , proof     :: Proof }
           | DisjE  { assmName  :: String
                    , proofA    :: Proof
                    , proofB    :: Proof }
           | EqivE  { assmName  :: String
                    , proof     :: Proof }
           | NegE   { assmName  :: String
                    , proof     :: Proof }
           | AllsE  { mvar      :: String
                    , assmName  :: String
                    , proof     :: Proof }
           | ExisE  { mvar      :: String
                    , assmName  :: String
                    , proof     :: Proof }


instance Show Assumption where
    show assm = show (formula assm) ++ " (\ESC[32m" ++ (name assm) ++ "\ESC[0m)"

instance {-# OVERLAPS #-} Show Assumptions where
    show [] = ""
    show (a : as) = "\ESC[34m• \ESC[0m" ++ show a ++ "\n" ++ show as

instance {-# OVERLAPS #-} Show MetaVars where
    show [] = ""
    show (v : vs) = "\ESC[30m- \ESC[0m" ++ v ++ "\n" ++ show vs

instance {-# OVERLAPS #-} Show Subgoal where
    show subgoal = show (mvars subgoal) ++  show (assms subgoal) ++ "\ESC[34m⊢\ESC[0m " ++ show (cncls subgoal)

instance {-# OVERLAPS #-} Show Goal where
    show [] = "Nothing to prove!"
    show goals = "\ESC[1mGoal (" ++ show (length goals) ++ " subgoals):\ESC[0m" ++ show' 1 goals

instance Show Proof where
    show proof = showProof "" proof

showProof :: String -> Proof -> String
showProof append ToDo                       = append ++ "{! !}\n"
showProof append (Exact assm)               = append ++ "Exact (" ++ assm ++ ").\n"
showProof append (ImplI assm proof)         = append ++ "→I (" ++ assm ++ ").\n" ++ showProof append proof
showProof append (ConjI proofA proofB)      = append ++ "∧I:\n" ++ showProof (append ++ "  ")  proofA ++ showProof append proofB
showProof append (DisjlI proof)             = append ++ "∨lI.\n" ++ showProof append proof
showProof append (DisjrI proof)             = append ++ "∨rI.\n" ++ showProof append proof
showProof append (NegI assm proof)          = append ++ "¬I (" ++ assm ++ ").\n" ++ showProof append proof
showProof append (EqivI assm proofA proofB) = append ++ "↔I (" ++ assm ++ "):\n" ++ showProof (append ++ "  ") proofA ++ showProof append proofB
showProof append (AllsI mvar proof)         = append ++ "∀I (" ++ mvar ++ ").\n" ++ showProof append proof
showProof append (ExisI mvar proof)         = append ++ "∃I (" ++ mvar ++ ").\n" ++ showProof append proof
showProof append (ImplE assm proofA proofB) = append ++ "→E (" ++ assm ++ "):\n" ++ showProof (append ++ "  ") proofA ++ showProof append proofB
showProof append (ConjE assm proof)         = append ++ "∧E (" ++ assm ++ ").\n" ++ showProof append proof
showProof append (DisjE assm proofA proofB) = append ++ "∨E (" ++ assm ++ "):\n" ++ showProof (append ++ "  ") proofA ++ showProof append proofB
showProof append (NegE assm proof)          = append ++ "¬E (" ++ assm ++ ").\n" ++ showProof append proof
showProof append (EqivE assm proof)         = append ++ "↔E (" ++ assm ++ ").\n" ++ showProof append proof
showProof append (AllsE mvar assm proof)    = append ++ "∀E (" ++ mvar ++ ", " ++ assm ++ ").\n" ++ showProof append proof
showProof append (ExisE mvar assm proof)    = append ++ "∃E (" ++ mvar ++ ", " ++ assm ++ ").\n" ++ showProof append proof

show' :: Int -> Goal -> String
show' _ [] = ""
show' n (g : gs) = "\n\n\ESC[32m" ++ show n ++ ". subgoal\ESC[0m\n" ++ show g ++ show' (n + 1) gs

find :: String -> Assumptions -> Assumption
find assmName []        = error $ assmName ++ " not in assumptions!"
find assmName (a : as)  = 
    if (name a) == assmName then a else find assmName as

member :: String -> Assumptions -> Bool
member assmName assms   = any ((== assmName) . name) assms

lookup :: String -> Assumptions -> Maybe Assumption
lookup assmName []      = Nothing
lookup assmName (a : as)= 
    if (name a) == assmName then Just a else Theodore.lookup assmName as

delete :: String -> Assumptions -> Assumptions
delete assmName []      = error $ assmName ++ " not in assumptions!"
delete assmName (a : as)= 
    if (name a) == assmName then as else a : delete assmName as

mkGoal :: Assumptions -> Formula -> Goal
mkGoal assms cncls = [ Subgoal [] assms cncls ]

-- Apply assumption
exact :: String -> Goal -> Goal
exact assmName []       = error "Nothing to apply exact to!"
exact assmName (g : gs) = 
    if member assmName (assms g) then gs else error "Invalid rule!"

-- Apply implI
intro :: String -> Goal -> Goal
intro assmName []       = error "Nothing to apply intro to!"
intro assmName (g : gs) = case (cncls g) of
    Impl f1 f2  -> Subgoal (mvars g) (Assumption assmName f1 : assms g) f2 : gs
    _           -> error "Invalid rule!"

-- Apply conjI
tear :: Goal -> Goal
tear []         = error "Nothing to apply exact to!"
tear (g : gs)   = case (cncls g) of
    Conj f1 f2  -> Subgoal (mvars g) (assms g) f1 
                 : Subgoal (mvars g) (assms g) f2 
                 : gs
    _           -> error "Invalid rule!"

-- Apply disjI left
left :: Goal -> Goal
left []         = error "Nothing to apply exact to!"
left (g : gs)   = case (cncls g) of
    Disj f1 f2  -> Subgoal (mvars g) (assms g) f1 : gs
    _           -> error "Invalid rule!"

-- Apply disjI right
right :: Goal -> Goal
right []        = error "Nothing to apply exact to!"
right (g : gs)  = case (cncls g) of
    Disj f1 f2  -> Subgoal (mvars g) (assms g) f2 : gs
    _           -> error "Invalid rule!"

-- Apply eqivI
iff :: String -> Goal -> Goal
iff assmName []       = error "Nothing to apply iff to!"
iff assmName (g : gs) = case (cncls g) of
    Eqiv f1 f2  -> Subgoal (mvars g) (Assumption assmName f1 : assms g) f2 
                 : Subgoal (mvars g) (Assumption assmName f2 : assms g) f1 
                 : gs
    _           -> error "Invalid rule!"

-- Apply negI
false :: String -> Goal -> Goal
false assmName []       = error "Nothing to apply false to!"
false assmName (g : gs) = case (cncls g) of
    Neg f       -> Subgoal (mvars g) (Assumption assmName f  : assms g) Bot 
                 : gs
    _           -> error "Invalid rule!"

-- Apply allI
free :: String -> Goal -> Goal
free mvar [] = error "Nothing to apply free to!"
free mvar (g : gs) = case (cncls g) of
    Alls x f    -> if (notElem mvar (mvars g)) 
                   then Subgoal 
                            (mvar : mvars g) 
                            (assms g) 
                            (substVar x mvar f) 
                      : gs
                   else error "Invalid rule!"
    _           -> error "Invalid rule!"

-- Apply exI
set :: String -> Goal -> Goal
set mvar [] = error "Nothing to apply set to!"
set mvar (g : gs) = case (cncls g) of
    Exis x f    -> if (elem mvar (mvars g))
                   then Subgoal
                            (mvars g)
                            (assms g)
                            (substVar x mvar f)
                      : gs
                   else error "Invalid rule!"
    _           -> error "Invalid rule!"

-- Apply conjE
split :: String -> Goal -> Goal
split assmName []       = error "Nothing to apply split to!"
split assmName (g : gs) = Subgoal (mvars g) (split' (assms g)) (cncls g) : gs
    where split' []         = error "Invalid rule!"
          split' (a : as)   = 
            if (name a) == assmName 
                then (split'' a) ++ as 
                else a : split' as
          split'' assm      = case (formula assm) of
            Conj f1 f2      -> [ Assumption (name assm ++ "1") f1
                               , Assumption (name assm ++ "2") f2 ]
            _               -> error "Invalid rule!"

-- Apply disjE
cases :: String -> Goal -> Goal
cases assmName []       = error "Nothing to apply cases to!"
cases assmName (g : gs) = Subgoal (mvars g) (left' (assms g)) (cncls g) 
                        : Subgoal (mvars g) (right'(assms g)) (cncls g) 
                        : gs
    where left' []          = error "Invalid rule!"
          left' (a : as)    = 
            if (name a) == assmName
                then left'' a : as
                else a : left' as
          left'' assm   = case (formula assm) of
            Disj f1 f2      -> Assumption assmName f1
            _               -> error "Invalid rule!"
          right' []         = error "Invalid rule!"
          right' (a : as)   =
            if (name a) == assmName
                then right'' a : as
                else a : right' as
          right'' assm      = case (formula assm) of
            Disj f1 f2      -> Assumption assmName f2
            _               -> error "Invalid rule!"

-- Apply impE
have :: String -> Goal -> Goal
have assmName []       = error "Nothing to apply have to!"
have assmName (g : gs) = Subgoal (mvars g) (delete assmName (assms g)) (left' (assms g))
                        : Subgoal (mvars g) (right' (assms g)) (cncls g)
                        : gs
    where left' as          =  
            let f = find assmName as
             in case (formula f) of
                Impl f1 f2  -> f1
                _           -> error "Invalid rule!"
          right' []         = error "Invalid rule!"
          right' (a : as)   = 
            if (name a) == assmName 
                then (right'' a) : as
                else a : right' as
          right'' assm      = case (formula assm) of
            Impl f1 f2      -> Assumption (name assm) f2
            _               -> error "Invalid rule!"

-- Apply eqivE
equiv :: String -> Goal -> Goal
equiv assmName []       = error "Nothing to apply equiv to!"
equiv assmName (g : gs) = Subgoal (mvars g) (split' (assms g)) (cncls g) : gs
    where split' []         = error "Invalid rule!"
          split' (a : as)   = 
            if (name a) == assmName
                then (split'' a) ++ as
                else a : split' as
          split'' assm      = case (formula assm) of
            Eqiv f1 f2      -> [ Assumption (name assm ++ "1") (Impl f1 f2)
                               , Assumption (name assm ++ "2") (Impl f2 f1) ]
            _               -> error "Invalid rule!"

-- Apply notE
turn :: String -> Goal -> Goal
turn assmName []        = error "Nothing to applt turn to!"
turn assmName (g : gs)  = Subgoal 
                            (mvars g) 
                            (delete assmName (assms g)) 
                            (subneg (assms g)) 
                        : gs
    where subneg as     = 
            let f = find assmName as 
             in case (formula f) of
                Neg f1  -> f1
                _       -> error "Invalid rule!"

-- Apply allE
fix :: String -> String -> Goal -> Goal
fix mvar assmName [] = error "Nothing to apply fix to!"
fix mvar assmName (g : gs) = if elem mvar (mvars g) 
                                then Subgoal (mvars g) (fix' (assms g)) (cncls g) 
                                     : gs
                                else error "Invalid meta var!"
    where fix' [] = error "Invalid rule!"
          fix' (a : as) =
            if (name a) == assmName
                then case (formula a) of
                    Alls x f -> Assumption assmName (substVar x mvar f) : as
                    _        -> error "Invalid rule!"
                else a : fix' as

-- Apply exE
gen :: String -> String -> Goal -> Goal
gen mvar assmName [] = error "Nothing to apply gen to!"
gen mvar assmName (g : gs) = Subgoal 
                                (insert (assms g)) 
                                (gen' (assms g)) 
                                (cncls g)
                            : gs
    where gen' [] = error "Invalid rule!"
          gen' (a : as) =
            if (name a) == assmName
                then case (formula a) of
                    Exis x f -> if notElem mvar (mvars g)
                                then Assumption assmName (substVar x mvar f) : as
                                else error "Invalid rule!"
                    _        -> error "Invalid rule!"
                else a : gen' as
          insert as = 
            case Theodore.lookup assmName as of
                (Just a) -> case (formula a) of
                    Exis x f -> if notElem mvar (mvars g)
                                then mvar : (mvars g)
                                else error "Invalid rule!"
                    _        -> error "Invalid rule!"
                Nothing  -> error "Invalid rule!"

apply :: Proof -> Goal -> Goal
apply ToDo                          goal = goal
apply (Exact assm)                  goal = exact assm goal
apply (ImplI assm proof)            goal = apply proof (intro assm goal)
apply (ConjI proofA proofB)         goal = apply proofB (apply proofA (tear goal))
apply (DisjlI proof)                goal = apply proof (left goal)
apply (DisjrI proof)                goal = apply proof (right goal)
apply (EqivI assm proofA proofB)    goal = apply proofB (apply proofA (iff assm goal))
apply (NegI assm proof)             goal = apply proof (false assm goal)
apply (AllsI mvar proof)            goal = apply proof (free mvar goal)
apply (ExisI mvar proof)            goal = apply proof (set mvar goal)
apply (ImplE assm proofA proofB)    goal = apply proofB (apply proofA (have assm goal))
apply (ConjE assm proof)            goal = apply proof (split assm goal)
apply (DisjE assm proofA proofB)    goal = apply proofB (apply proofA (cases assm goal))
apply (EqivE assm proof)            goal = apply proof (equiv assm goal)
apply (NegE assm proof)             goal = apply proof (turn assm goal)
apply (AllsE mvar assm proof)       goal = apply proof (fix mvar assm goal)
apply (ExisE mvar assm proof)       goal = apply proof (gen mvar assm goal)

mathTexMetaVars :: MetaVars -> String
mathTexMetaVars mvars = List.intercalate ", " mvars

mathTexAssumption :: Assumption -> String
mathTexAssumption (Assumption _ f) = mathTexFormula f

mathTexAssumptions :: Assumptions -> String
mathTexAssumptions assms = (List.intercalate ", " . map mathTexAssumption) assms

mathTexSubgoal :: Subgoal -> String
mathTexSubgoal (Subgoal [] assms cncls)     = mathTexAssumptions assms 
                                           ++ " \\vdash " 
                                           ++ mathTexFormula cncls
mathTexSubgoal (Subgoal mvars assms cncls)  = mathTexMetaVars mvars 
                                           ++ "; " 
                                           ++ mathTexAssumptions assms 
                                           ++ " \\vdash " 
                                           ++ mathTexFormula cncls

latexTree :: Proof -> Goal -> String
latexTree ToDo                          _    = "%ToDo\n"
latexTree (Exact assm)                  goal = "\\AxiomC{}\n\\RightLabel{$\\mathsf{asm}$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (ImplI assm proof)            goal = latexTree proof (intro assm goal) 
                                            ++ "\\RightLabel{$\\implies_I$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (ConjI proofA proofB)         goal = latexTree proofB (apply proofA (tear goal))
                                            ++ latexTree proofA (tear goal) 
                                            ++ "\\RightLabel{$\\land_I$}\n\\BinaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (DisjlI proof)                goal = latexTree proof (left goal)
                                            ++ "\\RightLabel{$\\lor_{I_l}$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (DisjrI proof)                goal = latexTree proof (right goal)
                                            ++ "\\RightLabel{$\\lor_{I_r}$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (EqivI assm proofA proofB)    goal = latexTree proofB (apply proofA (iff assm goal))
                                            ++ latexTree proofA (iff assm goal) 
                                            ++ "\\RightLabel{$\\equiv_I$}\n\\BinaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (NegI assm proof)             goal = latexTree proof (false assm goal)
                                            ++ "\\RightLabel{$\\neg_I$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (AllsI mvar proof)            goal = latexTree proof (free mvar goal)
                                            ++ "\\RightLabel{$\\forall_I(" ++ mvar ++ ")$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (ExisI mvar proof)            goal = latexTree proof (set mvar goal)
                                            ++ "\\RightLabel{$\\exists_I(" ++ mvar ++ ")$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (ImplE assm proofA proofB)    goal = latexTree proofB (apply proofA (have assm goal))
                                            ++ latexTree proofA (have assm goal)
                                            ++ "\\RightLabel{$\\implies_E$}\n\\BinaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n" 
latexTree (ConjE assm proof)            goal = latexTree proof (split assm goal)
                                            ++ "\\RightLabel{$\\land_E$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (DisjE assm proofA proofB)    goal = latexTree proofB (apply proofA (cases assm goal))
                                            ++ latexTree proofA (cases assm goal) 
                                            ++ "\\RightLabel{$\\lor_E$}\n\\BinaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n" 
latexTree (EqivE assm proof)            goal = latexTree proof (equiv assm goal)
                                            ++ "\\RightLabel{$\\equiv_E$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (NegE assm proof)             goal = latexTree proof (turn assm goal)
                                            ++ "\\RightLabel{$\\neg_E$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (AllsE mvar assm proof)       goal = latexTree proof (fix mvar assm goal)
                                            ++ "\\RightLabel{$\\forall_E(" ++ mvar ++ ")$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"
latexTree (ExisE mvar assm proof)       goal = latexTree proof (gen mvar assm goal)
                                            ++ "\\RightLabel{$\\exists_E(" ++ mvar ++ ")$}\n\\UnaryInfC{$" ++ mathTexSubgoal (head goal) ++ "$}\n"

genLatexTree :: Proof -> Goal -> IO ()
genLatexTree proof goal = 
    case apply proof goal of
    []  -> do
        putStr "\\begin{prooftree}\n"
        putStr (latexTree proof goal)
        putStr "\\end{prooftree}\n"
    _   -> error "Invalid proof!"
