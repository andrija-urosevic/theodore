module NatDed
    ( Assumption ( Assumption )
    , Assumptions
    , Subgoal ( Subgoal )
    , Goal
    , mkGoal
    , exact
    , intro
    , tear
    , left
    , right
    , iff
    , false
    , free
    , split
    , cases
    , apply
    , equiv
    , turn
    , fix
    , gen
    ) where

import FOL

data Assumption = Assumption { name :: String 
                             , formula :: Formula }

type Assumptions = [Assumption]

type MetaVars = [String]

data Subgoal = Subgoal { mvars :: MetaVars
                       , assms :: Assumptions 
                       , cncls :: Formula }

type Goal = [Subgoal]

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
    if (name a) == assmName then Just a else NatDed.lookup assmName as

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
    Impl f1 f2  -> Subgoal (mvars g) [Assumption assmName f1] f2 : gs
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
apply :: String -> Goal -> Goal
apply assmName []       = error "Nothing to apply apply to!"
apply assmName (g : gs) = Subgoal (mvars g) (delete assmName (assms g)) (left' (assms g))
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
fix mvar assmName (g : gs) = Subgoal (mvars g) (fix' (assms g)) (cncls g) 
                            : gs
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
          insert as = case NatDed.lookup assmName as of
                (Just a) -> case (formula a) of
                    Exis x f -> if notElem mvar (mvars g)
                                then mvar : (mvars g)
                                else error "Invalid rule!"
                    _        -> error "Invalid rule!"
                Nothing  -> error "Invalid rule!"


