module NatDed
    ( Assumption ( Assumption )
    , Assumptions
    , Subgoal ( Subgoal )
    , Goal
    , exact
    , intro
    , tear
    , left
    , right
    , iff
    , false
    , split
    , cases
    , apply
    , equiv
    , turn
    ) where

import FOL

data Assumption = Assumption { name :: String 
                             , formula :: Formula }

type Assumptions = [Assumption]

data Subgoal = Subgoal { assms :: Assumptions 
                       , cncls :: Formula } -- TODO: meta vars 

type Goal = [Subgoal]

instance Show Assumption where
    show assm = show (formula assm) ++ " (\ESC[32m" ++ (name assm) ++ "\ESC[0m)"

instance {-# OVERLAPS #-} Show Assumptions where
    show [] = ""
    show (a : as) = "\ESC[34m• \ESC[0m" ++ show a ++ "\n" ++ show as

instance {-# OVERLAPS #-} Show Subgoal where
    show subgoal = show (assms subgoal) ++ "\ESC[34m⊢\ESC[0m " ++ show (cncls subgoal)
    -- TODO: show meta vars

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

-- Apply assumption
exact :: String -> Goal -> Goal
exact assmName []       = error "Nothing to apply exact to!"
exact assmName (g : gs) = 
    if member assmName (assms g) then gs else error "Invalid rule!"

-- Apply implI
intro :: String -> Goal -> Goal
intro assmName []       = error "Nothing to apply intro to!"
intro assmName (g : gs) = case (cncls g) of
    Impl f1 f2  -> Subgoal [Assumption assmName f1] f2 : gs
    _           -> error "Invalid rule!"

-- Apply conjI
tear :: Goal -> Goal
tear []         = error "Nothing to apply exact to!"
tear (g : gs)   = case (cncls g) of
    Conj f1 f2  -> Subgoal (assms g) f1 : Subgoal (assms g) f2 : gs
    _           -> error "Invalid rule!"

-- Apply disjI left
left :: Goal -> Goal
left []         = error "Nothing to apply exact to!"
left (g : gs)   = case (cncls g) of
    Disj f1 f2  -> Subgoal (assms g) f1 : gs
    _           -> error "Invalid rule!"

-- Apply disjI right
right :: Goal -> Goal
right []        = error "Nothing to apply exact to!"
right (g : gs)  = case (cncls g) of
    Disj f1 f2  -> Subgoal (assms g) f2 : gs
    _           -> error "Invalid rule!"

-- Apply eqivI
iff :: String -> Goal -> Goal
iff assmName []       = error "Nothing to apply iff to!"
iff assmName (g : gs) = case (cncls g) of
    Eqiv f1 f2  -> Subgoal (Assumption assmName f1 : assms g) f2 
                 : Subgoal (Assumption assmName f2 : assms g) f1 
                 : gs
    _           -> error "Invalid rule!"

-- Apply negI
false :: String -> Goal -> Goal
false assmName []       = error "Nothing to apply false to!"
false assmName (g : gs) = case (cncls g) of
    Neg f       -> Subgoal (Assumption assmName f  : assms g) Bot : gs
    _           -> error "Invalid rule!"

-- Apply conjE
split :: String -> Goal -> Goal
split assmName []       = error "Nothing to apply split to!"
split assmName (g : gs) = Subgoal (split' (assms g)) (cncls g) : gs
    where split' []         = error "Invalid rule!"
          split' (a : as)   = 
            if (name a) == assmName 
                then (split'' a) ++ as 
                else a : split' as
          split'' assm      = case (formula assm) of
            Conj f1 f2      -> [ Assumption (name assm ++ "1") f1
                               , Assumption (name assm ++ "2") f2 ]
            _               -> error "Invalid rule!"

-- disjE
cases :: String -> Goal -> Goal
cases assmName []       = error "Nothing to apply cases to!"
cases assmName (g : gs) = Subgoal (left' (assms g)) (cncls g) 
                        : Subgoal (right'(assms g)) (cncls g) 
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

-- impE
apply :: String -> Goal -> Goal
apply assmName []       = error "Nothing to apply apply to!"
apply assmName (g : gs) = Subgoal (delete assmName (assms g)) (left' (assms g))
                        : Subgoal (right' (assms g)) (cncls g)
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
-- eqivE
equiv :: String -> Goal -> Goal
equiv assmName []       = error "Nothing to apply equiv to!"
equiv assmName (g : gs) = Subgoal (split' (assms g)) (cncls g) : gs
    where split' []         = error "Invalid rule!"
          split' (a : as)   = 
            if (name a) == assmName
                then (split'' a) ++ as
                else a : split' as
          split'' assm      = case (formula assm) of
            Eqiv f1 f2      -> [ Assumption (name assm ++ "1") (Impl f1 f2)
                               , Assumption (name assm ++ "2") (Impl f2 f1) ]
            _               -> error "Invalid rule!"

-- notE
turn :: String -> Goal -> Goal
turn assmName []        = error "Nothing to applt turn to!"
turn assmName (g : gs)  = Subgoal (delete assmName (assms g)) (subneg (assms g)) : gs
    where subneg as     = 
            let f = find assmName as 
             in case (formula f) of
                Neg f1  -> f1
                _       -> error "Invalid rule!"

