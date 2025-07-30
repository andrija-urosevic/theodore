{-# LANGUAGE TypeSynonymInstances #-}
 
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Data.Set as Set
import qualified Data.Map as Map

import Propositional as Prop
import NormalForm as NormalForm
import FOL as FOL
import Theodore as Theodore

main :: IO ()
main = defaultMain tests

propExample :: PropFormula
propExample = Prop.Impl (Prop.Conj (Prop.Var "p") (Prop.Var "q")) (Prop.Impl (Prop.Disj (Prop.Conj (Prop.Var "r") (Prop.Var "p")) (Prop.Neg (Prop.Var "s1"))) (Prop.Var "s2"))

valuationExample :: PartialValuation
valuationExample = Map.fromList [("p", True), ("q", True), ("r", True)]

p :: Literal
p = NormalForm.Pos "p"

q :: Literal
q = NormalForm.Pos "q"

negr :: Literal
negr = NormalForm.Neg "r"

nnfExample :: NnfForm
nnfExample = NormalForm.Conj (NormalForm.Disj (NormalForm.Lit p) (NormalForm.Lit negr)) (NormalForm.Disj (NormalForm.Lit q) (NormalForm.Lit NormalForm.Bot))

nnfExample1 :: NnfForm
nnfExample1 = NormalForm.Conj (NormalForm.Lit (NormalForm.Bot)) (NormalForm.Lit (NormalForm.Neg "p"))

exClause0 :: Clause
exClause0 = [NormalForm.Pos "p"]

exClause1 :: Clause
exClause1 = [NormalForm.Pos "p", NormalForm.Neg "q", NormalForm.Pos "r"]

exClause2 :: Clause
exClause2 = [NormalForm.Pos "r", NormalForm.Neg "s"]

exCnf0 :: CnfForm
exCnf0 = 
    [ [NormalForm.Pos "p"]
    , [NormalForm.Neg "p", NormalForm.Pos "q", NormalForm.Neg "r"]
    , [NormalForm.Neg "p", NormalForm.Neg "q"]
    ]

exCnf1 :: CnfForm
exCnf1 =
    [ [NormalForm.Pos "p", NormalForm.Neg "q"]
    , [NormalForm.Pos "p", NormalForm.Pos "q"]
    , [NormalForm.Neg "p", NormalForm.Neg "r"]
    , [NormalForm.Neg "p", NormalForm.Pos "r"]
    ]

exCnf2 :: CnfForm
exCnf2 =
    [ [NormalForm.Pos "p", NormalForm.Pos "q"]
    , [NormalForm.Neg "p"]
    , [NormalForm.Neg "q"]
    ]

binAirthInterp :: FnInterp Bool
binAirthInterp = Map.fromList
    [ ("+", \ args -> (args !! 0) /= (args !! 1))
    , ("*", \ args -> (args !! 0) && (args !! 1))
    , ("0", \ _    -> False)
    , ("1", \ _    -> True)
    ]

bitArithAssigment :: Assigment Bool
bitArithAssigment = Map.fromList
    [ ("p", True)
    , ("q", False)
    ]

bitArithTerm :: Term
bitArithTerm =
    FOL.Fun "+"
    [ FOL.Fun "+" [FOL.Var "p", mkConstTerm "0"]
    , FOL.Fun "*" [FOL.Var "p", FOL.Var "q"]
    ]

f1 :: Formula
f1 = FOL.Rel "even" [FOL.Var "x"]

f2 :: Formula
f2 = FOL.Rel "odd" [FOL.Var "x"]

f3 :: Formula
f3 = FOL.Alls "x" (FOL.Impl
        (FOL.Rel "even" [FOL.Var "x"])
        (FOL.Rel "eq" [FOL.Var "x", mkConstTerm "zero"])
    )

f4 :: Formula
f4 = FOL.Alls "x" (FOL.Impl
        (FOL.Neg (FOL.Rel "even" [FOL.Var "x"]))
        (FOL.Exis "y" (FOL.Rel "lt" [FOL.Var "x", FOL.Var "y"]))
    )

babyArithModel :: Model Int
babyArithModel = Model
    [0..9]
    ( Map.fromList
    [ ("+",     \args -> args !! 0 + args !! 1 `mod` 10)
    , ("*",     \args -> args !! 0 * args !! 1 `mod` 10) 
    , ("zero",  \_ -> 0)
    , ("one",   \_ -> 1)
    , ("two",   \_ -> 2)
    , ("three", \_ -> 3)
    , ("four",  \_ -> 4)
    , ("five",  \_ -> 5)
    , ("six",   \_ -> 6)
    , ("seven", \_ -> 7)
    , ("eight", \_ -> 8)
    , ("nine",  \_ -> 9)
    ])
    ( Map.fromList
    [ ("eq",    \args -> args !! 0 == args !! 1)
    , ("lt",    \args -> args !! 0 < args !! 1)
    , ("even",  \args -> even $ args !! 0)
    ])

-- even(x)
babyFormula1 :: Formula
babyFormula1 = FOL.Rel "even" [FOL.Var "x"]

-- ∃y. lt(x, y)
babyFormula2 :: Formula
babyFormula2 = FOL.Exis "y" (FOL.Rel "lt" [FOL.Var "x", FOL.Var "y"])

-- even(two)
babyFormula3 :: Formula
babyFormula3 = FOL.Rel "even" [mkConstTerm "two"]

-- even(three)
babyFormula4 :: Formula
babyFormula4 = FOL.Rel "even" [mkConstTerm "three"]

-- ∃x. even(%x)
babyFormula5 :: Formula
babyFormula5 = FOL.Exis "x" (FOL.Rel "even" [FOL.Var "x"])

-- ∀x. even(%x)
babyFormula6 :: Formula
babyFormula6 = FOL.Alls "x" (FOL.Rel "even" [FOL.Var "x"])

-- ∃x. lt(x, two) ∧ even(x)
babyFormula7 :: Formula
babyFormula7 =
    FOL.Exis "x" (FOL.Conj
        (FOL.Rel "lt" [FOL.Var "x", mkConstTerm "two"])
        (FOL.Rel "even" [FOL.Var "x"])
    )

-- ∃x. ∃y. lt(x, y) ∧ lt(y, two) ∧ even(x) ∧ even(y)
babyFormula8 :: Formula
babyFormula8 =
    FOL.Exis "x" (FOL.Exis "y" (FOL.Conj
        (FOL.Conj
            (FOL.Conj
                (FOL.Rel "lt" [FOL.Var "x", FOL.Var "y"])
                (FOL.Rel "lt" [FOL.Var "y", mkConstTerm "two"])
            )
            (FOL.Rel "even" [FOL.Var "x"])
        )
        (FOL.Rel "even" [FOL.Var "y"])
    ))

-- ∀x. even(x) ∧ lt(x, two) → x = zero
babyFormula9 :: Formula
babyFormula9 =
    FOL.Alls "x" (FOL.Impl
        (FOL.Conj
            (FOL.Rel "even" [FOL.Var "x"])
            (FOL.Rel "lt" [FOL.Var "x", mkConstTerm "two"])
        )
        (FOL.Rel "eq" [FOL.Var "x", mkConstTerm "zero"])
    )

-- ∀x. even(x) ∧ lt(x,three) → x = zero
babyFormula10 :: Formula
babyFormula10 =
    FOL.Alls "x" (FOL.Impl
        (FOL.Conj
            (FOL.Rel "even" [FOL.Var "x"])
            (FOL.Rel "lt" [FOL.Var "x", mkConstTerm "three"])
        )
        (FOL.Rel "eq" [FOL.Var "x", mkConstTerm "zero"])
    )

-- ∀x. even(x) ∧ lt(x,three) → x = zero ∨ x = two
babyFormula11 :: Formula
babyFormula11 =
    FOL.Alls "x" (FOL.Impl
        (FOL.Conj
            (FOL.Rel "even" [FOL.Var "x"])
            (FOL.Rel "lt" [FOL.Var "x", mkConstTerm "three"])
        )
        (FOL.Disj
            (FOL.Rel "eq" [FOL.Var "x", mkConstTerm "zero"])
            (FOL.Rel "eq" [FOL.Var "x", mkConstTerm "two"])
        )
    )

-- ∀x. ∃y. lt(x, y)
babyFormula12 :: Formula
babyFormula12 =
    FOL.Alls "x" (FOL.Exis "y" (FOL.Rel "lt" [FOL.Var "x", FOL.Var "y"]))

-- ∀x. even(x) → ∃y. lt(x, y)
babyFormula13 :: Formula
babyFormula13 =
    FOL.Alls "x" (FOL.Impl
        (FOL.Rel "even" [FOL.Var "x"])
        (FOL.Exis "y" (FOL.Rel "lt" [FOL.Var "x", FOL.Var "y"]))
    )

-- ∀x. ¬ even(x) → ∃y. lt(x, y)
babyFormula14 :: Formula
babyFormula14 =
    FOL.Alls "x" (FOL.Impl
        (FOL.Neg (FOL.Rel "even" [FOL.Var "x"]))
        (FOL.Exis "y" (FOL.Rel "lt" [FOL.Var "x", FOL.Var "y"]))
    )

trivAssigment :: Assigment Int
trivAssigment = Map.fromList []

-- x->5
babyAssigment1 :: Assigment Int
babyAssigment1 = Map.fromList [ ("x", 5) ]

-- x->6
babyAssigment2 :: Assigment Int
babyAssigment2 = Map.fromList [ ("x", 6) ]

-- f(x, g(y))
t1 :: Term
t1 = FOL.Fun "f" [FOL.Var "x", FOL.Fun "g" [FOL.Var "y"]]

-- f(f(z), w)
t2 :: Term
t2 = FOL.Fun "f" [FOL.Fun "f" [FOL.Var "z"], FOL.Var "w"]

-- f(f(z), g(y))
t3 :: Term
t3 = FOL.Fun "f" [FOL.Fun "f" [FOL.Var "z"], FOL.Fun "g" [FOL.Var "y"]]

-- f(x, y)
t4 :: Term
t4 = FOL.Fun "f" [FOL.Var "x", FOL.Var "y"]

-- f(y, x)
t5 :: Term
t5 = FOL.Fun "f" [FOL.Var "y", FOL.Var "x"]

-- x0, x1, x2, x3, x4
x0 = FOL.Var "x0"
x1 = FOL.Var "x1"
x2 = FOL.Var "x2"
x3 = FOL.Var "x3"
x4 = FOL.Var "x4"

-- f11, f22, f33, f44
f11 = FOL.Fun "f" [x1, x1]
f22 = FOL.Fun "f" [x2, x2]
f33 = FOL.Fun "f" [x3, x3]
f44 = FOL.Fun "f" [x4, x4]

fConjCommute = FOL.Impl
        (FOL.Conj (FOL.Rel "A" []) (FOL.Rel "B" []))
        (FOL.Conj (FOL.Rel "B" []) (FOL.Rel "A" []))

fDisjCommute = FOL.Impl
        (FOL.Disj (FOL.Rel "A" []) (FOL.Rel "B" []))
        (FOL.Disj (FOL.Rel "B" []) (FOL.Rel "A" []))


tests :: TestTree
tests = testGroup "All tests"
  [ unitTests
  , propertyTests
  ]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
    [ testCase "complexity" $ 
        complexity propExample @?= 6
    , testCase "depth" $
        depth propExample @?= 4
    , testCase "vars" $
        Set.fromList (vars propExample) @?= Set.fromList ["p","q","r","s1","s2"]
    , testCase "eval" $
        eval propExample valuationExample @?= False
    , testCase "isSat" $
        isSat propExample @?= True
    , testCase "isValid" $
        isValid propExample @?= False
    , testCase "negateLit Top" $
        negateLit (NormalForm.Top) @?= NormalForm.Bot
    , testCase "negateLit Bot" $
        negateLit (NormalForm.Bot) @?= NormalForm.Top
    , testCase "negateLit Pos" $
        negateLit (negateLit p) @?= p
    , testCase "negateLit Neg" $
        negateLit (negateLit negr) @?= negr
    , testCase "bitArith" $
        evalTerm binAirthInterp bitArithAssigment bitArithTerm @?= True 
    , testCase "eval even(x); x->5" $
        evalFormula babyArithModel babyAssigment1 babyFormula1 @?= False
    , testCase "eval even(x); x->5" $
        evalFormula babyArithModel babyAssigment2 babyFormula1 @?= True
    , testCase "eval ∃y. lt(x, y); x->5" $
        evalFormula babyArithModel babyAssigment1 babyFormula2 @?= True
    , testCase "eval ∃y. lt(x, y); x->5" $
        evalFormula babyArithModel babyAssigment2 babyFormula2 @?= True
    , testCase ("eval " ++ show babyFormula3 ++ " = True") $
        evalFormula babyArithModel trivAssigment babyFormula3 @?= True
    , testCase ("eval " ++ show babyFormula4 ++ " = False") $
        evalFormula babyArithModel trivAssigment babyFormula4 @?= False
    , testCase ("eval " ++ show babyFormula5 ++ " = True") $
        evalFormula babyArithModel trivAssigment babyFormula5 @?= True
    , testCase ("eval " ++ show babyFormula6 ++ " = False") $
        evalFormula babyArithModel trivAssigment babyFormula6 @?= False
    , testCase ("eval " ++ show babyFormula7 ++ " = True") $
        evalFormula babyArithModel trivAssigment babyFormula7 @?= True
    , testCase ("eval " ++ show babyFormula8 ++ " = False") $
        evalFormula babyArithModel trivAssigment babyFormula8 @?= False
    , testCase ("eval " ++ show babyFormula9 ++ " = True") $
        evalFormula babyArithModel trivAssigment babyFormula9 @?= True
    , testCase ("eval " ++ show babyFormula10 ++ " = False") $
        evalFormula babyArithModel trivAssigment babyFormula10 @?= False
    , testCase ("eval " ++ show babyFormula11 ++ " = True") $
        evalFormula babyArithModel trivAssigment babyFormula11 @?= True
    , testCase ("eval " ++ show babyFormula12 ++ " = False") $
        evalFormula babyArithModel trivAssigment babyFormula12 @?= False
    , testCase ("eval " ++ show babyFormula13 ++ " = True") $
        evalFormula babyArithModel trivAssigment babyFormula13 @?= True
    , testCase ("eval " ++ show babyFormula14 ++ " = False") $
        evalFormula babyArithModel trivAssigment babyFormula14 @?= False
    , testCase ("unify [(" ++ show t1 ++ ", " ++ show t2 ++")] = [(\"w\",g(y)),(\"x\",f(z))]") $
        unify [(t1, t2)] @?= Just [("w", FOL.Fun "g" [FOL.Var "y"]), ("x", FOL.Fun "f" [FOL.Var "z"])]
    , testCase ("unifyAndApply " ++ show [(t1, t2)] ++ " = " ++ show [(t3, t3)]) $
        unifyAndApply [(t1, t2)] @?= Just [(t3, t3)]
    , testCase ("unify " ++ show [(t4, t5)] ++ " = Nothing") $
        unify [(t4, t5)] @?= Nothing
    , testCase ("unifyAndApply " ++ show [(t4, t5)] ++ " = Nothing") $
        unify [(t4, t5)] @?= Nothing
    , testCase ("unify " ++ show [(t1, t5)] ++ " = Nothing") $
        unify [(t1, t5)] @?= Nothing
    , testCase ("unifyAndApply " ++ show [(t1, t5)] ++ " = Nothing") $
        unifyAndApply [(t1, t5)] @?= Nothing
    , testCase ("unifyAndApply " ++ show [(x0, f11), (x1, f22), (x2, f33), (x3, f44)] ++ " /= Nothing") $
        unifyAndApply [(x0, f11), (x1, f22), (x2, f33), (x3, f44)] /= Nothing @?= True
    ]

propertyTests :: TestTree
propertyTests = testGroup "Property tests"
    [ testProperty "Depth is always less then or equal to complexity" propertyComplexityLEQDepth
    , testProperty "Double negation of literal is id" propertyDoubleNegationLiteral
    , testProperty "Double negation of Nnf is id" propertyDoubleNegationNnf
    , testProperty "evalNnf f = evalCnf (toCnf f)" propertyEvalNnfCnf
    , testProperty "eval f = evalNnf (toNnfForm f)" propertyEvalPropNnf
    , testProperty "unifyAndApply [(t1, t2)] = [(t1', t2')] -> t1' == t2'" propertyUnifyAndApplyEq
    ]

instance {-# OVERLAPS #-} Arbitrary PartialValuation where
    arbitrary = do
        m <- chooseInt(1, 10)
        return (mkPartialValuation (randomVars m))

instance Arbitrary Literal where
    arbitrary = do
        m <- chooseInt(1, 10)
        randomLiteral (randomVars m)

instance Arbitrary NnfForm where
    arbitrary = do
        n <- chooseInt(1, 5)
        m <- chooseInt(1, 10)
        randomNnf n (randomVars m)

instance Arbitrary PropFormula where
    arbitrary = do
        n <- chooseInt(1, 5)
        m <- chooseInt(1, 10)
        randomFormula n (randomVars m)

instance Arbitrary Term where
    arbitrary = do
        n <- chooseInt(1, 5)
        m <- chooseInt(1, 10)
        arity <- sequence [chooseInt(0, 3) | _ <- [1..n]]
        randomTerm n (randomFuns n arity) (randomVars m)
    
randomItem :: [a] -> Gen a
randomItem = elements

randomVars :: Int -> Vars
randomVars n = map (\x -> 'p' : show x) [1..n]

randomFuns :: Int -> [Int] -> Funs
randomFuns n arity = zip (map (\x -> 'f' : show x) [1..n]) arity

randomLiteral :: Vars -> Gen Literal
randomLiteral varSet = do
    var <- randomItem varSet
    j <- chooseInt (1, 4)
    case j of
        1 -> return NormalForm.Top
        2 -> return NormalForm.Bot
        3 -> return (NormalForm.Pos var)
        4 -> return (NormalForm.Neg var)
        _ -> error "Invalid state"

randomNnf :: Int -> Vars -> Gen NnfForm
randomNnf 0 varSet = do
    l <- randomLiteral varSet
    return (NormalForm.Lit l)
randomNnf n varSet = do
    connective <- randomItem [NormalForm.Disj, NormalForm.Conj]
    f1 <- randomNnf (n - 1) varSet
    f2 <- randomNnf (n - 1) varSet
    return (connective f1 f2)

randomAtom :: Vars -> Gen PropFormula
randomAtom varSet = do
    var <- randomItem varSet
    j <- chooseInt(1, 4)
    case j of
        1 -> return Prop.Top
        2 -> return Prop.Bot
        3 -> return (Prop.Var var)
        4 -> return (Prop.Neg (Prop.Var var))
        _ -> error "Invalid state"

randomFormula :: Int -> Vars -> Gen PropFormula
randomFormula 0 varSet = randomAtom varSet
randomFormula n varSet = do
    connective <- randomItem [Prop.Conj, Prop.Disj, Prop.Impl, Prop.Eqiv]
    f1 <- randomFormula (n - 1) varSet
    f2 <- randomFormula (n - 1) varSet
    return (connective f1 f2)

randomConstTerm :: Vars -> Gen Term
randomConstTerm varSet = do
    var <- randomItem varSet
    return (mkConstTerm var)

randomTerm :: Int -> Funs -> Vars -> Gen Term
randomTerm 0 _ varSet = randomConstTerm varSet
randomTerm n funSet varSet = do
    f <- randomItem funSet
    args <- sequence [randomTerm (n - 1) funSet varSet | _ <- [1..snd f]]
    return (FOL.Fun (fst f) args)

propertyComplexityLEQDepth :: PropFormula -> Bool
propertyComplexityLEQDepth f = depth f <= complexity f

propertyDoubleNegationLiteral :: Literal -> Bool
propertyDoubleNegationLiteral l = negateLit (negateLit l) == l

propertyDoubleNegationNnf :: NnfForm -> Bool
propertyDoubleNegationNnf f = negateNnf (negateNnf f) == f

propertyEvalNnfCnf :: NnfForm -> PartialValuation -> Bool
propertyEvalNnfCnf f v = evalNnf f v == evalCnf (fromNnfToCnf f) v

propertyEvalPropNnf :: PropFormula -> PartialValuation -> Bool
propertyEvalPropNnf f v = eval f v == evalNnf (toNnfForm f) v

propertyUnifyAndApplyEq :: Term -> Term -> Bool
propertyUnifyAndApplyEq t1 t2 =
    case unifyAndApply [(t1, t2)] of
        Just [(t1', t2')]   -> t1' == t2'
        Just _              -> error "Invalid state!"
        Nothing             -> True
