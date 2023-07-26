{-# LANGUAGE TypeSynonymInstances #-}
 
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Data.Set as Set
import qualified Data.Map as Map

import Propositional as Prop
import NormalForm as NormalForm

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
    ]

propertyTests :: TestTree
propertyTests = testGroup "Property tests"
    [ testProperty "Depth is always less then or equal to complexity" propertyComplexityLEQDepth
    , testProperty "Double negation of literal is id" propertyDoubleNegationLiteral
    , testProperty "Double negation of Nnf is id" propertyDoubleNegationNnf
    , testProperty "evalNnf f = evalCnf (toCnf f)" propertyEvalNnfCnf
    , testProperty "eval f = evalNnf (toNnfForm f)" propertyEvalPropNnf
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
    
randomItem :: [a] -> Gen a
randomItem = elements

randomVars :: Int -> Vars
randomVars n = map (\x -> 'p' : show x) [1..n]

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

