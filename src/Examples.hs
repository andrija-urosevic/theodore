import FOL
import Theodore

lemma_disj_commut = mkGoal [] 
    (Impl 
        (Disj (Rel "A" []) (Rel "B" [])) 
        (Disj (Rel "B" []) (Rel "A" []))
    )
proof_disj_commut = 
    ImplI "h" 
        (DisjE "h" 
            (DisjrI 
                (Exact "h")
            ) 
            (DisjlI 
                (Exact "h")
            )
        )

lemma_impl_composition = mkGoal 
    [ Assumption "h1" (Impl (Rel "A" []) (Rel "B" []))
    , Assumption "h2" (Impl (Rel "B" []) (Rel "C" [])) ] 
    (Impl (Rel "A" []) (Rel "C" []))
proof_impl_composition =
    ImplI "h" 
        (ImplE "h1" 
            (Exact "h") 
            (ImplE "h2" 
                (Exact "h1") 
                (Exact "h2")
            )
        )

lemma_1 = mkGoal [] 
    (Impl 
        (Rel "A" []) 
        (Conj 
            (Disj (Rel "A" []) (Rel "B" [])) 
            (Disj (Rel "A" []) (Rel "C" []))
        )
    )
proof_1 = 
    ImplI "h" 
        (ConjI 
            (DisjlI 
                (Exact "h")
            ) 
            (DisjlI 
                (Exact "h")
            )
        )

lemma_alls_modus_pones = mkGoal
    [ Assumption "h1" (Alls "x" (Rel "A" [Var "x"]))
    , Assumption "h2" (Alls "x" (Impl (Rel "A" [Var "x"]) (Rel "B" [Var "x"])))]
    (Alls "x" (Rel "B" [Var "x"]))
proof_alls_modus_pones =
    AllsI "x" 
        (AllsE "x" "h1" 
            (AllsE "x" "h2" 
                (ImplE "h2" 
                    (Exact "h1") 
                    (Exact "h2")
                )
            )
        )

lemma_contrapositive = mkGoal [] 
    (Impl 
        (Neg (Exis "x" (Rel "p" [Var "x"]))) 
        (Alls "x" (Neg (Rel "p" [Var "x"])))
    )
proof_contrapositive = 
    ImplI "h" 
        (AllsI "x" 
            (NegI "h1" 
                (NegE "h" 
                    (ExisI "x" 
                        (Exact "h1")
                    )
                )
            )
        )

lemma_distrib_alls_conj = mkGoal []
    Impl 
        (Alls "x" 
            (Conj 
                (Rel "P" [Var "x"]) 
                (Rel "Q" [Var "x"])
            )
        ) 
        (Conj 
            (Alls "x" 
                (Rel "P" [Var "x"])
            ) 
            (Alls "x" 
                (Rel "Q" [Var "x"])
            )
        )
proof_distrib_alls_conj = 
    ImplI "h" 
        (ConjI 
            (AllsI "x" 
                (AllsE "x" "h" 
                    (ConjE "h" 
                        (Exact "h1")
                    )
                )
            ) 
            (AllsI "x" 
                (AllsE "x" "h" 
                    (ConjE "h" 
                        (Exact "h2")
                    )
                )
            )
        )

main :: IO ()
main = do
    putStrLn "\nDisjunction commutes:"
    genLatexTree proof_disj_commut lemma_disj_commut
    putStrLn "\nImplication composition:"
    genLatexTree proof_impl_composition lemma_impl_composition
    putStrLn "\nLemma 1:"
    genLatexTree proof_1 lemma_1
    putStrLn "\nUniversal modus pones:"
    genLatexTree proof_alls_modus_pones lemma_alls_modus_pones
    putStrLn "\nContrapostive:"
    genLatexTree proof_contrapositive lemma_contrapositive

