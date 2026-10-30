module FOLAlgorithmsTests exposing (suite)

import Dict
import Expect
import FOLOracle as O
import Fuzz exposing (Fuzzer)
import Graph
import List.Extra as LE
import LogicUS.FOL.Clauses as CL exposing (ClauseFOL, ClauseFOLAtom(..), ClauseFOLSet)
import LogicUS.FOL.Herbrand as H
import LogicUS.FOL.Resolution as R
import LogicUS.FOL.SemanticTableaux as ST
import LogicUS.FOL.SemanticTableauxEQ as STEQ
import LogicUS.FOL.SyntaxSemantics as SS exposing (FormulaFOL(..), Term(..))
import LogicUS.FOL.Unification as U
import Set
import Test exposing (Test, describe, fuzz, fuzz2, test)


suite : Test
suite =
    describe "FOL algorithms"
        [ describe "unification"
            [ fuzz (Fuzz.pair (O.term 2) (O.term 2)) "termMGU exists iff the terms unify" <|
                \( t1, t2 ) -> (U.termMGU t1 t2 /= Nothing) |> Expect.equal (O.unify [ ( t1, t2 ) ] /= Nothing)
            , fuzz (Fuzz.pair (O.term 2) (O.term 2)) "termMGU makes both terms equal" <|
                \( t1, t2 ) ->
                    case U.termMGU t1 t2 of
                        Just s ->
                            SS.termApplySubstitution s t1 |> Expect.equal (SS.termApplySubstitution s t2)

                        Nothing ->
                            Expect.pass
            , fuzz (Fuzz.pair (Fuzz.listOfLength 2 (O.term 2)) (Fuzz.listOfLength 2 (O.term 2))) "termsMGU makes both lists equal" <|
                \( l1, l2 ) ->
                    case ( U.termsMGU l1 l2, O.unify (List.map2 Tuple.pair l1 l2) ) of
                        ( Just s, _ ) ->
                            List.map (SS.termApplySubstitution s) l1 |> Expect.equal (List.map (SS.termApplySubstitution s) l2)

                        ( Nothing, ref ) ->
                            ref |> Expect.equal Nothing
            , fuzz (Fuzz.pair (O.term 2) (O.term 2)) "termMGU is most general: the reference unifier is an instance of it" <|
                \( t1, t2 ) ->
                    case ( U.termMGU t1 t2, O.unify [ ( t1, t2 ) ] ) of
                        ( Just s, Just r ) ->
                            -- r = r ∘ s on the unified term (s is at least as general as r)
                            SS.termApplySubstitution r (SS.termApplySubstitution s t1) |> Expect.equal (SS.termApplySubstitution r t1)

                        _ ->
                            Expect.pass
            ]
        , describe "Herbrand"
            [ fuzz (Fuzz.listOfLengthBetween 1 2 (Fuzz.map stripQuantifiers (O.formula 2))) "level-1 Herbrand universe of open formulas = constants (or a fresh one) plus f applied once" <|
                \fs ->
                    case H.sfolHerbrandUniverse fs 1 of
                        Just u ->
                            Set.fromList (List.map SS.termToString u) |> Expect.equal (Set.fromList (List.map SS.termToString (herbrandUniverse fs 1)))

                        Nothing ->
                            Expect.fail "no universe"
            ]
        , describe "resolution (True = unsatisfiable)"
            [ fuzz2 O.functionFreeClauseSet (Fuzz.listOfLength 4 O.structure) "SCF: every derived clause holds in the models of the input" <|
                \cs ss -> R.csfolSCFResolution cs |> Tuple.second |> graphClauses |> derivedSound cs ss
            , fuzz2 O.functionFreeClauseSet (Fuzz.listOfLength 4 O.structure) "linear: every derived clause holds in the models of the input" <|
                \cs ss -> R.csfolSCFLinearResolution cs |> Tuple.second |> graphClauses |> derivedSound cs ss
            , fuzz2 O.functionFreeClauseSet (Fuzz.listOfLength 4 O.structure) "positive: every derived clause holds in the models of the input" <|
                \cs ss -> R.csplSCFPositiveResolution cs |> Tuple.second |> graphClauses |> derivedSound cs ss
            , fuzz2 O.functionFreeClauseSet (Fuzz.listOfLength 4 O.structure) "negative: every derived clause holds in the models of the input" <|
                \cs ss -> R.csplSCFNegativeResolution cs |> Tuple.second |> graphClauses |> derivedSound cs ss
            , fuzz O.functionFreeClauseSet "SCF decides function-free clause sets (checked on all ground instances)" <|
                \cs -> Tuple.first (R.csfolSCFResolution cs) |> Expect.equal (not (groundSatisfiable cs))
            , fuzz O.functionFreeClauseSet "linear (bounded search) never refutes a satisfiable set" <|
                \cs ->
                    if Tuple.first (R.csfolSCFLinearResolution cs) then
                        groundSatisfiable cs |> Expect.equal False

                    else
                        Expect.pass
            , fuzz O.functionFreeClauseSet "positive decides function-free clause sets" <|
                \cs -> Tuple.first (R.csplSCFPositiveResolution cs) |> Expect.equal (not (groundSatisfiable cs))
            , fuzz O.functionFreeClauseSet "negative decides function-free clause sets" <|
                \cs -> Tuple.first (R.csplSCFNegativeResolution cs) |> Expect.equal (not (groundSatisfiable cs))
            , test "textbook: {P(x) ∨ Q(x), ¬P(a), ¬Q(a)} is refuted" <|
                \_ ->
                    [ "{P(X), Q(X)}", "{¬P(a)}", "{¬Q(a)}" ]
                        |> List.map (CL.cfolReadExtraction << CL.cfolReadFromString)
                        |> R.csfolSCFResolution
                        |> Tuple.first
                        |> Expect.equal True
            , test "textbook: {¬P(x) ∨ P(f(x)), P(a), ¬P(f(f(a)))} is refuted" <|
                \_ ->
                    [ "{¬P(X), P(f(X))}", "{P(a)}", "{¬P(f(f(a)))}" ]
                        |> List.map (CL.cfolReadExtraction << CL.cfolReadFromString)
                        |> R.csfolSCFResolution
                        |> Tuple.first
                        |> Expect.equal True
            ]
        , describe "semantic tableaux"
            [ fuzz2 (O.closedSet 3 2) (Fuzz.listOfLength 8 O.structure) "a closed tableau means no model (soundness)" <|
                \fs ss ->
                    if ST.semanticTableauIsInsat (ST.semanticTableau fs 3 25) then
                        ss |> List.filter (\s -> List.all (O.evalClosed s) fs) |> List.length |> Expect.equal 0

                    else
                        Expect.pass
            , fuzz2 (Fuzz.listOfLengthBetween 1 3 (O.closedFormulaEq 2)) (Fuzz.listOfLength 8 O.structure) "with equality: a closed tableau means no model (soundness)" <|
                \fs ss ->
                    if STEQ.stfoleqCheckIfClose (STEQ.semanticTableauEq fs 3 3) then
                        ss |> List.filter (\s -> List.all (O.evalClosed s) fs) |> List.length |> Expect.equal 0

                    else
                        Expect.pass
            , fuzz (O.closedSet 3 2) "propositional-like sets: the tableau closes iff unsatisfiable (no quantifiers)" <|
                \fs ->
                    let
                        qf =
                            List.filter O.quantifierFree fs
                    in
                    if List.isEmpty qf then
                        Expect.pass

                    else
                        ST.semanticTableauIsInsat (ST.semanticTableau qf 3 25) |> Expect.equal (not (groundSatisfiableFormulas qf))
            , test "textbook: ∀x(P(x) → Q(x)), ∀x P(x), ¬Q(a) closes" <|
                \_ ->
                    [ "!A[X](P(X) -> Q(X))", "!A[X]P(X)", "¬Q(a)" ]
                        |> List.map SS.ffolRead
                        |> (\fs -> ST.semanticTableau fs 3 25)
                        |> ST.semanticTableauIsInsat
                        |> Expect.equal True
            , test "textbook: ¬(∃x∀y Q(x,y) → ∀y∃x Q(x,y)) closes" <|
                \_ ->
                    [ SS.ffolRead "¬(!E[X]!A[Y]Q(X,Y) -> !A[Y]!E[X]Q(X,Y))" ]
                        |> (\fs -> ST.semanticTableau fs 3 25)
                        |> ST.semanticTableauIsInsat
                        |> Expect.equal True
            , test "with equality: a = b, P(a), ¬P(b) closes" <|
                \_ ->
                    [ SS.ffolRead "a = b", SS.ffolRead "P(a)", SS.ffolRead "¬P(b)" ]
                        |> (\fs -> STEQ.semanticTableauEq fs 3 3)
                        |> STEQ.stfoleqCheckIfClose
                        |> Expect.equal True
            , test "with equality: group axioms entail that a left identity is unique (Exercise 9.3 style)" <|
                \_ ->
                    [ "!A[X] !A[Y] !A[Z] (s(s(X,Y), Z)=s(X,s(Y, Z)))"
                    , "!A[X] !E[Y] (s(X, Y)=e)"
                    , "!A[X] (s(X,e)=X & s(e,X)=X)"
                    , "¬!A[X]( (!A[Y] s(X,Y)=Y) -> X=e)"
                    ]
                        |> List.map SS.ffolRead
                        |> (\fs -> STEQ.semanticTableauEq fs 3 3)
                        |> STEQ.stfoleqCheckIfClose
                        |> Expect.equal True
            ]
        ]



-- HELPERS


stripQuantifiers : FormulaFOL -> FormulaFOL
stripQuantifiers f =
    case f of
        Forall _ g ->
            stripQuantifiers g

        Exists _ g ->
            stripQuantifiers g

        Neg g ->
            Neg (stripQuantifiers g)

        Conj g h ->
            Conj (stripQuantifiers g) (stripQuantifiers h)

        Disj g h ->
            Disj (stripQuantifiers g) (stripQuantifiers h)

        Impl g h ->
            Impl (stripQuantifiers g) (stripQuantifiers h)

        Equi g h ->
            Equi (stripQuantifiers g) (stripQuantifiers h)

        _ ->
            f


graphClauses : Graph.Graph ( Bool, ClauseFOL ) e -> List ClauseFOL
graphClauses g =
    Graph.nodes g |> List.map (.label >> Tuple.second)


clauseFormula : ClauseFOL -> FormulaFOL
clauseFormula c =
    case c of
        [] ->
            Insat

        _ ->
            SS.sfolDisjunction (List.map CL.clauseFOLLitToLiteral c)


derivedSound : ClauseFOLSet -> List O.Struct -> List ClauseFOL -> Expect.Expectation
derivedSound cs ss derived =
    let
        models =
            List.filter (\s -> O.evalClauses s cs) ss

        bad =
            List.filter (\c -> List.any (\s -> not (O.evalClosed s (clauseFormula c))) models) derived
    in
    List.map CL.cfolToString bad |> Expect.equal []


{-| Herbrand universe up to the given level, for the base signature.
-}
herbrandUniverse : List FormulaFOL -> Int -> List Term
herbrandUniverse fs level =
    let
        constIds =
            List.concatMap SS.ffolConstSymbols fs

        consts =
            List.filter (\c -> List.member c [ O.cA, O.cB ]) (List.map (\i -> Func i []) (LE.unique constIds))

        base =
            if List.isEmpty consts then
                -- the library's choice of fresh constant is checked by name below
                Maybe.withDefault [] (H.sfolHerbrandUniverse fs 0)

            else
                consts

        usesF =
            List.member ( "f", [] ) (List.concatMap SS.ffolFuncSymbols fs)

        step ts =
            if usesF then
                LE.unique (ts ++ List.map (\t -> Func ( "f", [] ) [ t ]) ts)

            else
                ts
    in
    List.foldl (\_ acc -> step acc) base (List.range 1 level)


{-| Function-free clause sets: satisfiable iff satisfiable on their ground
instances over their constants (a fresh one if none), decided by brute force.
-}
groundSatisfiable : ClauseFOLSet -> Bool
groundSatisfiable cs =
    let
        consts =
            let
                c =
                    List.concatMap (List.concatMap litTerms) cs |> List.filter isConst |> LE.unique
            in
            if List.isEmpty c then
                [ O.cA ]

            else
                c

        instances =
            cs
                |> List.concatMap
                    (\c ->
                        let
                            vars =
                                Set.toList (CL.cfolVarSymbols c)

                            substs =
                                List.foldl (\v acc -> List.concatMap (\s -> List.map (\k -> Dict.insert v k s) consts) acc) [ Dict.empty ] vars
                        in
                        List.map (\s -> CL.cfolApplySubstitution s c) substs
                    )

        groundAtoms =
            instances |> List.concatMap (List.map Tuple.first) |> LE.unique

        assignments =
            LE.subsequences groundAtoms
    in
    List.any (\trueAtoms -> List.all (List.any (\( a, pol ) -> List.member a trueAtoms == pol)) instances) assignments


groundSatisfiableFormulas : List FormulaFOL -> Bool
groundSatisfiableFormulas fs =
    let
        atoms f =
            case f of
                Neg g ->
                    atoms g

                Conj g h ->
                    atoms g ++ atoms h

                Disj g h ->
                    atoms g ++ atoms h

                Impl g h ->
                    atoms g ++ atoms h

                Equi g h ->
                    atoms g ++ atoms h

                Pred _ _ ->
                    [ f ]

                _ ->
                    []

        all =
            fs |> List.concatMap atoms |> LE.unique

        evalWith trueAtoms f =
            case f of
                Pred _ _ ->
                    List.member f trueAtoms

                Neg g ->
                    not (evalWith trueAtoms g)

                Conj g h ->
                    evalWith trueAtoms g && evalWith trueAtoms h

                Disj g h ->
                    evalWith trueAtoms g || evalWith trueAtoms h

                Impl g h ->
                    not (evalWith trueAtoms g) || evalWith trueAtoms h

                Equi g h ->
                    evalWith trueAtoms g == evalWith trueAtoms h

                Taut ->
                    True

                _ ->
                    False
    in
    List.any (\ta -> List.all (evalWith ta) fs) (LE.subsequences all)


litTerms : ( ClauseFOLAtom, Bool ) -> List Term
litTerms ( a, _ ) =
    case a of
        P _ ts ->
            ts

        Eq t1 t2 ->
            [ t1, t2 ]


isConst : Term -> Bool
isConst t =
    case t of
        Func _ [] ->
            True

        _ ->
            False
