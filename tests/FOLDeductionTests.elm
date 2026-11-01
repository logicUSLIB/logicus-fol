module FOLDeductionTests exposing (suite)

{-| Deduction systems for first-order logic: the presets are read, textbook proofs are accepted, each kind of error is
rejected, the steps that the checker accepts are valid (random instances of the rules of the connectives, checked with
truth tables), and the hints only propose correct lines. The propositional module has its own tests in logicus-pl.
-}

import Dict exposing (Dict)
import Expect
import Fuzz exposing (Fuzzer)
import List.Extra as LE
import LogicUS.FOL.Deduction as D exposing (HintKind(..), Premise(..), Schema(..))
import LogicUS.FOL.DeductionSystems as DS
import LogicUS.FOL.SyntaxSemantics exposing (FormulaFOL(..), Term(..))
import Set
import Test exposing (Test, describe, fuzz, test)


system : String -> D.System
system txt =
    case D.readSystem txt of
        Ok s ->
            s

        Err _ ->
            []


classical : D.System
classical =
    system DS.naturalDeduction


withDerived : D.System
withDerived =
    system (DS.naturalDeduction ++ "\n" ++ DS.derivedRules)


problem : List String -> String -> D.Problem
problem ps g =
    { premises = List.filterMap (Result.toMaybe << D.readFormula) ps
    , goal = Result.toMaybe (D.readFormula g)
    }


check : D.System -> List String -> String -> String -> D.ProofReport
check sys ps g proof =
    D.checkProof sys (problem ps g) (D.readProof proof)


errorAt : Int -> D.ProofReport -> String
errorAt n rep =
    rep.lines |> LE.find (\l -> l.number == n) |> Maybe.map .message |> Maybe.withDefault "no such line"


type alias Exercise =
    { name : String, sys : D.System, premises : List String, goal : String, proof : String }


exercises : List Exercise
exercises =
    [ { name = "hypothetical syllogism"
      , sys = classical
      , premises = [ "P(a) -> Q(a)", "Q(a) -> R(a)" ]
      , goal = "P(a) -> R(a)"
      , proof = """
        1 P(a) -> Q(a)      premise
        2 Q(a) -> R(a)      premise
        3 | P(a)            assumption
        4 | Q(a)            ->E 1, 3
        5 | R(a)            ->E 2, 4
        6 P(a) -> R(a)      ->I 3-5"""
      }
    , { name = "commutativity of ∨"
      , sys = classical
      , premises = [ "P(a) | Q(b)" ]
      , goal = "Q(b) | P(a)"
      , proof = """
        1 P(a) | Q(b)       premise
        2 | P(a)            assumption
        3 | Q(b) | P(a)     ∨I2 2
        4 | Q(b)            assumption
        5 | Q(b) | P(a)     ∨I1 4
        6 Q(b) | P(a)       ∨E 1, 2-3, 4-5"""
      }
    , { name = "excluded middle (classical)"
      , sys = classical
      , premises = []
      , goal = "P(a) | ¬P(a)"
      , proof = """
        1 | ¬(P(a) | ¬P(a))     assumption
        2 | | P(a)              assumption
        3 | | P(a) | ¬P(a)      ∨I1 2
        4 | | !F                ¬E 3, 1
        5 | ¬P(a)               ¬I 2-4
        6 | P(a) | ¬P(a)        ∨I2 5
        7 | !F                  ¬E 6, 1
        8 P(a) | ¬P(a)          RAA 1-7"""
      }
    , { name = "derived rules"
      , sys = withDerived
      , premises = [ "¬!A[X]P(X)", "!E[X]¬P(X) -> Q(a)", "Q(a) -> R(a)" ]
      , goal = "!E[X]¬P(X) -> R(a)"
      , proof = """
        1 ¬!A[X]P(X)              premise
        2 !E[X]¬P(X) -> Q(a)      premise
        3 Q(a) -> R(a)            premise
        4 !E[X]¬P(X)              ¬∀ 1
        5 !E[X]¬P(X) -> R(a)      HS 2, 3"""
      }
    , { name = "axiomatic: ∀x P(x) → P(a)"
      , sys = system DS.axiomatic
      , premises = [ "!A[X]P(X)" ]
      , goal = "P(a)"
      , proof = """
        1 !A[X]P(X)               premise
        2 !A[X]P(X) -> P(a)       A4
        3 P(a)                    MP 1, 2"""
      }
    , { name = "∀ and →"
      , sys = classical
      , premises = [ "!A[X](P(X) -> Q(X))", "!A[X]P(X)" ]
      , goal = "!A[X]Q(X)"
      , proof = """
        1 !A[X](P(X) -> Q(X))    premise
        2 !A[X]P(X)              premise
        3 P(a) -> Q(a)           ∀E 1
        4 P(a)                   ∀E 2
        5 Q(a)                   ->E 3, 4
        6 !A[X]Q(X)              ∀I 5"""
      }
    , { name = "∃ and ∀"
      , sys = classical
      , premises = [ "!E[X]P(X)", "!A[X](P(X) -> Q(X))" ]
      , goal = "!E[X]Q(X)"
      , proof = """
        1 !E[X]P(X)              premise
        2 !A[X](P(X) -> Q(X))    premise
        3 | P(a)                 assumption
        4 | P(a) -> Q(a)         ∀E 2
        5 | Q(a)                 ->E 4, 3
        6 | !E[X]Q(X)            ∃I 5
        7 !E[X]Q(X)              ∃E 1, 3-6"""
      }
    , { name = "∃∀ ⊢ ∀∃"
      , sys = classical
      , premises = [ "!E[X]!A[Y]R(X,Y)" ]
      , goal = "!A[Y]!E[X]R(X,Y)"
      , proof = """
        1 !E[X]!A[Y]R(X,Y)       premise
        2 | !A[Y]R(a,Y)          assumption
        3 | R(a,b)               ∀E 2
        4 | !E[X]R(X,b)          ∃I 3
        5 | !A[Y]!E[X]R(X,Y)     ∀I 4
        6 !A[Y]!E[X]R(X,Y)       ∃E 1, 2-5"""
      }
    , { name = "symmetry of equality"
      , sys = classical
      , premises = [ "a = b" ]
      , goal = "b = a"
      , proof = """
        1 a = b      premise
        2 a = a      =I
        3 b = a      =E 1, 2"""
      }
    ]


suite : Test
suite =
    describe "deduction"
        [ describe "presets"
            [ test "every preset is read" <|
                \_ ->
                    DS.presets
                        |> List.filterMap
                            (\p ->
                                case D.readSystem p.rules of
                                    Ok _ ->
                                        Nothing

                                    Err e ->
                                        Just (p.name ++ ": " ++ e)
                            )
                        |> Expect.equal []
            , test "a system is written as it is read" <|
                \_ ->
                    D.readSystem (D.systemToString withDerived) |> Expect.equal (Ok withDerived)
            , test "errors in the rules say the line" <|
                \_ ->
                    D.readSystem "rule ∧I : A, B ⊢ A ∧ B\nrule bad : A, ⊢"
                        |> Expect.equal (Err "line 2: bad: unexpected '⊢'")
            ]
        , describe "textbook proofs are accepted" <|
            List.map
                (\ex ->
                    test ex.name <|
                        \_ ->
                            check ex.sys ex.premises ex.goal ex.proof
                                |> (\r -> ( r.complete, List.filter (not << .ok) r.lines |> List.map (\l -> String.fromInt l.number ++ ": " ++ l.message) ))
                                |> Expect.equal ( True, [] )
                )
                exercises
        , describe "errors"
            [ test "a rule that does not give the formula" <|
                \_ ->
                    check classical [ "P(a) -> Q(a)" ] "Q(b)" "P(a) -> Q(a)  premise\n| P(b)  assumption\n| Q(b)  ->E 1, 2"
                        |> errorAt 3
                        |> Expect.equal "→E (A → B, A ⊢ B) does not give this formula from 1, 2"
            , test "a rule that is not in the system" <|
                \_ ->
                    check (system DS.axiomatic) [ "!A[X]P(X)" ] "P(a)" "!A[X]P(X)  premise\nP(a)  ∀E 1"
                        |> errorAt 2
                        |> Expect.equal "the rule ∀E is not one of the rules of this system"
            , test "a line inside a closed subproof" <|
                \_ ->
                    check classical [] "P(a) -> P(a)" "| P(a)  assumption\nP(a) -> P(a)  ->I 1-1\nP(a)  R 1"
                        |> errorAt 3
                        |> Expect.equal "line 1 is inside a closed subproof, and cannot be used here"
            , test "∀I with a term of a premise" <|
                \_ ->
                    check classical [ "P(a)" ] "!A[X]P(X)" "P(a)  premise\n!A[X]P(X)  ∀I 1"
                        |> errorAt 2
                        |> Expect.equal "a must be new: it occurs in the premise or open assumption P(a)"
            , test "∃E with the new term in the conclusion" <|
                \_ ->
                    check classical [ "!E[X]P(X)" ] "P(a)" "!E[X]P(X)  premise\n| P(a)  assumption\nP(a)  ∃E 1, 2-2"
                        |> errorAt 3
                        |> Expect.equal "a cannot occur in the conclusion of ∃E"
            , test "∀E with a term that would be captured" <|
                \_ ->
                    check classical [ "!A[X]!E[Y]R(X,Y)" ] "!E[Y]R(Y,Y)" "!A[X]!E[Y]R(X,Y)  premise\n!E[Y]R(Y,Y)  ∀E 1"
                        |> errorAt 2
                        |> Expect.equal "∀E (∀x A ⊢ A[x/t]) does not give this formula from 1"
            , test "A5 with the variable free in A" <|
                \_ ->
                    check (system DS.axiomatic) [] "!A[X](P(X) -> Q(X)) -> (P(X) -> !A[X]Q(X))" "!A[X](P(X) -> Q(X)) -> (P(X) -> !A[X]Q(X))  A5"
                        |> errorAt 1
                        |> Expect.equal "x cannot occur free in P(x)"
            , test "a premise that is not one of the exercise" <|
                \_ ->
                    check classical [ "P(a)" ] "P(a)" "Q(a)  premise"
                        |> errorAt 1
                        |> Expect.equal "this formula is not a premise of the exercise"
            , test "a proof that does not end with the goal" <|
                \_ ->
                    check classical [ "P(a)" ] "Q(a)" "P(a)  premise"
                        |> .message
                        |> Expect.equal "Every line is correct, but the proof does not end with the goal Q(a)."
            , test "a propositional formula is not first order" <|
                \_ ->
                    check classical [] "p" "p  premise"
                        |> errorAt 1
                        |> String.startsWith "the formula cannot be read"
                        |> Expect.equal True
            ]
        , describe "rules given by the exercise"
            [ test "rules can be added: ∀ distributes over ∧" <|
                \_ ->
                    check (system "rule ∀∧ : ∀x A, ∀x B ⊢ ∀x (A ∧ B)") [ "!A[X]P(X)", "!A[X]Q(X)" ] "!A[X](P(X) & Q(X))" "!A[X]P(X)  premise\n!A[X]Q(X)  premise\n!A[X](P(X) & Q(X))  ∀∧ 1, 2"
                        |> .complete
                        |> Expect.equal True
            , test "rule names can be written in ASCII" <|
                \_ ->
                    check classical [ "P(a)", "Q(a)" ] "P(a) & Q(a)" "P(a)  premise\nQ(a)  premise\nP(a) & Q(a)  &I 1, 2"
                        |> .complete
                        |> Expect.equal True
            ]
        , fuzz oneStep "an accepted step is valid (random instances of the propositional rules)" <|
            \( rule, premiseForms, concl ) ->
                let
                    lines =
                        List.map (\f -> { depth = 0, formula = D.formulaToInputString f, rule = "premise", refs = "" }) premiseForms
                            ++ [ { depth = 0, formula = D.formulaToInputString concl, rule = rule.name, refs = String.join ", " (List.indexedMap (\i _ -> String.fromInt (i + 1)) premiseForms) } ]

                    rep =
                        D.checkProof withDerived { premises = [], goal = Nothing } lines

                    accepted =
                        List.all .ok rep.lines
                in
                if accepted then
                    entails premiseForms concl |> Expect.equal True

                else
                    Expect.pass
        , fuzz correctStep "a correct instance of a rule is accepted" <|
            \( rule, premiseForms, concl ) ->
                let
                    lines =
                        List.map (\f -> { depth = 0, formula = D.formulaToInputString f, rule = "premise", refs = "" }) premiseForms
                            ++ [ { depth = 0, formula = D.formulaToInputString concl, rule = rule.name, refs = String.join ", " (List.indexedMap (\i _ -> String.fromInt (i + 1)) premiseForms) } ]
                in
                D.checkProof withDerived { premises = [], goal = Nothing } lines
                    |> .lines
                    |> List.filter (not << .ok)
                    |> List.map .message
                    |> Expect.equal []
        , describe "hints only propose correct lines" <|
            List.map
                (\ex ->
                    test ex.name <|
                        \_ ->
                            let
                                ls =
                                    D.readProof ex.proof

                                prob =
                                    problem ex.premises ex.goal

                                bad =
                                    List.range 0 (List.length ls)
                                        |> List.concatMap
                                            (\k ->
                                                let
                                                    prefix =
                                                        List.take k ls

                                                    depth =
                                                        Maybe.withDefault 0 (Maybe.map .depth (LE.last prefix))

                                                    openDepth =
                                                        if List.isEmpty prefix then
                                                            0

                                                        else
                                                            depth
                                                in
                                                D.hints ex.sys prob prefix Nothing 30
                                                    |> List.filter (\h -> h.kind /= Backward && h.input /= "")
                                                    |> List.filterMap
                                                        (\h ->
                                                            let
                                                                d =
                                                                    if h.kind == CloseSubproof then
                                                                        openDepth - 1

                                                                    else
                                                                        openDepth

                                                                line =
                                                                    { depth = d, formula = h.input, rule = h.rule, refs = h.refs }

                                                                rep =
                                                                    D.checkProof ex.sys prob (prefix ++ [ line ])
                                                            in
                                                            case LE.last rep.lines of
                                                                Just l ->
                                                                    if l.ok then
                                                                        Nothing

                                                                    else
                                                                        Just (String.fromInt k ++ ": " ++ h.text ++ " → " ++ l.message)

                                                                Nothing ->
                                                                    Nothing
                                                        )
                                            )
                            in
                            bad |> Expect.equal []
                )
                exercises
        , test "backward hints for the goal" <|
            \_ ->
                D.hints classical (problem [ "!A[X](P(X) -> Q(X))" ] "!A[X]P(X) -> !A[X]Q(X)") (D.readProof "!A[X](P(X) -> Q(X))  premise") Nothing 10
                    |> List.filter (\h -> h.kind == Backward)
                    |> List.map .text
                    |> Expect.equal
                        [ "→I gives (∀xP(x) → ∀xQ(x)) from a subproof from the assumption ∀xP(x) to ∀xQ(x)"
                        , "RAA gives (∀xP(x) → ∀xQ(x)) from a subproof from the assumption ¬(∀xP(x) → ∀xQ(x)) to ⊥"
                        ]
        , test "hints when a subproof can be closed" <|
            \_ ->
                D.hints classical (problem [ "P(a) -> Q(a)", "Q(a) -> R(a)" ] "P(a) -> R(a)") (D.readProof "P(a) -> Q(a)  premise\nQ(a) -> R(a)  premise\n| P(a)  assumption\n| Q(a)  ->E 1, 3\n| R(a)  ->E 2, 4") Nothing 10
                    |> List.filter (\h -> h.kind == CloseSubproof)
                    |> List.map .text
                    |> Expect.equal [ "close the subproof 3-5 and apply →I 3-5: (P(a) → R(a))" ]
        , test "∀E is proposed with any term" <|
            \_ ->
                D.hints classical (problem [ "!A[X]P(X)" ] "P(a)") (D.readProof "!A[X]P(X)  premise") Nothing 10
                    |> List.map .text
                    |> Expect.equal [ "∀E gives P(a) from ∀xP(x) (line 1)", "RAA gives P(a) from a subproof from the assumption ¬P(a) to ⊥" ]
        ]



-- RANDOM STEPS


atoms : List FormulaFOL
atoms =
    List.map (\a -> Pred ( a, [] ) [ Func ( "a", [] ) [] ]) [ "P", "Q", "R" ]


formula : Int -> Fuzzer FormulaFOL
formula depth =
    if depth <= 0 then
        Fuzz.oneOfValues (atoms ++ [ Insat ])

    else
        let
            sub =
                Fuzz.lazy (\_ -> formula (depth - 1))
        in
        Fuzz.frequency
            [ ( 3, formula 0 )
            , ( 1, Fuzz.map Neg sub )
            , ( 1, Fuzz.map2 Conj sub sub )
            , ( 1, Fuzz.map2 Disj sub sub )
            , ( 1, Fuzz.map2 Impl sub sub )
            , ( 1, Fuzz.map2 Equi sub sub )
            ]


-- the propositional rules without subproofs (with derived rules), instantiated with random formulas


plainRules : List D.Rule
plainRules =
    List.filter
        (\r ->
            List.all
                (\p ->
                    case p of
                        PFormula s ->
                            propositional s

                        _ ->
                            False
                )
                r.premises
                && propositional r.conclusion
                && not (List.isEmpty r.premises)
        )
        withDerived


propositional : Schema -> Bool
propositional s =
    case s of
        SMeta _ ->
            True

        SBot ->
            True

        STop ->
            True

        SNot a ->
            propositional a

        SAnd a b ->
            propositional a && propositional b

        SOr a b ->
            propositional a && propositional b

        SImp a b ->
            propositional a && propositional b

        SIff a b ->
            propositional a && propositional b

        _ ->
            False


inst : Dict String FormulaFOL -> Schema -> FormulaFOL
inst env s =
    case s of
        SMeta a ->
            Maybe.withDefault Taut (Dict.get a env)

        SBot ->
            Insat

        STop ->
            Taut

        SNot a ->
            Neg (inst env a)

        SAnd a b ->
            Conj (inst env a) (inst env b)

        SOr a b ->
            Disj (inst env a) (inst env b)

        SImp a b ->
            Impl (inst env a) (inst env b)

        SIff a b ->
            Equi (inst env a) (inst env b)

        _ ->
            Taut


ruleInstance : Fuzzer ( D.Rule, Dict String FormulaFOL )
ruleInstance =
    Fuzz.map4
        (\r a b c -> ( r, Dict.fromList [ ( "A", a ), ( "B", b ), ( "C", c ) ] ))
        (Fuzz.oneOfValues plainRules)
        (formula 2)
        (formula 2)
        (formula 2)


correctStep : Fuzzer ( D.Rule, List FormulaFOL, FormulaFOL )
correctStep =
    Fuzz.map
        (\( r, env ) ->
            ( r
            , List.map
                (\p ->
                    case p of
                        PFormula s ->
                            inst env s

                        _ ->
                            Taut
                )
                r.premises
            , inst env r.conclusion
            )
        )
        ruleInstance



-- a correct instance, or one whose conclusion or premises have been changed


oneStep : Fuzzer ( D.Rule, List FormulaFOL, FormulaFOL )
oneStep =
    Fuzz.map3
        (\( r, ps, c ) other k ->
            case k of
                0 ->
                    ( r, ps, c )

                1 ->
                    ( r, ps, other )

                2 ->
                    ( r, List.reverse ps, c )

                3 ->
                    ( r, List.map (\p -> if p == c then other else p) ps, Neg c )

                _ ->
                    ( r, other :: List.drop 1 ps, c )
        )
        correctStep
        (formula 2)
        (Fuzz.intRange 0 4)


eval : Set.Set String -> FormulaFOL -> Bool
eval trueAtoms f =
    case f of
        Pred ( a, _ ) _ ->
            Set.member a trueAtoms

        Neg a ->
            not (eval trueAtoms a)

        Conj a b ->
            eval trueAtoms a && eval trueAtoms b

        Disj a b ->
            eval trueAtoms a || eval trueAtoms b

        Impl a b ->
            not (eval trueAtoms a) || eval trueAtoms b

        Equi a b ->
            eval trueAtoms a == eval trueAtoms b

        Taut ->
            True

        _ ->
            False


entails : List FormulaFOL -> FormulaFOL -> Bool
entails ps c =
    LE.subsequences [ "P", "Q", "R" ]
        |> List.map Set.fromList
        |> List.all (\v -> not (List.all (eval v) ps) || eval v c)
