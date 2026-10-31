module FOLTableauxDisplayTests exposing (suite)

{-| The three semantic tableaux show their trees in the same way: each formula numbered by its depth in the
branch, the rule and the premises on the edge, and the same marks for the leaves.
-}

import Expect
import LogicUS.FOL.SemanticTableaux as ST
import LogicUS.FOL.SemanticTableauxEQ as STEQ
import LogicUS.FOL.SemanticTableauxFV as FV
import LogicUS.FOL.SyntaxSemantics as SS
import Test exposing (Test, describe, test)


read : List String -> List SS.FormulaFOL
read =
    List.map SS.ffolRead


suite : Test
suite =
    describe "tableaux display"
        [ test "the three tableaux show {P(a) ∨ Q(a), ¬P(a)} in the same way" <|
            \_ ->
                let
                    fs =
                        read [ "P(a) | Q(a)", "¬P(a)" ]

                    fv =
                        FV.semanticTableauFVToString (FV.semanticTableauFV fs 3 40)
                in
                [ ST.semanticTableauToString (ST.semanticTableau fs 3 25)
                , STEQ.semanticTableauToString (STEQ.semanticTableauEq fs 3 3)
                , String.join "\n" (List.take 6 (String.lines fv))
                ]
                    |> Expect.equal
                        (List.repeat 3
                            (String.join "\n"
                                [ "1. (P(a) ∨ Q(a))"
                                , "2. ¬P(a)"
                                , "    3. P(a)         % β(1)"
                                , "    ✕               % ⊥(2,3)"
                                , "    3. Q(a)         % β(1)"
                                , "    ◯"
                                ]
                            )
                        )
        , test "ground tableau: double negation, α and closure" <|
            \_ ->
                ST.semanticTableauToString (ST.semanticTableau (read [ "¬¬(P(a) & ¬P(a))" ]) 2 20)
                    |> String.lines
                    |> Expect.equal
                        [ "1. ¬¬(P(a) ∧ ¬P(a))"
                        , "2. (P(a) ∧ ¬P(a))      % ¬¬(1)"
                        , "3. P(a)                % α(2)"
                        , "4. ¬P(a)               % α(2)"
                        , "✕                      % ⊥(3,4)"
                        ]
        , test "ground tableau: δ names the number of its formula (it named an internal key)" <|
            \_ ->
                ST.semanticTableauToString (ST.semanticTableau (read [ "¬(!E[X]!A[Y]Q(X,Y) -> !A[Y]!E[X]Q(X,Y))" ]) 3 25)
                    |> String.lines
                    |> List.map (String.join " " << String.words)
                    |> Expect.equal
                        [ "1. ¬(∃x∀yQ(x,y) → ∀y∃xQ(x,y))"
                        , "2. ∃x∀yQ(x,y) % α(1)"
                        , "3. ¬∀y∃xQ(x,y) % α(1)"
                        , "4. ∀yQ(c₁,y) % δ(2){x/c₁}"
                        , "5. ¬∃xQ(x,c₂) % δ(3){y/c₂}"
                        , "6. Q(c₁,c₁) % γ(4){y/c₁}"
                        , "7. ¬Q(c₁,c₂) % γ(5){x/c₁}"
                        , "8. Q(c₁,c₂) % γ(4){y/c₂}"
                        , "✕ % ⊥(7,8)"
                        ]
        , test "equality tableau: the new constants are c₁, c₂, ... without the ones of the input" <|
            \_ ->
                STEQ.semanticTableauToString (STEQ.semanticTableauEq (read [ "P(c_{1})", "!E[X] ¬P(X)", "!A[X] P(X)" ]) 3 3)
                    |> String.lines
                    |> List.map (String.join " " << String.words)
                    |> Expect.equal
                        [ "1. P(c₁)"
                        , "2. ∃x¬P(x)"
                        , "3. ∀xP(x)"
                        , "4. ¬P(c₂) % δ(2){x/c₂}"
                        , "5. P(c₂) % γ(3){x/c₂}"
                        , "✕ % ⊥(4,5)"
                        ]
        , test "equality tableau: Leibniz law in the rules" <|
            \_ ->
                STEQ.semanticTableauToString
                    (STEQ.semanticTableauEq
                        (read [ "!A[X] !A[Y] !A[Z] (s(s(X,Y), Z)=s(X,s(Y, Z)))", "!A[X] !E[Y] (s(X, Y)=e)", "!A[X] (s(X,e)=X & s(e,X)=X)", "¬!A[X]( (!A[Y] s(X,Y)=Y) -> X=e)" ])
                        5
                        5
                    )
                    |> String.lines
                    |> List.drop 9
                    |> List.map (String.join " " << String.words)
                    |> Expect.equal [ "10. (c₁ = e) % α(9).𝓛𝓛8", "✕ % ⊥(𝓛𝓛10(6))" ]
        , test "inequalities are written with ≠" <|
            \_ ->
                ( SS.ffolToString (SS.ffolRead "¬(f(a) = b)"), SS.ffolToMathString (SS.ffolRead "¬(f(a) = b)") )
                    |> Tuple.mapSecond (String.contains "\\neq")
                    |> Expect.equal ( "(f(a) ≠ b)", True )
        , test "DOT: numbered formulas, rules on the edges and the same leaf marks" <|
            \_ ->
                ST.semanticTableauToDOT (ST.semanticTableau (read [ "P(a) | Q(a)", "¬P(a)" ]) 3 25)
                    |> Expect.equal
                        (String.join "\n"
                            [ "digraph G {"
                            , "  0 [label=\"1. (P(a) ∨ Q(a))\"];"
                            , "  1 [label=\"2. ¬P(a)\"];"
                            , "  0 -> 1;"
                            , "  2 [label=\"3. P(a)\"];"
                            , "  1 -> 2 [label=\"β(1)\"];"
                            , "  3 [label=\"✕\"];"
                            , "  2 -> 3 [label=\"⊥(2,3)\"];"
                            , "  4 [label=\"3. Q(a)\"];"
                            , "  1 -> 4 [label=\"β(1)\"];"
                            , "  5 [label=\"◯\"];"
                            , "  4 -> 5;"
                            , "}"
                            ]
                        )
        ]
