module FOLRegressionTests exposing (suite)

{-| One test per bug found in the October 2026 review, with the concrete
counterexample that exposed it.
-}

import Expect
import FOLOracle as O
import LogicUS.FOL.Clauses as CL
import LogicUS.FOL.NormalForms as NF
import LogicUS.FOL.Resolution as R
import LogicUS.FOL.SemanticTableaux as ST
import LogicUS.FOL.SemanticTableauxEQ as STEQ
import LogicUS.FOL.SyntaxSemantics as SS exposing (FormulaFOL(..), Term(..))
import Test exposing (Test, describe, test)


cls : List String -> List CL.ClauseFOL
cls =
    List.map (CL.cfolReadExtraction << CL.cfolReadFromString)


allMethods : List ( String, List CL.ClauseFOL -> Bool )
allMethods =
    [ ( "SCF", R.csfolSCFResolution >> Tuple.first )
    , ( "linear", R.csfolSCFLinearResolution >> Tuple.first )
    , ( "positive", R.csplSCFPositiveResolution >> Tuple.first )
    , ( "negative", R.csplSCFNegativeResolution >> Tuple.first )
    ]


forAll : List CL.ClauseFOL -> Bool -> Expect.Expectation
forAll cs expected =
    allMethods
        |> List.map (\( name, m ) -> ( name, m cs ))
        |> Expect.equal (List.map (\( name, _ ) -> ( name, expected )) allMethods)


suite : Test
suite =
    describe "FOL regressions"
        [ test "tableau: ∀x P(x) is not refuted (a branch cut by the depth limit counted as closed)" <|
            \_ -> ST.semanticTableau [ SS.ffolRead "!A[X]P(X)" ] 3 25 |> ST.semanticTableauIsInsat |> Expect.equal False
        , test "equality tableau: the δ rule uses a new constant (it reused the one the γ rule had taken)" <|
            \_ ->
                STEQ.semanticTableauEq [ SS.ffolRead "!A[X] ¬P(X)", SS.ffolRead "!A[Y] !E[X] ¬(X = Y)" ] 3 3
                    |> STEQ.stfoleqCheckIfClose
                    |> Expect.equal False
        , test "tableau: {∀y∃x ¬Q(x,y), ∀x Q(x,x)} is not refuted" <|
            \_ ->
                ST.semanticTableau [ SS.ffolRead "!A[Y] !E[X] ¬Q(X,Y)", SS.ffolRead "!A[X] Q(X,X)" ] 3 25
                    |> ST.semanticTableauIsInsat
                    |> Expect.equal False
        , test "equality tableau: {∀y∃x ¬Q(x,y), ∀x Q(x,x)} is not refuted" <|
            \_ ->
                STEQ.semanticTableauEq [ SS.ffolRead "!A[Y] !E[X] ¬Q(X,Y)", SS.ffolRead "!A[X] Q(X,X)" ] 3 3
                    |> STEQ.stfoleqCheckIfClose
                    |> Expect.equal False
        , test "ffolToInputString writes variables inside function arguments in input syntax" <|
            \_ -> SS.ffolToInputString (SS.ffolRead "!A[X]P(f(X))") |> SS.ffolRead |> Expect.equal (SS.ffolRead "!A[X]P(f(X))")
        , test "ffolToClauses: ⊤ ∨ ⊤ gives no clauses (it gave the empty clause)" <|
            \_ -> CL.ffolToClauses (Disj Taut Taut) |> Expect.equal []
        , test "sfolToClauses: P(x) ∨ ⊤ is dropped, not turned into P(x)" <|
            \_ ->
                CL.sfolToClauses [ SS.ffolRead "!A[X](!T & (P(X) | !T))", SS.ffolRead "!A[X]¬P(X)" ]
                    |> List.length
                    |> Expect.equal 1
        , test "sfolToSkolem removes quantifiers under ↔ (it skipped the preprocessing)" <|
            \_ -> NF.sfolToSkolem [ SS.ffolRead "!T <-> !A[X]P(X)" ] |> List.all O.quantifierFree |> Expect.equal True
        , test "resolution needs factoring: {P(x), P(y)}, {¬P(u), ¬P(v)} is refuted" <|
            \_ -> forAll (cls [ "{P(X), P(Y)}", "{¬P(U), ¬P(V)}" ]) True
        , test "resolution terminates on a satisfiable function-free set (variants were never subsumed)" <|
            \_ -> forAll (cls [ "{¬Q(a,X), ¬P(Z)}", "{¬Q(X,Z), R}", "{P(Y), P(X), Q(a,b)}" ]) False
        , test "linear resolution tries every top clause" <|
            \_ -> forAll (cls [ "{¬Q(X,X)}", "{¬P(X)}", "{P(X)}" ]) True
        , test "an input with the empty clause is refuted" <|
            \_ -> forAll (cls [ "{}", "{P(a)}" ]) True
        , test "θ-subsumption: P(X) subsumes P(a) ∨ Q" <|
            \_ -> CL.cfolSubsumes (CL.cfolReadExtraction (CL.cfolReadFromString "{P(X)}")) (CL.cfolReadExtraction (CL.cfolReadFromString "{P(a), Q}")) |> Expect.equal True
        , test "parser errors are readable" <|
            \_ ->
                SS.ffolReadFromString "!A[X] (P(X) & "
                    |> (\( _, _, msg ) -> String.startsWith "Syntax error after" msg)
                    |> Expect.equal True
        ]
