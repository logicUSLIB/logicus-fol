module FOLProversTests exposing (suite)

import Dict
import Expect
import LogicUS.FOL.Prover9Mace4 as PM
import LogicUS.FOL.SyntaxSemantics as SS
import LogicUS.FOL.TPTP as T
import Set
import Test exposing (Test, describe, test)


problem : PM.P9M4Problem
problem =
    PM.p9m4Problem
        { assumptions = List.map SS.ffolRead [ "!A[X](P(X) -> Q(X))", "P(a)", "!A[X] ¬(f(X) = X)", "!A[X]!A[Y](R(X,Y) | R(Y,X))", "E" ]
        , goals = [ SS.ffolRead "Q(b)" ]
        }


{-| Output of Mace4 (LADR 2009-11A) on the problem above.
-}
mace4Output : String
mace4Output =
    """
============================== MODEL =================================

interpretation( 2, [number=1, seconds=0], [

        function(a, [ 0 ]),

        function(b, [ 1 ]),

        function(f(_), [ 1, 0 ]),

        relation(E, [ 1 ]),

        relation(P(_), [ 1, 0 ]),

        relation(Q(_), [ 1, 0 ]),

        relation(R(_,_), [
			   1, 0,
			   1, 1 ])
]).

============================== end of model ==========================
"""


suite : Test
suite =
    describe "External provers"
        [ test "p9m4Problem writes assumptions and goals" <|
            \_ ->
                (PM.p9m4Problem { assumptions = [ SS.ffolRead "!A[X](P(X) -> Q(X))", SS.ffolRead "P(a)" ], goals = [ SS.ffolRead "Q(a)" ] }).input
                    |> Expect.equal "formulas(assumptions).\n(all X (P(X) -> Q(X))).\nP(a).\nend_of_list.\n\nformulas(goals).\nQ(a).\nend_of_list.\n"
        , test "Prover9 names: a constant starting with u-z is renamed (it would be read as a variable)" <|
            \_ -> (PM.p9m4Problem { assumptions = [ SS.ffolRead "P(x)" ], goals = [] }).input |> Expect.equal "formulas(assumptions).\nP(c_x).\nend_of_list.\n"
        , test "mace4Models reads the model" <|
            \_ ->
                case PM.mace4Models problem mace4Output of
                    [ ( u, i ) ] ->
                        ( ( Set.toList u, Dict.toList i.const ), ( Dict.get ( "f", [] ) i.func, Dict.get ( "R", [] ) i.pred ) )
                            |> Expect.equal
                                ( ( [ 0, 1 ], [ ( ( "a", [] ), 0 ), ( ( "b", [] ), 1 ) ] )
                                , ( Just ( 1, Dict.fromList [ ( [ 0 ], 1 ), ( [ 1 ], 0 ) ] ), Just ( 2, Set.fromList [ [ 0, 0 ], [ 1, 0 ], [ 1, 1 ] ] ) )
                                )

                    ms ->
                        Expect.fail ("expected one model, got " ++ String.fromInt (List.length ms))
        , test "the Mace4 model is a counter-model, checked with ffolValuation" <|
            \_ ->
                case PM.mace4Models problem mace4Output of
                    [ m ] ->
                        ( List.map (\f -> SS.ffolValuation (SS.ffolRead f) m) [ "!A[X](P(X) -> Q(X))", "P(a)", "!A[X] ¬(f(X) = X)", "!A[X]!A[Y](R(X,Y) | R(Y,X))", "E" ]
                        , SS.ffolValuation (SS.ffolRead "Q(b)") m
                        )
                            |> Expect.equal ( List.repeat 5 (Just True), Just False )

                    _ ->
                        Expect.fail "no model"
        , test "prover9Result" <|
            \_ ->
                List.map PM.prover9Result [ "...THEOREM PROVED...", "...SEARCH FAILED...", "killed" ]
                    |> Expect.equal [ Just True, Just False, Nothing ]
        , test "tptpProblem" <|
            \_ ->
                (T.tptpProblem { axioms = [ SS.ffolRead "!A[X](P(X) -> Q(X))", SS.ffolRead "P(a)" ], conjecture = Just (SS.ffolRead "Q(a)") }).input
                    |> Expect.equal "fof(ax1, axiom, ![X]: (p(X) => q(X))).\nfof(ax2, axiom, p(a)).\nfof(goal, conjecture, q(a)).\n"
        , test "TPTP names: predicate P and constant p do not clash" <|
            \_ ->
                (T.tptpProblem { axioms = [ SS.ffolRead "P(p)" ], conjecture = Nothing })
                    |> (\pr -> ( pr.input, Dict.get "p_2" pr.symbols ))
                    |> Expect.equal ( "fof(ax1, axiom, p(p_2)).\n", Just ( "p", [] ) )
        , test "szsStatus" <|
            \_ ->
                List.map T.szsStatus [ "# SZS status Theorem for x.p", "% SZS status CounterSatisfiable for x", "nothing" ]
                    |> Expect.equal [ Just "Theorem", Just "CounterSatisfiable", Nothing ]
        ]
