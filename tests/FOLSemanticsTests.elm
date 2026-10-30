module FOLSemanticsTests exposing (suite)

import Dict
import Expect
import FOLOracle as O
import Fuzz
import LogicUS.FOL.Clauses as CL
import LogicUS.FOL.NormalForms as NF
import LogicUS.FOL.SyntaxSemantics as SS exposing (FormulaFOL(..), Term(..))
import Set
import Test exposing (Test, describe, fuzz, fuzz2, fuzz3, test)


suite : Test
suite =
    describe "FOL syntax, semantics and normal forms"
        [ describe "parser"
            [ fuzz (O.formula 3) "ffolRead (ffolToInputString f) == f" <|
                \f -> SS.ffolRead (SS.ffolToInputString f) |> Expect.equal f |> Expect.onFail (SS.ffolToInputString f)
            , fuzz (O.closedFormulaEq 3) "with equality: ffolRead (ffolToInputString f) == f" <|
                \f -> SS.ffolRead (SS.ffolToInputString f) |> Expect.equal f |> Expect.onFail (SS.ffolToInputString f)
            , test "error messages do not expose internal Elm values" <|
                \_ ->
                    let
                        ( _, _, msg ) =
                            SS.ffolReadFromString "!A[X] (P(X) & "
                    in
                    String.contains "ExpectingSymbol" msg |> Expect.equal False |> Expect.onFail msg
            ]
        , describe "semantics"
            [ fuzz2 (O.closedFormulaEq 3) O.structure "ffolValuation agrees with the reference" <|
                \f s -> SS.ffolValuation f (O.toLStructure s) |> Expect.equal (Just (O.evalClosed s f))
            , fuzz (O.formula 3) "ffolFreeVars" <|
                \f -> Set.fromList (SS.ffolFreeVars f) |> Expect.equal (O.freeVars f)
            , fuzz2 (O.formula 3) O.structure "ffolUniversalClosure is closed and equivalent to the closure" <|
                \f s ->
                    let
                        g =
                            SS.ffolUniversalClosure f
                    in
                    ( SS.ffolIsClosed g, O.evalClosed s g ) |> Expect.equal ( True, O.evalClosed s f )
            , fuzz2 (O.formula 3) O.structure "ffolExistentialClosure is closed and is the existential closure" <|
                \f s ->
                    let
                        g =
                            SS.ffolExistentialClosure f

                        ref =
                            Set.foldr Exists f (O.freeVars f)
                    in
                    ( SS.ffolIsClosed g, O.evalClosed s g ) |> Expect.equal ( True, O.evalClosed s ref )
            , fuzz3 (O.formula 3) (O.groundTerm 1) O.structure "ffolApplySubstitution of a ground term for X" <|
                \f t s ->
                    let
                        g =
                            SS.ffolApplySubstitution (Dict.singleton O.varX t) f

                        envVal =
                            O.evalTerm s Dict.empty t

                        others =
                            Set.remove O.varX (O.freeVars f) |> Set.toList
                    in
                    -- for every value of the other free variables
                    allEnvs s others
                        |> List.all (\env -> O.eval s env g == O.eval s (Dict.insert O.varX envVal env) f)
                        |> Expect.equal True
                        |> Expect.onFail (SS.ffolToString g)
            , fuzz2 (O.closedFormula 3) O.structure "ffolNegation is the negation" <|
                \f s -> O.evalClosed s (SS.ffolNegation f) |> Expect.equal (not (O.evalClosed s f))
            , fuzz2 (O.closedFormula 3) O.structure "ffolRenameVars keeps the meaning" <|
                \f s -> O.evalClosed s (SS.ffolRenameVars f) |> Expect.equal (O.evalClosed s f)
            ]
        , describe "normal forms (equivalences)"
            [ fuzz2 (O.closedFormula 3) O.structure "ffolRemoveAllEquiv" <|
                \f s -> O.evalClosed s (NF.ffolRemoveAllEquiv f) |> Expect.equal (O.evalClosed s f)
            , fuzz2 (O.closedFormula 3) O.structure "ffolRemoveAllImpl" <|
                \f s -> O.evalClosed s (NF.ffolRemoveAllImpl (NF.ffolRemoveAllEquiv f)) |> Expect.equal (O.evalClosed s f)
            , fuzz2 (O.closedFormula 3) O.structure "ffolInteriorizeNeg" <|
                \f s -> O.evalClosed s (NF.ffolInteriorizeNeg (NF.ffolRemoveAllImpl (NF.ffolRemoveAllEquiv f))) |> Expect.equal (O.evalClosed s f)
            , fuzz2 (O.closedFormula 3) O.structure "ffolToPrenex is equivalent" <|
                \f s -> O.evalClosed s (NF.ffolToPrenex f) |> Expect.equal (O.evalClosed s f) |> Expect.onFail (SS.ffolToString (NF.ffolToPrenex f))
            , fuzz (O.closedFormula 3) "ffolToPrenex is in prenex form" <|
                \f -> O.isPrenex (NF.ffolToPrenex f) |> Expect.equal True |> Expect.onFail (SS.ffolToString (NF.ffolToPrenex f))
            , fuzz (O.closedFormula 3) "ffolIsPrenex agrees with the reference" <|
                \f -> NF.ffolIsPrenex f |> Expect.equal (O.isPrenex f)
            ]
        , describe "Skolem forms and clauses (equisatisfiable)"
            [ skolemSound "ffolToSkolem" (\f -> [ NF.ffolToSkolem f ])
            , skolemComplete "ffolToSkolem" (\f -> [ NF.ffolToSkolem f ])
            , skolemSound "ffolToNNF" (\f -> [ NF.ffolToNNF f ])
            , skolemComplete "ffolToNNF" (\f -> [ NF.ffolToNNF f ])
            , skolemSound "ffolToCNF" (\f -> [ NF.ffolToCNF f ])
            , skolemComplete "ffolToCNF" (\f -> [ NF.ffolToCNF f ])
            , skolemSound "ffolToClauses" (\f -> List.map clauseFormula (CL.ffolToClauses f))
            , skolemComplete "ffolToClauses" (\f -> List.map clauseFormula (CL.ffolToClauses f))
            , setSkolemSound "sfolToSkolem" NF.sfolToSkolem
            , setSkolemComplete "sfolToSkolem" NF.sfolToSkolem
            , setSkolemSound "sfolToCNF" NF.sfolToCNF
            , setSkolemComplete "sfolToCNF" NF.sfolToCNF
            , setSkolemSound "sfolToClauses" (CL.sfolToClauses >> List.map clauseFormula)
            , setSkolemComplete "sfolToClauses" (CL.sfolToClauses >> List.map clauseFormula)
            , fuzz (O.closedFormula 3) "ffolToSkolem has no existential quantifier" <|
                \f -> noExists (NF.ffolToSkolem f) |> Expect.equal True |> Expect.onFail (SS.ffolToString (NF.ffolToSkolem f))
            , fuzz (O.closedSet 3 3) "sfolToSkolem has no existential quantifier" <|
                \fs -> List.all noExists (NF.sfolToSkolem fs) |> Expect.equal True |> Expect.onFail (SS.sfolToString (NF.sfolToSkolem fs))
            ]
        ]


allEnvs : O.Struct -> List SS.Variable -> List (Dict.Dict SS.Variable Int)
allEnvs s vars =
    List.foldl
        (\v acc -> List.concatMap (\env -> List.map (\o -> Dict.insert v o env) (List.range 0 (s.n - 1))) acc)
        [ Dict.empty ]
        vars


clauseFormula : CL.ClauseFOL -> FormulaFOL
clauseFormula c =
    case c of
        [] ->
            Insat

        _ ->
            SS.sfolDisjunction (List.map CL.clauseFOLLitToLiteral c)


noExists : FormulaFOL -> Bool
noExists f =
    case f of
        Exists _ _ ->
            False

        Forall _ g ->
            noExists g

        Neg g ->
            O.quantifierFree g || noExists g

        Conj g h ->
            noExists g && noExists h

        Disj g h ->
            noExists g && noExists h

        Impl g h ->
            noExists g && noExists h

        Equi g h ->
            O.quantifierFree g && O.quantifierFree h

        _ ->
            True


{-| If the transformed formulas are true (with any interpretation of the new
function symbols), the original formula is true.
-}
skolemSound : String -> (FormulaFOL -> List FormulaFOL) -> Test
skolemSound name tr =
    fuzz2 (O.closedFormula 3) O.structure (name ++ ": a model of the result is a model of the formula") <|
        \f s ->
            if List.all (O.evalClosed s) (tr f) then
                O.evalClosed s f |> Expect.equal True |> Expect.onFail (SS.sfolToString (tr f))

            else
                Expect.pass


{-| If the formula is true, some interpretation of the new function symbols
makes the result true.
-}
skolemComplete : String -> (FormulaFOL -> List FormulaFOL) -> Test
skolemComplete name tr =
    fuzz2 (O.closedFormula 3) O.structure (name ++ ": a model of the formula expands to a model of the result") <|
        \f s ->
            if O.evalClosed s f then
                case O.existsExpansion s (tr f) of
                    Just b ->
                        b |> Expect.equal True |> Expect.onFail (SS.sfolToString (tr f))

                    Nothing ->
                        Expect.pass

            else
                Expect.pass


setSkolemSound : String -> (List FormulaFOL -> List FormulaFOL) -> Test
setSkolemSound name tr =
    fuzz2 (O.closedSet 3 2) O.structure (name ++ ": a model of the result is a model of the set") <|
        \fs s ->
            if List.all (O.evalClosed s) (tr fs) then
                List.all (O.evalClosed s) fs |> Expect.equal True |> Expect.onFail (SS.sfolToString (tr fs))

            else
                Expect.pass


setSkolemComplete : String -> (List FormulaFOL -> List FormulaFOL) -> Test
setSkolemComplete name tr =
    fuzz2 (O.closedSet 3 2) O.structure (name ++ ": a model of the set expands to a model of the result") <|
        \fs s ->
            if List.all (O.evalClosed s) fs then
                case O.existsExpansion s (tr fs) of
                    Just b ->
                        b |> Expect.equal True |> Expect.onFail (SS.sfolToString (tr fs))

                    Nothing ->
                        Expect.pass

            else
                Expect.pass
