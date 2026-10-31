module FOLTableauxFVTests exposing (suite)

{-| Free-variable tableaux: soundness of the closed tableaux against random finite structures, a model built from
every open branch, propositional completeness, and textbook problems (Pelletier 1986).
-}

import Dict exposing (Dict)
import Expect
import FOLOracle as O
import Fuzz
import Graph.Tree as GTree
import List.Extra as LE
import LogicUS.FOL.SemanticTableaux as ST
import LogicUS.FOL.SemanticTableauxFV as FV exposing (FVNode, FVResult(..), FVRule(..))
import LogicUS.FOL.SyntaxSemantics as SS exposing (FormulaFOL(..), Term(..))
import Test exposing (Test, describe, fuzz, fuzz2, test)


limits : FV.FVLimits
limits =
    { gammaUses = 3, depth = 30, steps = 5000 }


tableau : List String -> FV.FVTableau
tableau ss =
    FV.semanticTableauFVWith { gammaUses = 4, depth = 60, steps = 200000 } (List.map SS.ffolRead ss)


isUnknown : FVResult -> Bool
isUnknown r =
    case r of
        Unknown _ ->
            True

        _ ->
            False


suite : Test
suite =
    describe "free-variable tableaux"
        [ fuzz2 (O.closedSet 3 2) (Fuzz.listOfLength 8 O.structure) "a closed tableau means no model (soundness)" <|
            \fs ss ->
                if FV.semanticTableauFVIsClosed (FV.semanticTableauFVWith limits fs) then
                    ss |> List.filter (\s -> List.all (O.evalClosed s) fs) |> List.length |> Expect.equal 0

                else
                    Expect.pass
        , fuzz2 (Fuzz.listOfLengthBetween 1 3 (O.closedFormulaEq 2)) (Fuzz.listOfLength 8 O.structure) "with equality: a closed tableau means no model (soundness)" <|
            \fs ss ->
                if FV.semanticTableauFVIsClosed (FV.semanticTableauFVWith limits fs) then
                    ss |> List.filter (\s -> List.all (O.evalClosed s) fs) |> List.length |> Expect.equal 0

                else
                    Expect.pass
        , fuzz (O.closedSet 3 2) "an open branch defines a model of the set" <|
            \fs ->
                let
                    t =
                        FV.semanticTableauFVWith limits fs
                in
                case ( t.result, openBranch t.tree ) of
                    ( Open, Just branch ) ->
                        let
                            s =
                                branchModel branch
                        in
                        List.filter (not << O.evalClosed s) fs |> List.map SS.ffolToString |> Expect.equal []

                    ( Open, Nothing ) ->
                        Expect.fail "an open tableau without an open leaf"

                    _ ->
                        Expect.pass
        , fuzz (Fuzz.listOfLengthBetween 1 3 (O.closedFormulaEq 2)) "with equality: an open answer has an open branch without equalities between different terms" <|
            \fs ->
                let
                    t =
                        FV.semanticTableauFVWith limits fs
                in
                case ( t.result, openBranch t.tree ) of
                    ( Open, Just branch ) ->
                        let
                            s =
                                branchModel branch
                        in
                        List.filter (not << O.evalClosed s) fs |> List.map SS.ffolToString |> Expect.equal []

                    _ ->
                        Expect.pass
        , fuzz (O.closedSet 4 2) "propositional-like sets: closed iff unsatisfiable, open iff satisfiable" <|
            \fs ->
                let
                    qf =
                        List.filter O.quantifierFree fs
                in
                if List.isEmpty qf then
                    Expect.pass

                else
                    (FV.semanticTableauFVWith limits qf).result
                        |> Expect.equal
                            (if groundSatisfiableFormulas qf then
                                Open

                             else
                                Closed
                            )
        , fuzz (O.closedSet 3 2) "the closed sets of the ground tableau are closed (with the same limit of γ uses)" <|
            \fs ->
                if ST.semanticTableauIsInsat (ST.semanticTableau fs 2 25) then
                    (FV.semanticTableauFVWith { gammaUses = 3, depth = 40, steps = 50000 } fs).result |> Expect.equal Closed

                else
                    Expect.pass
        , test "∀x(P(x) → Q(x)), ∀x P(x), ¬Q(a) closes, binding the free variables" <|
            \_ ->
                tableau [ "!A[X](P(X) -> Q(X))", "!A[X]P(X)", "¬Q(a)" ]
                    |> (\t -> ( t.result, SS.substitutionToString t.substitution ))
                    |> Expect.equal ( Closed, "{x₁/a, x₂/a}" )
        , test "the tree shows the free variables and the bindings of each closure" <|
            \_ ->
                FV.semanticTableauFVToString (tableau [ "!A[X](P(X) -> Q(X))", "!A[X]P(X)", "¬Q(a)" ])
                    |> String.lines
                    |> Expect.equal
                        [ "1. ∀x(P(x) → Q(x))"
                        , "2. ∀xP(x)"
                        , "3. ¬Q(a)"
                        , "4. (P(x₁) → Q(x₁))    % γ(1){x/x₁}"
                        , "    5. ¬P(x₁)         % β(4)"
                        , "    6. P(x₂)          % γ(2){x/x₂}"
                        , "    ✕                 % ⊥(5,6){x₂/x₁}"
                        , "    5. Q(x₁)          % β(4)"
                        , "    ✕                 % ⊥(3,5){x₁/a}"
                        , "Closed tableau (each γ formula used at most once in a branch): the set is unsatisfiable. σ = {x₁/a, x₂/a}"
                        ]
        , test "δ: a Skolem term on the free variables of the formula" <|
            \_ ->
                FV.semanticTableauFVToString (FV.semanticTableauFVWith { gammaUses = 1, depth = 10, steps = 1000 } [ SS.ffolRead "!A[Y]!E[X]¬Q(X,Y)" ])
                    |> String.contains "δ(2){x/ş₁(y₁)}"
                    |> Expect.equal True
        , test "a set with a γ formula and no closed tableau is unknown" <|
            \_ -> tableau [ "!A[X]P(X)" ] |> .result |> isUnknown |> Expect.equal True
        , test "{∀y∃x ¬Q(x,y), ∀x Q(x,x)} is not refuted" <|
            \_ -> tableau [ "!A[Y] !E[X] ¬Q(X,Y)", "!A[X] Q(X,X)" ] |> .result |> isUnknown |> Expect.equal True
        , test "a fully expanded open branch without γ formulas: satisfiable" <|
            \_ -> tableau [ "P(a) | Q(a)", "¬P(a)", "!E[X]¬Q(X)" ] |> .result |> Expect.equal Open
        , test "a vacuous quantifier is used once: {∀x R, ∃x ¬P(a)} is satisfiable" <|
            \_ -> tableau [ "!A[X]R", "!E[X]¬P(a)" ] |> .result |> Expect.equal Open
        , test "free variables of the input are constants: {P(x), ¬P(a)} is satisfiable" <|
            \_ -> tableau [ "P(X)", "¬P(a)" ] |> .result |> Expect.equal Open
        , test "an open branch with an equality between different terms is not a model" <|
            \_ -> tableau [ "a = b", "P(a)", "¬P(b)" ] |> .result |> isUnknown |> Expect.equal True
        , test "¬(t = t) closes after unification" <|
            \_ -> tableau [ "!A[X]¬(f(X) = f(a))" ] |> .result |> Expect.equal Closed
        , test "equalities close in both orientations" <|
            \_ -> tableau [ "!A[X](f(X) = a)", "¬(a = f(b))" ] |> .result |> Expect.equal Closed
        , test "the bound variables of the input are not captured by the new ones" <|
            \_ -> tableau [ "!A[X_{1}]!E[X]¬Q(X,X_{1})", "!A[X]Q(X,X)" ] |> .result |> isUnknown |> Expect.equal True
        , describe "Pelletier problems 18-46 (except 34, 38 and 43) are closed" <|
            List.map
                (\( n, fs ) -> test ("Pelletier " ++ String.fromInt n) <| \_ -> tableau fs |> .result |> Expect.equal Closed)
                pelletier
        ]



-- THE OPEN BRANCH AND ITS MODEL


openBranch : GTree.Tree FVNode -> Maybe (List FormulaFOL)
openBranch t =
    case GTree.root t of
        Just ( n, ch ) ->
            if n.rule == OpenLeaf then
                Just []

            else
                ch
                    |> List.filterMap openBranch
                    |> List.head
                    |> Maybe.map
                        (\fs ->
                            if n.rule == Closure || n.rule == LimitLeaf || n.rule == Unexplored then
                                fs

                            else
                                n.f :: fs
                        )

        Nothing ->
            Nothing


subterms : Term -> List Term
subterms t =
    case t of
        Var _ ->
            [ t ]

        Func _ ts ->
            t :: List.concatMap subterms ts


{-| The structure whose elements are the terms of the literals of the branch, plus one more for the other terms,
and where the positive literals of the branch are the true atoms.
-}
branchModel : List FormulaFOL -> O.Struct
branchModel fs =
    let
        atoms =
            List.filterMap
                (\f ->
                    case f of
                        Pred _ ts ->
                            Just ( True, f, ts )

                        Neg ((Pred _ ts) as a) ->
                            Just ( False, a, ts )

                        Equal t1 t2 ->
                            Just ( True, f, [ t1, t2 ] )

                        Neg ((Equal t1 t2) as a) ->
                            Just ( False, a, [ t1, t2 ] )

                        _ ->
                            Nothing
                )
                fs

        terms =
            LE.unique (List.concatMap (\( _, _, ts ) -> List.concatMap subterms ts) atoms)

        junk =
            List.length terms

        n =
            junk + 1

        idx t =
            Maybe.withDefault junk (LE.elemIndex t terms)

        positive =
            List.filterMap
                (\( sign, a, _ ) ->
                    if sign then
                        Just a

                    else
                        Nothing
                )
                atoms

        dom =
            List.range 0 (n - 1)

        termAt i =
            LE.getAt i terms

        holds a =
            List.member a positive

        p =
            List.map (\i -> Maybe.withDefault False (Maybe.map (\t -> holds (Pred ( "P", [] ) [ t ])) (termAt i))) dom

        q =
            List.concatMap
                (\i ->
                    List.map
                        (\j ->
                            case ( termAt i, termAt j ) of
                                ( Just t1, Just t2 ) ->
                                    holds (Pred ( "Q", [] ) [ t1, t2 ])

                                _ ->
                                    False
                        )
                        dom
                )
                dom

        fInterp =
            List.map (\i -> Maybe.withDefault junk (Maybe.map (\t -> idx (Func ( "f", [] ) [ t ])) (termAt i))) dom

        -- the Skolem functions and constants, on the terms of the branch
        extra : Dict String (Dict (List Int) Int)
        extra =
            List.foldl
                (\t d ->
                    case t of
                        Func (( name, is ) as id) args ->
                            if name == "a" || name == "b" || name == "f" then
                                d

                            else
                                Dict.update (name ++ "_" ++ String.join "," (List.map String.fromInt is))
                                    (\m -> Just (Dict.insert (List.map idx args) (idx t) (Maybe.withDefault Dict.empty m)))
                                    d

                        _ ->
                            d
                )
                Dict.empty
                terms
    in
    { n = n
    , a = idx O.cA
    , b = idx O.cB
    , f = fInterp
    , p = p
    , q = q
    , r = holds (Pred ( "R", [] ) [])
    , seed = 0
    , extra = extra
    }


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
    List.any (\ts -> List.all (evalWith ts) fs) (LE.subsequences all)



-- PELLETIER PROBLEMS: the premises and the negation of the conclusion


pelletier : List ( Int, List String )
pelletier =
    List.map (\( n, ps, c ) -> ( n, ps ++ [ "¬(" ++ c ++ ")" ] ))
        [ ( 18, [], "!E[Y]!A[X](F(Y) -> F(X))" )
        , ( 19, [], "!E[X]!A[Y]!A[Z]((P(Y) -> Q(Z)) -> (P(X) -> Q(X)))" )
        , ( 20, [ "!A[X]!A[Y]!E[Z]!A[W]((P(X) & Q(Y)) -> (R(Z) & S(W)))" ], "(!E[X]!E[Y](P(X) & Q(Y))) -> !E[Z]R(Z)" )
        , ( 21, [ "!E[X](Pp -> F(X))", "!E[X](F(X) -> Pp)" ], "!E[X](Pp <-> F(X))" )
        , ( 22, [ "!A[X](Pp <-> F(X))" ], "Pp <-> !A[X]F(X)" )
        , ( 23, [], "(!A[X](Pp | F(X))) <-> (Pp | !A[X]F(X))" )
        , ( 24, [ "¬!E[X](S(X) & Q(X))", "!A[X](P(X) -> (Q(X) | R(X)))", "(¬!E[X]P(X)) -> !E[X]Q(X)", "!A[X]((Q(X) | R(X)) -> S(X))" ], "!E[X](P(X) & R(X))" )
        , ( 25, [ "!E[X]P(X)", "!A[X](F(X) -> (¬G(X) & R(X)))", "!A[X](P(X) -> (G(X) & F(X)))", "(!A[X](P(X) -> Q(X))) | !E[X](P(X) & R(X))" ], "!E[X](Q(X) & P(X))" )
        , ( 26, [ "(!E[X]P(X)) <-> !E[X]Q(X)", "!A[X]!A[Y]((P(X) & Q(Y)) -> (R(X) <-> S(Y)))" ], "(!A[X](P(X) -> R(X))) <-> !A[X](Q(X) -> S(X))" )
        , ( 27, [ "!E[X](F(X) & ¬G(X))", "!A[X](F(X) -> H(X))", "!A[X]((J(X) & I(X)) -> F(X))", "(!E[X](H(X) & ¬G(X))) -> !A[X](I(X) -> ¬H(X))" ], "!A[X](J(X) -> ¬I(X))" )
        , ( 28, [ "!A[X](P(X) -> !A[X]Q(X))", "(!A[X](Q(X) | R(X))) -> !E[X](Q(X) & S(X))", "(!E[X]S(X)) -> !A[X](F(X) -> G(X))" ], "!A[X]((P(X) & F(X)) -> G(X))" )
        , ( 29, [ "(!E[X]F(X)) & !E[X]G(X)" ], "((!A[X](F(X) -> H(X))) & !A[X](G(X) -> J(X))) <-> !A[X]!A[Y]((F(X) & G(Y)) -> (H(X) & J(Y)))" )
        , ( 30, [ "!A[X]((F(X) | G(X)) -> ¬H(X))", "!A[X]((G(X) -> ¬I(X)) -> (F(X) & H(X)))" ], "!A[X]I(X)" )
        , ( 31, [ "¬!E[X](F(X) & (G(X) | H(X)))", "!E[X](I(X) & F(X))", "!A[X](¬H(X) -> J(X))" ], "!E[X](I(X) & J(X))" )
        , ( 32, [ "!A[X]((F(X) & (G(X) | H(X))) -> I(X))", "!A[X]((I(X) & H(X)) -> J(X))", "!A[X](K(X) -> H(X))" ], "!A[X]((F(X) & K(X)) -> J(X))" )
        , ( 33, [], "(!A[X]((P(a) & (P(X) -> P(b))) -> P(c))) <-> !A[X]((¬P(a) | P(X) | P(c)) & (¬P(a) | ¬P(b) | P(c)))" )
        , ( 35, [], "!E[X]!E[Y](P(X,Y) -> !A[X]!A[Y]P(X,Y))" )
        , ( 36, [ "!A[X]!E[Y]F(X,Y)", "!A[X]!E[Y]G(X,Y)", "!A[X]!A[Y]((F(X,Y) | G(X,Y)) -> !A[Z]((F(Y,Z) | G(Y,Z)) -> H(X,Z)))" ], "!A[X]!E[Y]H(X,Y)" )
        , ( 37, [ "!A[Z]!E[W]!A[X]!E[Y]((P(X,Z) -> P(Y,W)) & P(Y,Z) & (P(Y,W) -> !E[U]Q(U,W)))", "!A[X]!A[Z](¬P(X,Z) -> !E[Y]Q(Y,Z))", "(!E[X]!E[Y]Q(X,Y)) -> !A[X]R(X,X)" ], "!A[X]!E[Y]R(X,Y)" )
        , ( 39, [], "¬!E[X]!A[Y](F(Y,X) <-> ¬F(Y,Y))" )
        , ( 40, [], "(!E[Y]!A[X](F(X,Y) <-> F(X,X))) -> ¬!A[X]!E[Y]!A[Z](F(Z,Y) <-> ¬F(Z,X))" )
        , ( 41, [ "!A[Z]!E[Y]!A[X](F(X,Y) <-> (F(X,Z) & ¬F(X,X)))" ], "¬!E[Z]!A[X]F(X,Z)" )
        , ( 42, [], "¬!E[Y]!A[X](F(X,Y) <-> ¬!E[Z](F(X,Z) & F(Z,X)))" )
        , ( 44, [ "!A[X](F(X) -> ((!E[Y](G(Y) & H(X,Y))) & !E[Y](G(Y) & ¬H(X,Y))))", "!E[X](J(X) & !A[Y](G(Y) -> H(X,Y)))" ], "!E[X](J(X) & ¬F(X))" )
        , ( 45, [ "!A[X]((F(X) & !A[Y]((G(Y) & H(X,Y)) -> J(X,Y))) -> !A[Y]((G(Y) & H(X,Y)) -> K(Y)))", "¬!E[Y](L(Y) & K(Y))", "!E[X](F(X) & (!A[Y](H(X,Y) -> L(Y))) & !A[Y]((G(Y) & H(X,Y)) -> J(X,Y)))" ], "!E[X](F(X) & ¬!E[Y](G(Y) & H(X,Y)))" )
        , ( 46, [ "!A[X]((F(X) & !A[Y]((F(Y) & H(Y,X)) -> G(Y))) -> G(X))", "(!E[X](F(X) & ¬G(X))) -> !E[X](F(X) & ¬G(X) & !A[Y]((F(Y) & ¬G(Y)) -> J(X,Y)))", "!A[X]!A[Y]((F(X) & F(Y) & H(X,Y)) -> ¬J(Y,X))" ], "!A[X](F(X) -> G(X))" )
        ]
