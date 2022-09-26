module LogicUS.FOL.NormalForms exposing
    ( Quantifier(..)
    , ffolRemoveAllEquiv, ffolRemoveAllImpl, ffolInteriorizeNeg, ffolInteriorizeDisj, ffolInteriorizeConj
    , ffolToPrenex, ffolToPrenex2, ffolIsPrenex, ffolApplyQuantifiers, prenexGraphToDOT
    , extractHeaderQuantifiers, getSkolemSubs, ffolToSkolem, sfolToSkolem
    , ffolToNNF, ffolToCNF, ffolToDNF, sfolToNNF, sfolToCNF, sfolToDNF
    )

{-| The module provides the tools for expressing formulas in Prenex, Skolem, CNF, DNF.


# Defined types

@docs Quantifier


# Formulas Equivalent Transformations

@docs ffolRemoveAllEquiv, ffolRemoveAllImpl, ffolInteriorizeNeg, ffolInteriorizeDisj, ffolInteriorizeConj


# Prenex Form

@docs ffolToPrenex, ffolToPrenex2, ffolIsPrenex, ffolApplyQuantifiers, prenexGraphToDOT


# Skolem Form

@docs extractHeaderQuantifiers, getSkolemSubs, ffolToSkolem, sfolToSkolem


# NNF, CNF and DNF

@docs ffolToNNF, ffolToCNF, ffolToDNF, sfolToNNF, sfolToCNF, sfolToDNF

-}

import Dict
import Graph exposing (Edge, Graph, Node, nodes)
import Graph.DOT
import List
import List.Extra
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), SetFOL, Substitution, Term(..), Variable, ffolApplySubstitution, ffolFreeVars)



-- Auxiliar Functions
-- Regular Functions


{-| It represents the universal (all) and existencial (exists) quantifier with the associated variable
-}
type Quantifier
    = A Variable
    | E Variable



-- It represents the result of the prenex auxiliar calculation for prenex graph construction-}


type alias PrenexCalcResult =
    { nodes : List (Node FormulaFOL)
    , edges : List (Edge ( Bool, List Quantifier ))
    , cuants : List Quantifier
    , f : FormulaFOL
    }



-- It indicates if a quantifier is exitencial-like


isEQuantifier : Quantifier -> Bool
isEQuantifier c =
    case c of
        A _ ->
            False

        E _ ->
            True



-- It gives the contrary quantifier


contraryQuantifier : Quantifier -> Quantifier
contraryQuantifier c =
    case c of
        A x ->
            E x

        E x ->
            A x



-- It quantifies a formula with the quantifier given


applyQuantifier : Quantifier -> FormulaFOL -> FormulaFOL
applyQuantifier c f =
    case c of
        A x ->
            Forall x f

        E x ->
            Exists x f


{-| It quantifies a formula with the quantifiers given by following the reverse order on applying it (tail to head)
-}
ffolApplyQuantifiers : List Quantifier -> FormulaFOL -> FormulaFOL
ffolApplyQuantifiers cs f =
    List.foldr applyQuantifier f cs



-- It sort two list of quantifiers by choosing first the existencial (keeping the order in the corresponding lists)


sortWithFirstE : List Quantifier -> List Quantifier -> List Quantifier
sortWithFirstE l1 l2 =
    sortWithFirstEAux l1 l2 []


sortWithFirstEAux : List Quantifier -> List Quantifier -> List Quantifier -> List Quantifier
sortWithFirstEAux l1 l2 res =
    case l1 of
        [] ->
            res ++ l2

        (E x) :: ls1 ->
            sortWithFirstEAux ls1 l2 (res ++ [ E x ])

        _ ->
            case l2 of
                [] ->
                    res ++ l1

                (E x) :: ls2 ->
                    sortWithFirstEAux l1 ls2 (res ++ [ E x ])

                _ ->
                    let
                        ( xs1, ys1 ) =
                            List.Extra.break (\x -> isEQuantifier x) l1

                        ( xs2, ys2 ) =
                            List.Extra.break (\x -> isEQuantifier x) l2
                    in
                    if List.isEmpty ys2 then
                        res ++ l1 ++ xs2

                    else if List.isEmpty ys1 then
                        res ++ l2 ++ xs1

                    else if List.length xs2 < List.length xs1 then
                        sortWithFirstEAux l1 ys2 (res ++ xs2)

                    else
                        sortWithFirstEAux ys1 l2 (res ++ xs1)



-- FORMULA TRANSFORMATIONS


{-| It allows extract all the external quantifiers, especially interesting for applying over Prenex Form Formulas
-}
extractHeaderQuantifiers : FormulaFOL -> ( List Quantifier, FormulaFOL )
extractHeaderQuantifiers f =
    case f of
        Forall x g ->
            let
                ( cuants, h ) =
                    extractHeaderQuantifiers g
            in
            ( A x :: cuants, h )

        Exists x g ->
            let
                ( cuants, h ) =
                    extractHeaderQuantifiers g
            in
            ( E x :: cuants, h )

        _ ->
            ( [], f )


{-| It removes all the equivalences by changing it by the conjuction of the implications
-}
ffolRemoveAllEquiv : FormulaFOL -> FormulaFOL
ffolRemoveAllEquiv f =
    case f of
        Pred _ _ ->
            f

        Equal _ _ ->
            f

        Neg h ->
            Neg (ffolRemoveAllEquiv h)

        Conj x y ->
            Conj (ffolRemoveAllEquiv x) (ffolRemoveAllEquiv y)

        Disj x y ->
            Disj (ffolRemoveAllEquiv x) (ffolRemoveAllEquiv y)

        Impl x y ->
            Impl (ffolRemoveAllEquiv x) (ffolRemoveAllEquiv y)

        Equi x y ->
            Conj (Impl (ffolRemoveAllEquiv x) (ffolRemoveAllEquiv y)) (Impl (ffolRemoveAllEquiv y) (ffolRemoveAllEquiv x))

        Insat ->
            Insat

        Taut ->
            Taut

        Exists v h ->
            Exists v (ffolRemoveAllEquiv h)

        Forall v h ->
            Forall v (ffolRemoveAllEquiv h)


{-| It removes all the equivalences by changing it by the disjunction of the negation of the antecedent and the consecuent
-}
ffolRemoveAllImpl : FormulaFOL -> FormulaFOL
ffolRemoveAllImpl f =
    case f of
        Pred _ _ ->
            f

        Equal _ _ ->
            f

        Neg x ->
            Neg (ffolRemoveAllImpl x)

        Conj x y ->
            Conj (ffolRemoveAllImpl x) (ffolRemoveAllImpl y)

        Disj x y ->
            Disj (ffolRemoveAllImpl x) (ffolRemoveAllImpl y)

        Impl x y ->
            Disj (Neg (ffolRemoveAllImpl x)) (ffolRemoveAllImpl y)

        Equi x y ->
            Conj (ffolRemoveAllImpl <| Impl x y) (ffolRemoveAllImpl <| Impl x y)

        Forall v g ->
            Forall v (ffolRemoveAllImpl g)

        Exists v g ->
            Exists v (ffolRemoveAllImpl g)

        Insat ->
            Insat

        Taut ->
            Taut


{-| It interiorizes negations applying the De Morgan Rule and the rule of negation of the quantifier
-}
ffolInteriorizeNeg : FormulaFOL -> FormulaFOL
ffolInteriorizeNeg f =
    let
        aux g =
            case g of
                Pred _ _ ->
                    Neg g

                Equal _ _ ->
                    Neg g

                Neg h ->
                    ffolInteriorizeNeg h

                Conj x y ->
                    Disj (aux x) (aux y)

                Disj x y ->
                    Conj (aux x) (aux y)

                Impl x y ->
                    Conj (ffolInteriorizeNeg x) (aux y)

                Equi x y ->
                    Disj (aux (Impl x y)) (aux (Impl y x))

                Insat ->
                    Taut

                Taut ->
                    Insat

                Exists v h ->
                    Forall v (aux h)

                Forall v h ->
                    Exists v (aux h)
    in
    case f of
        Pred _ _ ->
            f

        Equal _ _ ->
            f

        Neg h ->
            aux h

        Conj x y ->
            Conj (ffolInteriorizeNeg x) (ffolInteriorizeNeg y)

        Disj x y ->
            Disj (ffolInteriorizeNeg x) (ffolInteriorizeNeg y)

        Impl x y ->
            Impl (ffolInteriorizeNeg x) (ffolInteriorizeNeg y)

        Equi x y ->
            Equi (ffolInteriorizeNeg x) (ffolInteriorizeNeg y)

        Insat ->
            Insat

        Taut ->
            Taut

        Exists v h ->
            Exists v (ffolInteriorizeNeg h)

        Forall v h ->
            Forall v (ffolInteriorizeNeg h)


{-| It interiorizes the disjunctions by applying distributive rule
-}
ffolInteriorizeDisj : FormulaFOL -> FormulaFOL
ffolInteriorizeDisj f =
    case f of
        Disj (Conj f1 f2) g ->
            ffolInteriorizeDisj <| Conj (Disj f1 g) (Disj f2 g)

        Disj g (Conj f1 f2) ->
            ffolInteriorizeDisj <| Conj (Disj g f1) (Disj g f2)

        Conj f1 f2 ->
            Conj (ffolInteriorizeDisj f1) (ffolInteriorizeDisj f2)

        Disj f1 f2 ->
            let
                g1 =
                    ffolInteriorizeDisj f1

                g2 =
                    ffolInteriorizeDisj f2
            in
            case g1 of
                Conj _ _ ->
                    ffolInteriorizeDisj <| Disj g1 g2

                _ ->
                    case g2 of
                        Conj _ _ ->
                            ffolInteriorizeDisj <| Disj g1 g2

                        _ ->
                            f

        _ ->
            f


{-| It interiorizes the conjunctions by applying distributive rule
-}
ffolInteriorizeConj : FormulaFOL -> FormulaFOL
ffolInteriorizeConj f =
    case f of
        Conj (Disj f1 f2) g ->
            ffolInteriorizeConj <| Disj (Conj f1 g) (Conj f2 g)

        Conj g (Disj f1 f2) ->
            ffolInteriorizeConj <| Disj (Conj g f1) (Conj g f2)

        Disj f1 f2 ->
            Disj (ffolInteriorizeConj f1) (ffolInteriorizeConj f2)

        Conj f1 f2 ->
            let
                g1 =
                    ffolInteriorizeConj f1

                g2 =
                    ffolInteriorizeConj f2
            in
            case g1 of
                Disj _ _ ->
                    ffolInteriorizeConj <| Conj g1 g2

                _ ->
                    case g2 of
                        Disj _ _ ->
                            ffolInteriorizeConj <| Conj g1 g2

                        _ ->
                            f

        _ ->
            f



-- PRENEX FORM


{-| It transforms a FOL Formula into one equivalent Prenex Form
-}
ffolToPrenex : FormulaFOL -> FormulaFOL
ffolToPrenex f =
    let
        f1 =
            ffolRemoveAllEquiv f
    in
    let
        f2 =
            FOL_SS.ffolRenameVars f1
    in
    let
        f3 =
            ffolInteriorizeNeg f2
    in
    let
        ret1 =
            ffolToPrenexAux 3 f3
    in
    ffolApplyQuantifiers ret1.cuants ret1.f


{-| It transforms a FOL Formula into one equivalent Prenex Form. It gives the list of quantifiers and the open formula of the Prenex Form. It also gives a Graph with the Prenex form calculus
-}
ffolToPrenex2 : FormulaFOL -> ( List Quantifier, FormulaFOL, Graph FormulaFOL ( Bool, List Quantifier ) )
ffolToPrenex2 f =
    let
        f1 =
            ffolRemoveAllEquiv f
    in
    let
        f2 =
            FOL_SS.ffolRenameVars f1
    in
    let
        f3 =
            ffolInteriorizeNeg f2
    in
    let
        ret1 =
            ffolToPrenexAux 4 f3
    in
    let
        nodes_extra =
            (if f /= f3 then
                [ Node 1 f ]

             else
                []
            )
                ++ (if f1 /= f && f1 /= f3 then
                        [ Node 2 f1 ]

                    else
                        []
                   )
                ++ (if f2 /= f1 && f2 /= f3 then
                        [ Node 3 f2 ]

                    else
                        []
                   )
    in
    let
        edges_extra =
            if List.isEmpty nodes_extra then
                []

            else
                Tuple.second <| List.foldr (\n ( j, es ) -> ( n.id, Edge n.id j ( False, [] ) :: es )) ( 4, [] ) nodes_extra
    in
    ( ret1.cuants, ret1.f, Graph.fromNodesAndEdges (nodes_extra ++ ret1.nodes) (edges_extra ++ ret1.edges) )



-- let
--     nodes_res =
--         (if f == f3 then
--             []
--          else
--             [ Node 1 f ]
--         )
--             ++ (if f == f1 then
--                     []
--                 else
--                     [ Node 2 f1 ]
--                )
--             ++ (if f1 == f2 then
--                     []
--                 else
--                     [ Node 3 f2 ]
--                )
--             ++
--     edges_res =
--         (if f /= f1 then
--             [ Edge 1 2 ( False, [] ) ]
--          else
--             []
--         )
--             ++ (if f1 /= f2 then
--                     [ Edge 2 3 ( False, [] ), Edge 3 4 ( False, [] ) ]
--                 else if f /= f1 then
--                     [ Edge 2 4 ( False, [] ) ]
--                 else if f /= f3 then
--                     [ Edge 1 4 ( False, [] ) ]
--                 else
--                     []
--                )
--             ++ ret1.edges
-- in
-- ( ret1.cuants, ret1.f, Graph.fromNodesAndEdges nodes_res edges_res )
-- It calculates Prenex Form of a Formula


ffolToPrenexAux : Int -> FormulaFOL -> PrenexCalcResult
ffolToPrenexAux nid f =
    case f of
        Conj g h ->
            let
                ret1 =
                    ffolToPrenexAux (nid + 1) g
            in
            let
                max_nid1 =
                    nid + List.length ret1.nodes
            in
            let
                ret2 =
                    ffolToPrenexAux (max_nid1 + 1) h
            in
            let
                max_nid2 =
                    max_nid1 + List.length ret2.nodes
            in
            let
                cuants =
                    sortWithFirstE ret1.cuants ret2.cuants

                openFormula =
                    Conj ret1.f ret2.f
            in
            let
                nodes =
                    [ Node nid f, Node (max_nid2 + 1) (ffolApplyQuantifiers cuants <| openFormula) ] ++ ret1.nodes ++ ret2.nodes

                edges =
                    [ Edge nid (nid + 1) ( False, [] )
                    , Edge nid (max_nid1 + 1) ( False, [] )
                    , Edge max_nid1 (max_nid2 + 1) ( True, ret1.cuants )
                    , Edge max_nid2 (max_nid2 + 1) ( False, ret2.cuants )
                    ]
                        ++ ret1.edges
                        ++ ret2.edges
            in
            { nodes = nodes, edges = edges, cuants = cuants, f = openFormula }

        Disj g h ->
            let
                ret1 =
                    ffolToPrenexAux (nid + 1) g
            in
            let
                max_nid1 =
                    nid + List.length ret1.nodes
            in
            let
                ret2 =
                    ffolToPrenexAux (max_nid1 + 1) h
            in
            let
                max_nid2 =
                    max_nid1 + List.length ret2.nodes
            in
            let
                cuants =
                    sortWithFirstE ret1.cuants ret2.cuants

                openFormula =
                    Disj ret1.f ret2.f
            in
            let
                nodes =
                    [ Node nid f, Node (max_nid2 + 1) (ffolApplyQuantifiers cuants <| openFormula) ] ++ ret1.nodes ++ ret2.nodes

                edges =
                    [ Edge nid (nid + 1) ( False, [] )
                    , Edge nid (max_nid1 + 1) ( False, [] )
                    , Edge max_nid1 (max_nid2 + 1) ( True, ret1.cuants )
                    , Edge max_nid2 (max_nid2 + 1) ( False, ret2.cuants )
                    ]
                        ++ ret1.edges
                        ++ ret2.edges
            in
            { nodes = nodes, edges = edges, cuants = cuants, f = openFormula }

        Impl g h ->
            let
                ret1 =
                    ffolToPrenexAux (nid + 1) g
            in
            let
                max_nid1 =
                    nid + List.length ret1.nodes
            in
            let
                ret2 =
                    ffolToPrenexAux (max_nid1 + 1) h
            in
            let
                max_nid2 =
                    max_nid1 + List.length ret2.nodes
            in
            let
                cuants =
                    sortWithFirstE (List.map contraryQuantifier ret1.cuants) ret2.cuants

                openFormula =
                    Impl ret1.f ret2.f
            in
            let
                nodes =
                    [ Node nid f, Node (max_nid2 + 1) (ffolApplyQuantifiers cuants <| openFormula) ] ++ ret1.nodes ++ ret2.nodes

                edges =
                    [ Edge nid (nid + 1) ( False, [] )
                    , Edge nid (max_nid1 + 1) ( False, [] )
                    , Edge max_nid1 (max_nid2 + 1) ( True, List.map contraryQuantifier ret1.cuants )
                    , Edge max_nid2 (max_nid2 + 1) ( False, ret2.cuants )
                    ]
                        ++ ret1.edges
                        ++ ret2.edges
            in
            { nodes = nodes, edges = edges, cuants = cuants, f = openFormula }

        g ->
            let
                ( cuants1, h ) =
                    extractHeaderQuantifiers g
            in
            if FOL_SS.ffolIsOpen h then
                { nodes = [ Node nid f ], edges = [], cuants = cuants1, f = h }

            else
                let
                    ret1 =
                        ffolToPrenexAux (nid + 1) h
                in
                let
                    max_nid1 =
                        nid + List.length ret1.nodes

                    cuants =
                        cuants1 ++ ret1.cuants
                in
                let
                    nodes =
                        [ Node nid f, Node (max_nid1 + 1) (ffolApplyQuantifiers cuants <| ret1.f) ] ++ ret1.nodes

                    edges =
                        [ Edge nid (nid + 1) ( False, [] ), Edge max_nid1 (max_nid1 + 1) ( False, [] ) ] ++ ret1.edges
                in
                { nodes = nodes, edges = edges, cuants = cuants, f = ret1.f }


{-| It indicates if a formula is in Prenex Form
-}
ffolIsPrenex : FormulaFOL -> Bool
ffolIsPrenex f =
    case f of
        Pred _ _ ->
            True

        Equal _ _ ->
            True

        Neg g ->
            FOL_SS.ffolIsOpen g

        Conj g h ->
            FOL_SS.ffolIsOpen g && FOL_SS.ffolIsOpen h

        Disj g h ->
            FOL_SS.ffolIsOpen g && FOL_SS.ffolIsOpen h

        Impl g h ->
            FOL_SS.ffolIsOpen g && FOL_SS.ffolIsOpen h

        Equi g h ->
            FOL_SS.ffolIsOpen g && FOL_SS.ffolIsOpen h

        Forall _ g ->
            ffolIsPrenex g

        Exists _ g ->
            ffolIsPrenex g

        Insat ->
            True

        Taut ->
            True


{-| It allows represent the Prenex Calculus Graph as DOT string, which could be rendered by GraphViz
-}
prenexGraphToDOT : Graph FormulaFOL ( Bool, List Quantifier ) -> String
prenexGraphToDOT g =
    let
        toStringQuantifier c =
            case c of
                A t ->
                    "∀" ++ FOL_SS.termToString (Var t)

                E t ->
                    "∃" ++ FOL_SS.termToString (Var t)
    in
    String.replace "\n" "" <|
        Graph.DOT.output
            (Just << FOL_SS.ffolToString)
            (\( cent, xs ) ->
                if xs == [] then
                    Nothing

                else
                    Just <|
                        (if cent then
                            "*"

                         else
                            ""
                        )
                            ++ (String.join "," <| List.map toStringQuantifier xs)
            )
        <|
            g



-- SKOLEM FORM


{-| It gives the Skolem functions correspondence of a list of quantifiers
-}
getSkolemSubs : List Quantifier -> Substitution
getSkolemSubs cS =
    let
        ( subs, _, _ ) =
            List.foldl
                (\c ( res, lF, nE ) ->
                    case c of
                        A x ->
                            ( res, lF ++ [ Var x ], nE )

                        E x ->
                            let
                                nres =
                                    Dict.insert x (Func ( "ş", [ nE + 1 ] ) lF) res
                            in
                            ( nres, lF, nE + 1 )
                )
                ( Dict.empty, [], 0 )
                cS
    in
    subs


{-| It calculates the Skolem Form of a Formula, by prenexization plus the introduction of skolem functions
-}
ffolToSkolem : FormulaFOL -> FormulaFOL
ffolToSkolem f =
    if ffolIsPrenex f then
        let
            ( lc, g ) =
                extractHeaderQuantifiers f
        in
        FOL_SS.ffolApplySubstitution (getSkolemSubs lc) g

    else
        let
            f1 =
                ffolRemoveAllEquiv f
        in
        let
            f2 =
                FOL_SS.ffolRenameVars f1
        in
        let
            f3 =
                ffolInteriorizeNeg f2
        in
        ffolToPrenex <| Tuple.first <| ffolToSkolem2Aux True 1 f3



{- It transforms a formula from a FOL into an equiconsistent formula with replacing existential quantifiers by skolem functions depending on the free variables that occurs in the corresponding subformula. -}


ffolToSkolem2Aux : Bool -> Int -> FormulaFOL -> ( FormulaFOL, Int )
ffolToSkolem2Aux b i f =
    case f of
        Conj g h ->
            let
                ( f1, i1 ) =
                    ffolToSkolem2Aux b i g
            in
            let
                ( f2, i2 ) =
                    ffolToSkolem2Aux b i1 h
            in
            ( Conj f1 f2, i2 )

        Disj g h ->
            let
                ( f1, i1 ) =
                    ffolToSkolem2Aux b i g
            in
            let
                ( f2, i2 ) =
                    ffolToSkolem2Aux b i1 h
            in
            ( Disj f1 f2, i2 )

        Impl g h ->
            let
                ( f1, i1 ) =
                    ffolToSkolem2Aux (not b) i g
            in
            let
                ( f2, i2 ) =
                    ffolToSkolem2Aux b i1 h
            in
            ( Impl f1 f2, i2 )

        Exists v g ->
            if b then
                let
                    ls =
                        ffolFreeVars f
                in
                let
                    ss =
                        Dict.singleton v (Func ( "ş", [ i ] ) <| List.map Var ls)
                in
                let
                    h =
                        ffolApplySubstitution ss g
                in
                ffolToSkolem2Aux b (i + 1) h

            else
                let
                    ( h, i1 ) =
                        ffolToSkolem2Aux b i g
                in
                ( h, i1 )

        Forall v g ->
            if b then
                let
                    ( h, i1 ) =
                        ffolToSkolem2Aux b i g
                in
                ( h, i1 )

            else
                let
                    ls =
                        ffolFreeVars f
                in
                let
                    ss =
                        Dict.singleton v (Func ( "ş", [ i ] ) <| List.map Var ls)
                in
                let
                    h =
                        ffolApplySubstitution ss g
                in
                ffolToSkolem2Aux b (i + 1) h

        _ ->
            ( f, i )


{-| It calculates the Skolem Forms of the formulas of a set (by using ffolToSkolem2)
-}
sfolToSkolem : SetFOL -> SetFOL
sfolToSkolem fs =
    Tuple.first <|
        List.foldl
            (\f ( ls, i ) ->
                let
                    ( g, j ) =
                        ffolToSkolem2Aux True i f
                in
                ( ls ++ [ g ], j )
            )
            ( [], 1 )
            fs



-- NNF, CNF AND DNF


{-| It calculates a negative normal form of a formula
-}
ffolToNNF : FormulaFOL -> FormulaFOL
ffolToNNF f =
    (ffolToSkolem << ffolInteriorizeNeg << ffolRemoveAllImpl << ffolRemoveAllEquiv) f


{-| It calculates negative normal forms of formulas of a set
-}
sfolToNNF : SetFOL -> SetFOL
sfolToNNF fs =
    sfolToSkolem <| List.map (ffolInteriorizeNeg << ffolRemoveAllImpl << ffolRemoveAllEquiv) fs


{-| It calculates a conjuctive normal form of a formula
-}
ffolToCNF : FormulaFOL -> FormulaFOL
ffolToCNF f =
    ffolInteriorizeDisj <| ffolToNNF f


{-| It calculates conjuctive normal forms of formulas of a set
-}
sfolToCNF : SetFOL -> SetFOL
sfolToCNF fs =
    List.map ffolInteriorizeDisj <| sfolToNNF fs


{-| It calculates a disjuntive normal form of a formula
-}
ffolToDNF : FormulaFOL -> FormulaFOL
ffolToDNF f =
    ffolInteriorizeConj <| ffolToNNF f


{-| It calculates disjunctive normal forms of formulas of a set
-}
sfolToDNF : SetFOL -> SetFOL
sfolToDNF fs =
    List.map ffolInteriorizeConj <| sfolToNNF fs
