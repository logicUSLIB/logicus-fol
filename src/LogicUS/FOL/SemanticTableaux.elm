module LogicUS.FOL.SemanticTableaux exposing
    ( FormulaFOLType, FOLSemanticTableau, TableauNodeItem, TableauEdgeItem
    , ffolType, ffolUncuantifiedComponents, ffolCuantifiedComponents
    , semanticTableau, semanticTableauIsInsat, semanticTableauRUNII
    , semanticTableauToString, semanticTableauToDOT
    )

{-| The module provides the elementary tools for building the semantic tableau of a set of FOL formulas.


# Definition Types

@docs FormulaFOLType, FOLSemanticTableau, TableauNodeItem, TableauEdgeItem


# Formulas types and components

@docs ffolType, ffolUncuantifiedComponents, ffolCuantifiedComponents


# Semantic Tableau Algorithm

@docs semanticTableau, semanticTableauIsInsat, semanticTableauRUNII


# Fuctions for representation

@docs semanticTableauToString, semanticTableauToDOT

-}

import Dict exposing (Dict)
import Graph exposing (Edge, Graph, Node, nodes)
import Graph.DOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.AUX.AuxiliarFuctions exposing (replaceBySubscript, uniqueConcatList)
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), SetFOL, Substitution, Term(..), Variable)


{-| It defines the type of a PL formula which can be a _Literal_, _Double Negation_, _Alpha_, _Beta_, _Gamma_ (forall), _Delta_(exists) _Insat_ or _Taut_
-}
type FormulaFOLType
    = L
    | E
    | DN
    | A
    | B
    | G
    | D
    | I
    | T


{-| Defines the FOL Semantic Tableau type as a Graph whose node labels are pairs of an integer (0: internal node, 1: open leaf, -1: closed leaf) and a TableauNodeItem that contains some information for representation; and the edge labels are defined as TableauEdgeItem although some edges could not have any edge.
-}
type alias FOLSemanticTableau =
    Graph ( Int, TableauNodeItem ) (Maybe TableauEdgeItem)


{-| Defines the TableauNodeItem that is a record with the following features: 'f' the formula considered, 't' the type of the formula, 'u' the usability degree of the formula, 'ut': a list of terms with wich a gamma formula is solved, 'i':the index of the node (only for print the tableau), 'ps': the premises from which the formula is concluded
-}
type alias TableauNodeItem =
    { f : FormulaFOL
    , t : FormulaFOLType
    , u : Int
    , ut : List Term
    , i : Int
    , ps : List Int
    , ant : Int
    }


{-| Defines the TableauEdgeItem that is a record with the following features 'r' the rule applied in the deduction, 'id' the set of indices over that the rule is applied, 'br' the identifier of the branch (only used in beta bifurcations), 's' the substitution done over the formula (only in gamma and delta rules).
-}
type alias TableauEdgeItem =
    { r : FormulaFOLType
    , is : List Int
    , br : Int
    , s : Substitution
    }



--====================--
-- REGULARY FUNCTIONS --
--====================--


{-| It gives the class of a FOL formula. Atoms (predicates) and their negations are literals, double negation are typed as DN, conjunction, equivalence are classified as ALPHA, disjunction and implications are classified as BETA. forall-like formulas are classified as GAMMA and existencial-like ones as DELTA The negation of an alpha formula is a beta and vice versa, and the same happens with forall and exists like ones.
-}
ffolType : FormulaFOL -> FormulaFOLType
ffolType f =
    case f of
        Neg (Neg _) ->
            DN

        Pred _ _ ->
            L

        Neg (Pred _ _) ->
            L

        Equal _ _ ->
            E

        Neg (Equal t1 t2) ->
            if t1 == t2 then
                I

            else
                L

        Conj _ _ ->
            A

        Neg (Conj _ _) ->
            B

        Disj _ _ ->
            B

        Neg (Disj _ _) ->
            A

        Impl _ _ ->
            B

        Neg (Impl _ _) ->
            A

        Equi _ _ ->
            A

        Neg (Equi _ _) ->
            B

        Exists _ _ ->
            D

        Neg (Exists _ _) ->
            G

        Forall _ _ ->
            G

        Neg (Forall _ _) ->
            D

        Taut ->
            T

        Neg Taut ->
            I

        Insat ->
            I

        Neg Insat ->
            T


{-| It gives the components of a uncuantified formula for using them in the expansion of a semantic board
-}
ffolUncuantifiedComponents : FormulaFOL -> SetFOL
ffolUncuantifiedComponents f =
    case f of
        Neg (Neg g) ->
            [ g ]

        Pred _ _ ->
            [ f ]

        Neg (Pred _ _) ->
            [ f ]

        Equal _ _ ->
            [ f ]

        Neg (Equal _ _) ->
            [ f ]

        Conj g h ->
            [ g, h ]

        Neg (Conj g h) ->
            [ FOL_SS.ffolNegation g, FOL_SS.ffolNegation h ]

        Disj g h ->
            [ g, h ]

        Neg (Disj g h) ->
            [ FOL_SS.ffolNegation g, FOL_SS.ffolNegation h ]

        Impl g h ->
            [ FOL_SS.ffolNegation g, h ]

        Neg (Impl g h) ->
            [ g, FOL_SS.ffolNegation h ]

        Equi g h ->
            [ Impl g h, Impl h g ]

        Neg (Equi g h) ->
            [ FOL_SS.ffolNegation (Impl g h), FOL_SS.ffolNegation (Impl h g) ]

        Taut ->
            [ Taut ]

        Neg Taut ->
            [ Taut ]

        Insat ->
            [ Taut ]

        Neg Insat ->
            [ Taut ]

        _ ->
            []


{-| It gives the components of a cuantified formula for using them in the expansion of a semantic board
-}
ffolCuantifiedComponents : FormulaFOL -> Maybe ( Variable, FormulaFOL )
ffolCuantifiedComponents f =
    case f of
        Exists v g ->
            Just ( v, g )

        Neg (Exists v g) ->
            Just ( v, FOL_SS.ffolNegation g )

        Forall v g ->
            Just ( v, g )

        Neg (Forall v g) ->
            Just ( v, FOL_SS.ffolNegation g )

        _ ->
            Nothing



-- It gives if in the nodes of the esplored branch is there any contradiction. If it is discovered, it return the list of formulas implied in it


searchContradiction : List ( Int, ( Int, TableauNodeItem ) ) -> Maybe ( List Int, List Int )
searchContradiction nodes =
    case nodes of
        [] ->
            Nothing

        ( i, ( _, ti ) ) :: xs ->
            if ti.t == I then
                Just ( [ i ], [ ti.i ] )

            else
                case List.head <| List.filter (\( _, ( _, ti2 ) ) -> ti.f == FOL_SS.ffolNegation ti2.f) xs of
                    Nothing ->
                        searchContradiction xs

                    Just ( i2, ( _, ti2 ) ) ->
                        Just ( [ i, i2 ], [ ti.i, ti2.i ] )



-- Generate new constant where existencial formula is processed


generateNewConst : Int -> List Term -> Term
generateNewConst i m =
    let
        c =
            Func ( "c", [ i ] ) []
    in
    if List.member c m then
        generateNewConst (i + 1) m

    else
        c


{-| It performs the Semantic Tableaux algorithm on a set of FOL formulas. As the algorithm can be infinite, you must indicate the maximum depth allowed. Specifically, you must specify the maximum number of times a gamma formula can be used and the absolute limit for the depth of the tree.
-}
semanticTableau : SetFOL -> Int -> Int -> FOLSemanticTableau
semanticTableau fs uMax dMax =
    let
        nodes =
            Dict.fromList <| List.indexedMap (\i f -> ( i, ( 0, { f = f, t = ffolType f, u = uMax, ut = [], i = i, ps = [], ant = i - 1 } ) )) fs

        edges =
            Dict.fromList <| List.indexedMap (\i v -> ( ( i, i + 1 ), v )) <| List.repeat (List.length fs - 1) Nothing

        m =
            uniqueConcatList [] <| List.concat <| List.map FOL_SS.ffolAllClosedTerms fs
    in
    let
        ( res_nodes, res_edges ) =
            semanticTableauAux m dMax uMax (List.length fs) (List.length fs) (List.length fs - 1) 0 nodes edges
    in
    Graph.fromNodesAndEdges
        (List.map (\( k, v ) -> Node k v) <| Dict.toList <| res_nodes)
        (List.map (\( ( s, t ), v ) -> Edge s t v) <| Dict.toList <| res_edges)



-- It is the reall performer of the algorithm generating the data for construct the tree.


semanticTableauAux :
    List Term
    -> Int
    -> Int
    -> Int
    -> Int
    -> Int
    -> Int
    -> Dict Int ( Int, TableauNodeItem )
    -> Dict ( Int, Int ) (Maybe TableauEdgeItem)
    -> ( Dict Int ( Int, TableauNodeItem ), Dict ( Int, Int ) (Maybe TableauEdgeItem) )
semanticTableauAux m dMax uMax nid nid2 nidp dcur nodes edges =
    case searchContradiction <| Dict.toList nodes of
        Just ( xig, xif ) ->
            let
                dictNodes =
                    Dict.insert nid ( -1, { f = Insat, t = I, u = uMax, ut = [], i = nid2, ps = xig, ant = nidp } ) nodes

                dictEdges =
                    Dict.insert ( nidp, nid ) (Just { r = I, is = xif, br = 1, s = Dict.empty }) edges
            in
            ( dictNodes, dictEdges )

        Nothing ->
            if dcur == dMax then
                let
                    g =
                        Maybe.withDefault Insat <| Maybe.map (\x -> (Tuple.second x).f) <| Dict.get nidp nodes
                in
                ( Dict.insert nid ( 1, { f = g, t = I, u = uMax, ut = [], i = nid2, ps = [], ant = nidp } ) nodes
                , Dict.insert ( nidp, nid ) Nothing edges
                )

            else
                case List.head <| List.filter (\( _, ( _, ti ) ) -> ti.t == DN && ti.u /= 0) <| Dict.toList nodes of
                    Just ( i, ( _, ti ) ) ->
                        let
                            g =
                                Maybe.withDefault Insat <| List.head <| ffolUncuantifiedComponents ti.f
                        in
                        let
                            new_nodes =
                                Dict.insert nid ( 0, { f = g, t = ffolType g, u = uMax, ut = [], i = nid2, ps = [ i ], ant = nidp } ) <|
                                    Dict.insert i ( 0, { ti | u = 0 } ) nodes

                            new_edges =
                                Dict.insert ( nidp, nid ) (Just { r = DN, is = [ ti.i ], br = 1, s = Dict.empty }) edges
                        in
                        semanticTableauAux m dMax uMax (nid + 1) (nid2 + 1) nid (dcur + 1) new_nodes new_edges

                    Nothing ->
                        case List.head <| List.filter (\( _, ( _, ti ) ) -> ti.t == A && ti.u /= 0) <| Dict.toList nodes of
                            Just ( i, ( _, ti ) ) ->
                                let
                                    ( g, h ) =
                                        case ffolUncuantifiedComponents ti.f of
                                            [ g1, h1 ] ->
                                                ( g1, h1 )

                                            _ ->
                                                ( Insat, Insat )
                                in
                                let
                                    new_nodes =
                                        Dict.insert (nid + 1) ( 0, { f = h, t = ffolType h, u = uMax, ut = [], i = nid2 + 1, ps = [ i ], ant = nid } ) <|
                                            Dict.insert nid ( 0, { f = g, t = ffolType g, u = uMax, ut = [], i = nid2, ps = [ i ], ant = nidp } ) <|
                                                Dict.insert i ( 0, { ti | u = 0 } ) nodes

                                    new_edges =
                                        Dict.insert ( nid, nid + 1 ) (Just { r = A, is = [ ti.i ], br = 2, s = Dict.empty }) <|
                                            Dict.insert ( nidp, nid ) (Just { r = A, is = [ ti.i ], br = 1, s = Dict.empty }) edges
                                in
                                semanticTableauAux m dMax uMax (nid + 2) (nid2 + 2) (nid + 1) (dcur + 1) new_nodes new_edges

                            Nothing ->
                                case List.head <| List.filter (\( _, ( _, ti ) ) -> ti.t == B && ti.u /= 0) <| Dict.toList nodes of
                                    Just ( i, ( _, ti ) ) ->
                                        let
                                            ( g, h ) =
                                                case ffolUncuantifiedComponents ti.f of
                                                    [ g1, h1 ] ->
                                                        ( g1, h1 )

                                                    _ ->
                                                        ( Insat, Insat )
                                        in
                                        let
                                            new_nodes1 =
                                                Dict.insert nid ( 0, { f = g, t = ffolType g, u = uMax, ut = [], i = nid2, ps = [ i ], ant = nidp } ) <|
                                                    Dict.insert i ( 0, { ti | u = 0 } ) nodes

                                            new_edges1 =
                                                Dict.insert ( nidp, nid ) (Just { r = B, is = [ ti.i ], br = 1, s = Dict.empty }) edges
                                        in
                                        let
                                            ( nodes1, edges1 ) =
                                                semanticTableauAux m dMax uMax (nid + 1) (nid2 + 1) nid (dcur + 1) new_nodes1 new_edges1
                                        in
                                        let
                                            new_nid =
                                                1 + (Maybe.withDefault 0 <| List.maximum <| Dict.keys nodes1)
                                        in
                                        let
                                            new_nodes2 =
                                                Dict.insert new_nid ( 0, { f = h, t = ffolType h, u = uMax, ut = [], i = nid2, ps = [ i ], ant = nidp } ) <|
                                                    Dict.insert i ( 0, { ti | u = 0 } ) nodes

                                            new_edges2 =
                                                Dict.insert ( nidp, new_nid ) (Just { r = B, is = [ ti.i ], br = 2, s = Dict.empty }) edges
                                        in
                                        let
                                            ( nodes2, edges2 ) =
                                                semanticTableauAux m dMax uMax (new_nid + 1) (nid2 + 1) new_nid (dcur + 1) new_nodes2 new_edges2
                                        in
                                        ( Dict.union nodes1 nodes2, Dict.union edges1 edges2 )

                                    Nothing ->
                                        case List.head <| List.filter (\( _, ( _, ti ) ) -> ti.t == D && ti.u /= 0) <| Dict.toList nodes of
                                            Just ( i, ( _, ti ) ) ->
                                                let
                                                    c =
                                                        generateNewConst 1 m

                                                    ( v, g ) =
                                                        Maybe.withDefault ( ( "", [], 0 ), Insat ) <| ffolCuantifiedComponents ti.f
                                                in
                                                let
                                                    new_nodes =
                                                        Dict.insert nid ( 0, { f = FOL_SS.ffolApplySubstitution (Dict.singleton v c) g, t = ffolType g, u = uMax, ut = [], i = nid2, ps = [ i ], ant = nidp } ) <|
                                                            Dict.insert i ( 0, { ti | u = 0 } ) nodes

                                                    new_edges =
                                                        Dict.insert ( nidp, nid ) (Just { r = D, is = [ i ], br = 1, s = Dict.singleton v c }) edges
                                                in
                                                semanticTableauAux (m ++ [ c ]) dMax uMax (nid + 1) (nid2 + 1) nid (dcur + 1) new_nodes new_edges

                                            Nothing ->
                                                case List.head <| List.sortBy (\( _, ( _, ti ) ) -> uMax - ti.u) <| List.filter (\( _, ( _, ti ) ) -> ti.t == G && ti.u /= 0) <| Dict.toList nodes of
                                                    Just ( i, ( _, ti ) ) ->
                                                        let
                                                            occurs =
                                                                List.map (\( v, lv ) -> ( v, 1 + List.length lv )) <| LE.gatherEquals <| List.concat <| List.map (\( _, ti2 ) -> FOL_SS.ffolAllClosedTerms ti2.f) <| List.filter (\( _, ti2 ) -> ti2.t == L || ti2.t == E) <| Dict.values nodes
                                                        in
                                                        let
                                                            tsus =
                                                                Maybe.withDefault (generateNewConst 1 m) <| LE.maximumBy (\x -> Maybe.withDefault 0 <| List.head <| List.map Tuple.second <| List.filter (\( y, _ ) -> y == x) occurs) <| List.filter (\x -> not (List.member x ti.ut)) m

                                                            ( v, g ) =
                                                                Maybe.withDefault ( ( "", [], 0 ), Insat ) <| ffolCuantifiedComponents ti.f
                                                        in
                                                        let
                                                            new_m =
                                                                uniqueConcatList m [ tsus ]

                                                            new_nodes =
                                                                Dict.insert nid ( 0, { f = FOL_SS.ffolApplySubstitution (Dict.singleton v tsus) g, t = ffolType g, u = uMax, ut = [], i = nid2, ps = [ i ], ant = nidp } ) <|
                                                                    Dict.insert i ( 0, { ti | ut = tsus :: ti.ut, u = ti.u - 1 } ) nodes

                                                            new_edges =
                                                                Dict.insert ( nidp, nid ) (Just { r = G, is = [ ti.i ], br = 1, s = Dict.singleton v tsus }) edges
                                                        in
                                                        semanticTableauAux new_m dMax uMax (nid + 1) (nid2 + 1) nid (dcur + 1) new_nodes new_edges

                                                    Nothing ->
                                                        let
                                                            g =
                                                                Maybe.withDefault Insat <| Maybe.map (\x -> (Tuple.second x).f) <| Dict.get nidp nodes
                                                        in
                                                        ( Dict.insert nid ( 1, { f = g, t = I, u = uMax, ut = [], i = nid2, ps = [], ant = nidp } ) nodes
                                                        , Dict.insert ( nidp, nid ) Nothing edges
                                                        )


{-| It check if a tableau has all his branches closed
-}
semanticTableauIsInsat : FOLSemanticTableau -> Bool
semanticTableauIsInsat t =
    not <| List.any (\x -> Tuple.first x.label == 1) <| Graph.nodes t


{-| It allows to represent a FOL Semantic Tableau as a string
-}
semanticTableauToString : FOLSemanticTableau -> String
semanticTableauToString t =
    let
        toStringNode =
            \( i, ti ) ->
                Just <|
                    if i == -1 then
                        "X"

                    else if i == 1 then
                        "◯"

                    else
                        "F" ++ (replaceBySubscript <| String.fromInt (ti.i + 1)) ++ "≡" ++ FOL_SS.ffolToString ti.f

        toStringEdge =
            \ei ->
                case ei.r of
                    L ->
                        "L"

                    E ->
                        "E"

                    DN ->
                        "dN(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")"

                    A ->
                        "α" ++ (replaceBySubscript <| String.fromInt ei.br) ++ "(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")"

                    B ->
                        "β" ++ (replaceBySubscript <| String.fromInt ei.br) ++ "(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")"

                    G ->
                        "γ(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ "," ++ FOL_SS.substitutionToString ei.s ++ ")"

                    D ->
                        "δ(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")⇒" ++ FOL_SS.substitutionToString ei.s

                    I ->
                        "⟂(" ++ (String.join "," <| List.map (\ind -> "F" ++ (replaceBySubscript <| String.fromInt (ind + 1))) ei.is) ++ ")"

                    T ->
                        "T"
    in
    Graph.toString toStringNode (Maybe.map toStringEdge) <| t


{-| It allows to represent a FOL Semantic Tableau as a DOT String rederable by GraphViz
-}
semanticTableauToDOT : FOLSemanticTableau -> String
semanticTableauToDOT t =
    let
        toStringNode =
            \( i, ti ) ->
                Just <|
                    if i == -1 then
                        "🗴"

                    else if i == 1 then
                        "⭘"

                    else
                        "F" ++ (replaceBySubscript <| String.fromInt (ti.i + 1)) ++ "≡" ++ FOL_SS.ffolToString ti.f

        toStringEdge =
            \ei ->
                case ei.r of
                    L ->
                        "L"

                    E ->
                        "E"

                    DN ->
                        "dN(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")"

                    A ->
                        "α" ++ (replaceBySubscript <| String.fromInt ei.br) ++ "(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")"

                    B ->
                        "β" ++ (replaceBySubscript <| String.fromInt ei.br) ++ "(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")"

                    G ->
                        "γ(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ "," ++ FOL_SS.substitutionToString ei.s ++ ")"

                    D ->
                        "δ(F" ++ (replaceBySubscript <| String.join "," <| List.map (\ind -> String.fromInt <| ind + 1) ei.is) ++ ")⇒" ++ FOL_SS.substitutionToString ei.s

                    I ->
                        "⟂(" ++ (String.join "," <| List.map (\ind -> "F" ++ (replaceBySubscript <| String.fromInt (ind + 1))) ei.is) ++ ")"

                    T ->
                        "T"

        myStyles =
            { defaultStyles | node = "shape=box, color=white, fontcolor=black", edge = "dir=none, color=blue, fontcolor=blue" }
    in
    String.replace "\n" "" <| String.replace "\"" ">" <| String.replace "=\"" "=<" <| Graph.DOT.outputWithStyles myStyles toStringNode (Maybe.map toStringEdge) <| t



-- -- AuxiliarMethods for removing nodes that are irrelevant in the search process


recoverClosedPathNodes : Int -> Dict Int ( Int, TableauNodeItem ) -> List ( Int, ( Int, TableauNodeItem ) )
recoverClosedPathNodes i dictNodes =
    case Dict.get i dictNodes of
        Just ( tn, tni ) ->
            uniqueConcatList [ ( i, ( tn, tni ) ) ] <| List.concat <| List.map (\xi -> recoverClosedPathNodes xi dictNodes) tni.ps

        Nothing ->
            []


{-| It Removes the Useless Nodes In Insatisfiable tableau, that are the nodes that don't participates in the way to lograte the insatifiability.
-}
semanticTableauRUNII : FOLSemanticTableau -> FOLSemanticTableau
semanticTableauRUNII t =
    let
        dictNodes =
            Dict.fromList <| List.map (\x -> ( x.id, x.label )) <| List.sortBy .id <| Graph.nodes t

        edges =
            Graph.edges t

        nodesInsat =
            List.filter (\x -> Tuple.first x.label == -1) <| Graph.nodes t
    in
    let
        finalNodes =
            uniqueConcatList [] <| List.concat <| List.map (\x -> recoverClosedPathNodes x.id dictNodes) nodesInsat
    in
    let
        finalNodesInd =
            List.map Tuple.first <| finalNodes
    in
    let
        ( dic_ant, final_edges ) =
            List.foldl
                (\x ( d_ant, n_e ) ->
                    if List.member x.id finalNodesInd then
                        ( Dict.insert x.id x.id d_ant, n_e )

                    else
                        let
                            ant =
                                Maybe.withDefault 0 <| Dict.get (Tuple.second x.label).ant d_ant
                        in
                        ( Dict.insert x.id ant d_ant
                        , List.map
                            (\e ->
                                if e.from == x.id then
                                    Edge ant e.to e.label

                                else
                                    e
                            )
                          <|
                            List.filter (\e -> e.to /= x.id) n_e
                        )
                )
                ( Dict.empty, edges )
                (Graph.nodes t)
    in
    Graph.fromNodesAndEdges (List.map (\( i, ( tn, l ) ) -> Node i ( tn, { l | ant = Maybe.withDefault 0 <| Dict.get i dic_ant } )) finalNodes) final_edges
