module LogicUS.FOL.Resolution exposing
    ( Resolvent, cfol2SeparationSubst, cfol2Separation, cfol2ContraryLiterals
    , ResolutionTableau, csfolSCFResolution, csfolSCFLinearResolution, csplSCFPositiveResolution, csplSCFNegativeResolution
    , resolutionTableauToString, resolutionTableauToDOT
    , cfol2AllResolvents
    )

{-| The module provides the tools for aplying the differents resolution strategies to a set of propositional clauses for verifying its unfeasibility.


# Resolvents

@docs Resolvent, cfol2SeparationSubst, cfol2Separation, cfol2ContraryLiterals, cfol2AllResolvents.


# Refutationally Resolution Tableau Algorithm and Strategies

@docs ResolutionTableau, csfolSCFResolution, csfolSCFLinearResolution, csplSCFPositiveResolution, csplSCFNegativeResolution


# Resolution Tableau Representation

@docs resolutionTableauToString, resolutionTableauToDOT

-}

import Dict exposing (Dict)
import Graph exposing (Edge, Graph, Node)
import Graph.DOT as GDOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.FOL.AuxiliarFuctions exposing (uniqueConcatList)
import LogicUS.FOL.Clauses as FOL_CL exposing (ClauseFOL, ClauseFOLLiteral)
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (Substitution, Term(..))
import LogicUS.FOL.Unification as FOL_UN
import Set



-- Work functions


{-| It represent the information of the resolvent, the clauses involved, the renames done, the maximum general unifier (mgu) and the result of the resolvent
-}
type alias Resolvent =
    { c1 : ClauseFOL
    , c2 : ClauseFOL
    , r : Substitution
    , mgu : Substitution
    , res : ClauseFOL
    }


type alias ResolutionItem =
    { c : ClauseFOL
    , p1 : Int
    , p2 : Int
    , r : Substitution
    , mgu : Substitution
    }


{-| It represent the graph structure of the tableau
-}
type alias ResolutionTableau =
    Graph ( Bool, ClauseFOL ) ( Substitution, Substitution )


{-| It generates the appropriate substitutions for the separation of the clauses
-}
cfol2SeparationSubst : ClauseFOL -> ClauseFOL -> Substitution
cfol2SeparationSubst c1 c2 =
    let
        vs_r =
            Set.toList <|
                Set.filter (\x -> Set.member x <| FOL_CL.cfolVarSymbols c1) (FOL_CL.cfolVarSymbols c2)

        vs_c =
            Set.union
                (FOL_CL.cfolVarSymbols c1)
                (FOL_CL.cfolVarSymbols c2)
    in
    let
        getIndex s is i =
            if Set.member ( s, is, i ) vs_c then
                getIndex s is (i + 1)

            else
                i
    in
    let
        subs =
            Dict.fromList <| List.map (\( s, is, i ) -> ( ( s, is, i ), Var ( s, is, getIndex s is 0 ) )) vs_r
    in
    subs


{-| It generates the appropriate substitutions for the separation of the clauses
-}
cfol2Separation : ClauseFOL -> ClauseFOL -> ( ClauseFOL, ClauseFOL )
cfol2Separation c1 c2 =
    let
        s =
            cfol2SeparationSubst c1 c2
    in
    ( c1, FOL_CL.cfolApplySubstitution s c2 )


{-| It searches all the pairs of literals from two clauses that have the same predicate and contrary sign
-}
cfol2ContraryLiterals : ClauseFOL -> ClauseFOL -> List ( ClauseFOLLiteral, ClauseFOLLiteral )
cfol2ContraryLiterals c1 c2 =
    let
        searchContraryLiteral ( a, sign ) c =
            List.filter (\( a_, sign_ ) -> FOL_CL.cfolAtomSymbol a == FOL_CL.cfolAtomSymbol a_ && sign /= sign_) c
    in
    List.foldl (\( a, sign ) ac -> ac ++ (List.map (\l -> ( ( a, sign ), l )) <| searchContraryLiteral ( a, sign ) c2)) [] c1


{-| It searches all the pairs of literals from two clauses that have the same predicate and contrary sign
-}
cfol2AllResolvents : ClauseFOL -> ClauseFOL -> List Resolvent
cfol2AllResolvents c1 c2 =
    let
        r =
            cfol2SeparationSubst c1 c2

        c2_ =
            FOL_CL.cfolApplySubstitution r c2
    in
    let
        cls =
            cfol2ContraryLiterals c1 c2_
    in
    List.foldl
        (\( ( a1, sg1 ), ( a2, sg2 ) ) ac ->
            case FOL_UN.atomsMGU (FOL_CL.clauseFOLAtomToAtom a1) (FOL_CL.clauseFOLAtomToAtom a2) of
                Just mgu ->
                    let
                        c1__ =
                            List.filter (\x -> x /= ( FOL_CL.cfolAtomApplySubstitution mgu a1, sg1 )) <| FOL_CL.cfolApplySubstitution mgu c1

                        c2__ =
                            List.filter (\x -> x /= ( FOL_CL.cfolAtomApplySubstitution mgu a2, sg2 )) <| FOL_CL.cfolApplySubstitution mgu c2_
                    in
                    ac ++ [ { c1 = c1, c2 = c2, r = r, mgu = mgu, res = FOL_CL.cfolUnion c1__ c2__ } ]

                Nothing ->
                    ac
        )
        []
        cls


recoverResolutionPath : Int -> Dict Int ResolutionItem -> ( List (Node ClauseFOL), List (Edge ( Substitution, Substitution )) )
recoverResolutionPath i refDict =
    case Dict.get i refDict of
        Just ri ->
            let
                ( nodes1, edges1 ) =
                    recoverResolutionPath ri.p1 refDict

                ( nodes2, edges2 ) =
                    recoverResolutionPath ri.p2 refDict
            in
            ( uniqueConcatList nodes1 nodes2 ++ [ Node i ri.c ]
            , uniqueConcatList edges1 edges2
                ++ [ Edge ri.p1 i ( Dict.empty, Dict.filter (\k _ -> Set.member k (FOL_CL.cfolVarSymbols <| Maybe.withDefault [] <| Maybe.map .c <| Dict.get ri.p1 refDict)) ri.mgu )
                   , Edge ri.p2 i ( ri.r, Dict.filter (\k _ -> Set.member k (FOL_CL.cfolVarSymbols <| Maybe.withDefault [] <| Maybe.map .c <| Dict.get ri.p2 refDict)) ri.mgu )
                   ]
            )

        _ ->
            ( [], [] )


resolventsWithClosedSCFResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithClosedSCFResolutionAux closed id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) closed then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents ri.c c)
        )
        []
        closed


openedUpdationSCFResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( lx, _ ) -> lx <= li) rest
                    in
                    if List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.filter (\( _, x ) -> not (FOL_CL.cfolSubsumes ri.c x.c)) <| List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


csfolSCFResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClauseFOL), List (Edge ( Substitution, Substitution )) )
csfolSCFResolutionAux closed opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( _, ri ) :: xs ->
            if List.isEmpty ri.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ [ ( nid + 1, ri ) ]
                in
                recoverResolutionPath (nid + 1) refDict

            else
                let
                    r_closed =
                        resolventsWithClosedSCFResolutionAux closed (nid + 1) ri.c
                in
                let
                    new_closed =
                        closed ++ [ ( nid + 1, ri ) ]

                    new_opened =
                        openedUpdationSCFResolutionAux xs (List.sortBy (\x -> Tuple.first x) <| List.map (\x -> ( List.length x.c, x )) r_closed)
                in
                csfolSCFResolutionAux new_closed new_opened (nid + 1)


{-| It uses resolution algorithm using shorted clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOt_ as we show in the example above.

-}
csfolSCFResolution : List ClauseFOL -> ( Bool, ResolutionTableau )
csfolSCFResolution clauses =
    let
        cs =
            FOL_CL.csfolRemoveEqClauses clauses
    in
    let
        new_cs =
            List.sortBy (\x -> Tuple.first x) <| List.map (\x -> ( List.length x, { c = x, p1 = 0, p2 = 0, r = Dict.empty, mgu = Dict.empty } )) <| FOL_CL.csfolRemoveSubsumedClauses <| FOL_CL.csfolRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csfolSCFResolutionAux [] new_cs 0
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--=======================
--== LINEAR RESOLUTION ==
--=======================


filterSubsumedResolutionItems : List ResolutionItem -> List ResolutionItem
filterSubsumedResolutionItems xs =
    List.foldl
        (\x ac ->
            if List.any (\y -> FOL_CL.cfolSubsumes y.c x.c) ac then
                ac

            else
                ac ++ [ x ]
        )
        []
        (List.sortBy (\x -> List.length x.c) xs)



-- It calculates the resolvents with closed clauses


resolventsWithClosedSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithClosedSCFLinearResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) closed then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents c ri.c)
        )
        []
        (List.filter (\( i, _ ) -> not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone) <| closed)



-- It calculates the resolvents with opened clauses


resolventsWithOpenedSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithOpenedSCFLinearResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) opened then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents c ri.c)
        )
        []
        opened



-- It performs the linear resolution algorithm with SCF heuristic


csplSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClauseFOL), List (Edge ( Substitution, Substitution )) )
csplSCFLinearResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        filterSubsumedResolutionItems <|
                            List.sortBy (\x -> List.length x.c) <|
                                resolventsWithClosedSCFLinearResolutionAux closed resDone id rid.c
                                    ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFLinearResolutionAux xs id rid.c)
                in
                let
                    newClosed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first <| closed ++ xs) <| Dict.map (\_ v -> v ++ [ id ]) resDone
                in
                Maybe.withDefault ( [], [] ) <|
                    List.head <|
                        List.filter
                            (not << List.isEmpty << Tuple.first)
                        <|
                            List.map
                                (\ri -> csplSCFLinearResolutionAux newClosed newResDone (( nid + 1, ri ) :: xs) (nid + 1))
                                resolvents_i


{-| It uses linear resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:Sat) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csfolSCFLinearResolution : List ClauseFOL -> ( Bool, ResolutionTableau )
csfolSCFLinearResolution clauses =
    let
        cs =
            FOL_CL.csfolRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, r = Dict.empty, mgu = Dict.empty } )) <| List.sortBy (\x -> List.length x) <| FOL_CL.csfolRemoveSubsumedClauses <| FOL_CL.csfolRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFLinearResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    -- ( nodes, edges )
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



-- POSITIVE RESOLUTION


openedUpdationSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFPositiveResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithClosedSCFPositiveResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) closed then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents c ri.c)
        )
        []
        (List.filter (\( i, ri ) -> (FOL_CL.cfolIsPositive c || FOL_CL.cfolIsPositive ri.c) && (not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone)) <| closed)


resolventsWithOpenedSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithOpenedSCFPositiveResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) opened then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents c ri.c)
        )
        []
        (List.filter (\( _, ri ) -> FOL_CL.cfolIsPositive c || FOL_CL.cfolIsPositive ri.c) <| opened)


csplSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClauseFOL), List (Edge ( Substitution, Substitution )) )
csplSCFPositiveResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFPositiveResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFPositiveResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFPositiveResolutionAux xs resolvents_i
                in
                csplSCFPositiveResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses positive resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFPositiveResolution : List ClauseFOL -> ( Bool, ResolutionTableau )
csplSCFPositiveResolution clauses =
    let
        cs =
            FOL_CL.csfolRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, r = Dict.empty, mgu = Dict.empty } )) <| List.sortBy (\x -> List.length x) <| FOL_CL.csfolRemoveSubsumedClauses <| FOL_CL.csfolRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFPositiveResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



-- NEGATIVE RESOLUTION


openedUpdationSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFNegativeResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithClosedSCFNegativeResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) closed then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents c ri.c)
        )
        []
        (List.filter (\( i, ri ) -> (FOL_CL.cfolIsNegative c || FOL_CL.cfolIsNegative ri.c) && (not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone)) <| closed)


resolventsWithOpenedSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClauseFOL -> List ResolutionItem
resolventsWithOpenedSCFNegativeResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\r ac2 ->
                    if not <| FOL_CL.cfolIsTautology r.res || List.any (\x -> FOL_CL.cfolSubsumes x.c r.res) ac || List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c r.res) opened then
                        { c = r.res, p1 = id, p2 = i, r = r.r, mgu = r.mgu } :: List.filter (\x -> not <| FOL_CL.cfolSubsumes r.res x.c) ac2

                    else
                        ac2
                )
                ac
                (cfol2AllResolvents c ri.c)
        )
        []
        (List.filter (\( _, ri ) -> FOL_CL.cfolIsNegative c || FOL_CL.cfolIsNegative ri.c) <| opened)


csplSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClauseFOL), List (Edge ( Substitution, Substitution )) )
csplSCFNegativeResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFNegativeResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> FOL_CL.cfolSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFNegativeResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFNegativeResolutionAux xs resolvents_i
                in
                csplSCFNegativeResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses negative resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFNegativeResolution : List ClauseFOL -> ( Bool, ResolutionTableau )
csplSCFNegativeResolution clauses =
    let
        cs =
            FOL_CL.csfolRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, r = Dict.empty, mgu = Dict.empty } )) <| List.sortBy (\x -> List.length x) <| FOL_CL.csfolRemoveSubsumedClauses <| FOL_CL.csfolRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFNegativeResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



-------------------------------------------------------------------------------------------------------------------------


{-| Express a Resolution Tableau as a string.
-}
resolutionTableauToString : ResolutionTableau -> String
resolutionTableauToString g =
    let
        toStringNode =
            \( _, cs ) -> Just <| FOL_CL.cfolToString cs

        toStringEdge =
            \( rn, mgu ) ->
                if Dict.isEmpty rn then
                    Just <| FOL_SS.substitutionToString mgu

                else
                    Just <| FOL_SS.substitutionToString rn ++ "\n" ++ FOL_SS.substitutionToString mgu
    in
    Graph.toString toStringNode toStringEdge g


{-| Express a Resolution Tableau as a string in DOT format that is viewable with a GraphViz Render.
**Note:** If you are using elm repl, before introducing the code you must replace _\\n_ by _\\n_ and _\\"_ by _"_ in a simple text editor.
-}
resolutionTableauToDOT : ResolutionTableau -> String
resolutionTableauToDOT g =
    let
        toStringNode =
            \( _, cs ) -> Just <| FOL_CL.cfolToString cs

        toStringEdge =
            \( rn, mgu ) ->
                if Dict.isEmpty rn && Dict.isEmpty mgu then
                    Nothing

                else if Dict.isEmpty rn then
                    Just <| FOL_SS.substitutionToString mgu

                else if Dict.isEmpty mgu then
                    Just <| FOL_SS.substitutionToString rn

                else
                    Just <| FOL_SS.substitutionToString rn ++ "<BR/>" ++ FOL_SS.substitutionToString mgu

        initialNodes =
            String.join ";" <|
                List.map String.fromInt <|
                    List.foldl
                        (\x ac ->
                            if Tuple.first x.label then
                                ac ++ [ x.id ]

                            else
                                ac
                        )
                        []
                        (Graph.nodes g)
    in
    String.replace "\n" "" <| String.replace "\n}" ("\n\n  {rank=same; " ++ initialNodes ++ ";}\n}") <| GDOT.output toStringNode toStringEdge g
