module LogicUS.FOL.SemanticTableauxEQ exposing
    ( SmullyanFOLType, STEQRule, FOLSemanticTableau, STEQNode
    , ffolType
    , semanticTableauEq
    , semanticTableauToString, semanticTableauToDOT, semanticTableauToJSON
    )

{-| The module provides the elementary tools for building the semantic tableau of a set of FOLEQ formulas.


# Definition Types

@docs SmullyanFOLType, STEQRule, FOLSemanticTableau, STEQNode


# Formulas types and components

@docs ffolType


# Semantic Tableau Algorithm

@docs semanticTableauEq


# Fuctions for representation

@docs semanticTableauToString, semanticTableauToDOT, semanticTableauToJSON

-}

import Dict exposing (Dict)
import Graph.Tree as GTree exposing (Tree)
import Json.Encode as JSONE exposing (Value)
import List.Extra as LE
import LogicUS.AUX.AuxiliarFuctions exposing (listRemoveAll)
import LogicUS.FOL.Clauses exposing (ClauseFOLAtom(..))
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), Ident, SetFOL, Term(..), Variable, termClosedTerms, termToString, termsClosedTerms)
import Maybe.Extra as ME


{-| The Smullyan Uniform Notation for First Order formulas with equality
-}
type SmullyanFOLType
    = L -- Positive Literal
    | E -- Equality
    | NE -- Negation of Equality
    | DN -- Double Negation
    | A -- Alpha
    | B -- Beta
    | G -- Gamma (Universal)
    | D -- Delta (Existencial)
    | I -- Inconsistece
    | T -- Tautology


{-| The expansion rules (according to Smullyan Uniform Notation) and others for indicating initial formulas and unexplored branches.
-}
type STEQRule
    = AR -- Alpha
    | BR -- Beta
    | GR -- Gamma (Universal)
    | DR -- Delta (Existencial)
    | IR -- Inconsistece
    | OL -- Opened
    | LL -- Leibniz Law
    | IF -- Initial formula
    | UE -- Unexplored


{-| The structure that represents a tableau, that is, a Tree of STEQNode
-}
type alias FOLSemanticTableau =
    Tree STEQNode


{-| The structure that represents a node of a tableau. It contains the information of the index of the node, its formula, the indices of nodes from it is derived, the substitution made (if it is derives from universal or existential formula), the simplifications made (with respect to equalities) and the expansion rule involved in the derivation
-}
type alias STEQNode =
    { i : Int, f : FormulaFOL, simp : List Int, p1 : Maybe ( Int, List Int ), p2 : Maybe ( Int, List Int ), subs : Maybe ( Variable, Term ), r : STEQRule }



-- The structure that represents a tableau (but not final)


type alias FOLSemanticTableauAUX =
    Tree STEQNodeAUX



{- Defines the STEQNodeAUX that is a record with the following features:

   - 'f' : the formula considered,
   - 't' : the type of the formula.
   - 'u' : the usability degree of the formula. (Used for universal formulas)
   - 'ut' : a list of terms which a gamma formula has been already substituted with .
   - 'i' : the index of the tree node.
   - 'p1' : the first/unique premise from which the formula is concluded, including substitutions.
   - 'p2' : the possible second premise from which the formula is concluded, including substitutions.

-}


type alias STEQNodeAUX =
    { f : FormulaFOL
    , simp : List Int
    , t : SmullyanFOLType
    , u : Int
    , ut : List Term
    , i : Int
    , p1 : Maybe ( Int, List Int )
    , p2 : Maybe ( Int, List Int )
    , subs : Maybe ( Variable, Term )
    , r : STEQRule
    }



-- Establishes a total order relation over the ground terms in FOL.


termVarCount : Term -> Int
termVarCount t =
    case t of
        Var _ ->
            1

        Func _ ts ->
            List.sum <| List.map termVarCount ts


termConstCount : Term -> Int
termConstCount t =
    case t of
        Var _ ->
            0

        Func _ [] ->
            1

        Func _ ts ->
            List.sum <| List.map termConstCount ts


termFuncCount : Term -> Int
termFuncCount t =
    case t of
        Var _ ->
            0

        Func _ [] ->
            0

        Func _ ts ->
            1 + (List.sum <| List.map termFuncCount ts)


compareTerms : Term -> Term -> Order
compareTerms t1 t2 =
    let
        t1V =
            termVarCount t1

        t2V =
            termVarCount t2

        t1C =
            termConstCount t1

        t2C =
            termConstCount t2

        t1F =
            termFuncCount t1

        t2F =
            termFuncCount t2
    in
    if t1V < t2V || (t1V == t2V && t1C < t2C) || (t1V == t2V && t1C == t2C && t1F < t2F) then
        LT

    else if t1V == t2V && t1C == t2C && t1F == t2F then
        compare (termToString t1) (termToString t2)

    else
        GT



-- Establishes a priority order in the analysis of equalities.


compareEqualities : ( Term, Term ) -> ( Term, Term ) -> Order
compareEqualities ( t11, t12 ) ( t21, t22 ) =
    if t11 == t21 then
        compareTerms t12 t22

    else if List.member t11 (termClosedTerms t21 ++ termClosedTerms t22) then
        LT

    else if List.member t21 (termClosedTerms t11 ++ termClosedTerms t12) then
        GT

    else
        compareTerms t11 t21


{-| It gives the class of a FOLEQ formula (according to Smullyan Uniform Notation). Atoms (predicates) and their negations are literals, double negation are typed as DN, conjunction, equivalence are classified as ALPHA, disjunction and implications are classified as BETA. forall-like formulas are classified as GAMMA and existencial-like ones as DELTA The negation of an alpha formula is a beta and vice versa, and the same happens with forall and exists like ones.
-}
ffolType : FormulaFOL -> SmullyanFOLType
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

        Neg (Equal _ _) ->
            NE

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



-- The structure that stores each goal during the tableau performing


type alias Goal =
    { subgoals : List ( Term, Term ), substitutions : ( List Int, List Int ) }



-- It gives if in the nodes of the esplored branch is there any contradiction. If it is discovered, it return the list of formulas implied in it


checkGoals :
    Dict ( Int, Int ) Goal
    -> Maybe { f1 : Int, f2 : Int, substitutions : ( List Int, List Int ) }
checkGoals goals =
    case Dict.toList goals |> List.filter (\e -> List.isEmpty <| (Tuple.second e).subgoals) of
        x :: _ ->
            Just { f1 = (Tuple.first << Tuple.first) x, f2 = (Tuple.second << Tuple.first) x, substitutions = (Tuple.second x).substitutions }

        _ ->
            Nothing


{-| It allows construct the Semantic Tableau of a set of formulas. It recieves two additional parameters that corresponds to the maximum generated constants and the maximum size of terms allowed, respectively.
-}
semanticTableauEq :
    SetFOL
    -> Int
    -> Int
    -- -> Int
    -> FOLSemanticTableau
semanticTableauEq fs maxConstants maxSize =
    --maxDepth =
    let
        generateNodeAuxFromF =
            \i f -> ( i, { f = f, simp = [], t = ffolType f, u = 0, ut = [], i = i, p1 = Nothing, p2 = Nothing, subs = Nothing, r = IF } )
    in
    let
        nodes =
            Dict.fromList <| List.indexedMap generateNodeAuxFromF <| List.map (reduceDN << FOL_SS.ffolUniversalClausure) fs

        universe =
            []
    in
    let
        tableau =
            Tuple.first <| semanticTableauEqAux (Dict.size nodes) 0 maxConstants maxSize universe nodes Dict.empty Dict.empty
    in
    let
        newTableau =
            Tuple.second <|
                List.foldr
                    (\f ( i, t ) ->
                        ( i - 1
                        , GTree.inner
                            (Tuple.second <| generateNodeAuxFromF i f)
                            [ t ]
                        )
                    )
                    ( List.length fs - 1, tableau )
                    fs
    in
    -- let
    --     view =
    --         Debug.log "T" <| semanticTableauToString tableau
    -- in
    Maybe.withDefault GTree.empty <| List.head <| postProcessingSTEQ 1 Dict.empty newTableau



-- It calculates the size of a ground term.


groundTermSize : Term -> Maybe Int
groundTermSize t =
    case t of
        Var _ ->
            Nothing

        Func _ ts ->
            let
                tsSizes =
                    List.map groundTermSize ts
            in
            if List.member Nothing tsSizes then
                Nothing

            else
                Just <| 1 + (Maybe.withDefault 0 <| List.maximum <| ME.values tsSizes)



-- This is the main procedure in the tableau building.


semanticTableauEqAux :
    Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -- -> Int
    -> ( FOLSemanticTableauAUX, List Int )
semanticTableauEqAux deep generatedConstants maxConstants maxSize universein nodesin equalities goals =
    let
        nodes =
            Dict.fromList <|
                List.foldl
                    (\( i, ni ) ac ->
                        if List.any (\( _, nj ) -> nj.f == ni.f) ac then
                            ac

                        else
                            ac ++ [ ( i, ni ) ]
                    )
                    []
                <|
                    List.sortBy Tuple.first <|
                        Dict.toList nodesin

        universe =
            List.filter (\t -> (Maybe.withDefault (maxSize + 1) <| groundTermSize t) <= maxSize) universein

        -- maxDepth = 30
        -- viewUniverse =
        --     Debug.log "U:" universe
        -- viewNodes =
        --     Debug.log "N:" nodes
        -- viewEqualities =
        --     Debug.log "E:" equalities
        -- viewGoals =
        --     Debug.log "G:" goals
    in
    -- if deep > maxDepth then
    --     let
    --         viewLeaf1 =
    --             Debug.log "paso"
    --     in
    --     ( GTree.leaf
    --         { f = FOL_SS.Taut
    --         , simp = []
    --         , t = T
    --         , subs = Nothing
    --         , u = 0
    --         , ut = []
    --         , i = deep
    --         , r = OL
    --         , p1 = Nothing
    --         , p2 = Nothing
    --         }
    --     , []
    --     )
    -- else
    case checkGoals goals of
        Just inconsistence ->
            closeBranch inconsistence deep nodes

        Nothing ->
            case
                chooseEquality nodes
            of
                Just ( i, ni ) ->
                    -- let
                    --     viewProcessed =
                    --         Debug.log "EQ" ( i, ni )
                    -- in
                    processEquality ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                -- maxDepth
                Nothing ->
                    case chooseInequality nodes of
                        Just ( i, ni ) ->
                            -- let
                            --     viewProcessed =
                            --         Debug.log "NE" ( i, ni )
                            -- in
                            processInequality ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                        Nothing ->
                            case chooseLiteral nodes of
                                Just ( i, ni ) ->
                                    -- let
                                    --     viewProcessed =
                                    --         Debug.log "L" ( i, ni )
                                    -- in
                                    processLiteral ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                                Nothing ->
                                    case chooseAlpha nodes of
                                        Just ( i, ni ) ->
                                            -- let
                                            --     viewProcessed =
                                            --         Debug.log "A" ( i, ni )
                                            -- in
                                            processAlpha ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                                        Nothing ->
                                            case chooseBeta nodes of
                                                Just ( i, ni ) ->
                                                    -- let
                                                    --     viewProcessed =
                                                    --         Debug.log "B" ( i, ni )
                                                    -- in
                                                    processBeta ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                                                Nothing ->
                                                    case ( generatedConstants < maxConstants, chooseDelta nodes ) of
                                                        ( True, Just ( i, ni ) ) ->
                                                            -- let
                                                            --     viewProcessed =
                                                            --         Debug.log "D" ( i, ni )
                                                            -- in
                                                            processDelta ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                                                        _ ->
                                                            let
                                                                universe_ =
                                                                    if List.isEmpty universe then
                                                                        [ Func ( "κ", [ generatedConstants ] ) [] ]

                                                                    else
                                                                        universe
                                                            in
                                                            case chooseGamma universe_ nodes of
                                                                Just ( i, ni, t :: _ ) ->
                                                                    -- let
                                                                    --     viewProcessed =
                                                                    --         Debug.log "G" ( i, ni, t )
                                                                    -- in
                                                                    processGamma ( i, ni, t ) deep generatedConstants maxConstants maxSize universe nodes equalities goals

                                                                _ ->
                                                                    ( GTree.leaf
                                                                        { f = FOL_SS.Taut
                                                                        , simp = []
                                                                        , t = T
                                                                        , subs = Nothing
                                                                        , u = 0
                                                                        , ut = []
                                                                        , i = deep
                                                                        , r = OL
                                                                        , p1 = Nothing
                                                                        , p2 = Nothing
                                                                        }
                                                                    , []
                                                                    )


recoverPathFromNode : Dict Int STEQNodeAUX -> Int -> List Int
recoverPathFromNode nodes final =
    case Dict.get final nodes of
        Just v ->
            (LE.unique <| List.concat <| List.map (recoverPathFromNode nodes) <| LE.unique <| v.simp ++ (List.map Tuple.first <| ME.values [ v.p1, v.p2 ])) ++ [ final ]

        Nothing ->
            []


simplifyTermWithEq : ( Term, Term ) -> Term -> ( Term, Bool )
simplifyTermWithEq ( lhs, rhs ) t =
    if t == lhs then
        ( rhs, True )

    else
        case t of
            Func f (t1 :: ts) ->
                (\( ts_, isSimp ) -> ( Func f ts_, isSimp )) <| simplifyTermsWithEq ( lhs, rhs ) (t1 :: ts)

            _ ->
                ( t, False )


simplifyTermsWithEq : ( Term, Term ) -> List Term -> ( List Term, Bool )
simplifyTermsWithEq eq ts =
    (\( xs, bools ) -> ( xs, List.any identity bools )) <| List.unzip <| List.map (simplifyTermWithEq eq) ts


simplifyTermsWithEqsAux : List ( Int, ( Term, Term ) ) -> List Term -> Maybe ( List Term, Int )
simplifyTermsWithEqsAux eqs ts =
    case eqs of
        ( id, eq ) :: xs ->
            case simplifyTermsWithEq eq ts of
                ( ts_, True ) ->
                    Just ( ts_, id )

                ( _, False ) ->
                    simplifyTermsWithEqsAux xs ts

        _ ->
            Nothing


simplifyTermsWithEqs : Dict Int ( Term, Term ) -> List Term -> List Int -> ( List Term, List Int )
simplifyTermsWithEqs eqs ts simps =
    case simplifyTermsWithEqsAux (Dict.toList eqs) ts of
        Just ( ts_, id ) ->
            simplifyTermsWithEqs eqs ts_ (id :: simps)

        Nothing ->
            ( ts, simps )


simplifyTermWithEqs : Dict Int ( Term, Term ) -> Term -> ( Term, List Int )
simplifyTermWithEqs eqs t =
    (\( ts_, simps ) -> ( Maybe.withDefault t <| List.head ts_, simps )) <| simplifyTermsWithEqs eqs [ t ] []


insertInUniverse : List Term -> Term -> List Term
insertInUniverse universe t =
    let
        ( lts, gts ) =
            List.partition (\e -> compareTerms e t == LT) universe
    in
    case Maybe.map (\e -> compareTerms e t == EQ) <| List.head gts of
        Just True ->
            universe

        _ ->
            lts ++ t :: gts


removeSubsumedGoals : Dict ( Int, Int ) Goal -> Dict ( Int, Int ) Goal
removeSubsumedGoals goals =
    let
        goalList =
            List.sortBy (\e -> List.length (Tuple.second e).subgoals) <| Dict.toList goals

        subsumesList =
            \l1 l2 -> List.all (\x -> List.member x l2) l1
    in
    Dict.fromList <|
        Tuple.first <|
            List.foldl
                (\e ( ac1, ac2 ) ->
                    let
                        xs =
                            (Tuple.second e).subgoals
                    in
                    if List.any (\ys -> subsumesList ys xs) ac2 then
                        ( ac1, ac2 )

                    else
                        ( ac1 ++ [ e ], ac2 ++ [ xs ] )
                )
                ( [], [] )
                goalList


extractEQNEQTerms : FormulaFOL -> Maybe ( Term, Term )
extractEQNEQTerms f =
    case f of
        Equal t1 t2 ->
            Just ( t1, t2 )

        Neg (Equal t1 t2) ->
            Just ( t1, t2 )

        _ ->
            Nothing


getAComponents : FormulaFOL -> Maybe ( FormulaFOL, FormulaFOL )
getAComponents f =
    case f of
        Conj g h ->
            Just ( g, h )

        Neg (Disj g h) ->
            Just ( FOL_SS.ffolNegation g, FOL_SS.ffolNegation h )

        Neg (Impl g h) ->
            Just ( g, FOL_SS.ffolNegation h )

        Equi g h ->
            Just ( Impl g h, Impl h g )

        _ ->
            Nothing


getBComponents : FormulaFOL -> Maybe ( FormulaFOL, FormulaFOL )
getBComponents f =
    case f of
        Neg (Conj g h) ->
            Just ( FOL_SS.ffolNegation g, FOL_SS.ffolNegation h )

        Disj g h ->
            Just ( g, h )

        Impl g h ->
            Just ( FOL_SS.ffolNegation g, h )

        Neg (Equi g h) ->
            Just ( FOL_SS.ffolNegation (Impl g h), FOL_SS.ffolNegation (Impl h g) )

        _ ->
            Nothing


getDGVarComponent : FormulaFOL -> Maybe ( Variable, FormulaFOL )
getDGVarComponent f =
    case f of
        Forall v g ->
            Just ( v, g )

        Exists v g ->
            Just ( v, g )

        Neg (Forall v g) ->
            Just ( v, FOL_SS.ffolNegation g )

        Neg (Exists v g) ->
            Just ( v, FOL_SS.ffolNegation g )

        _ ->
            Nothing


reduceDN : FormulaFOL -> FormulaFOL
reduceDN f =
    case f of
        Neg (Neg g) ->
            reduceDN g

        _ ->
            f



-- INCONSISTENCE HANDLING


closeBranch :
    { f1 : Int, f2 : Int, substitutions : ( List Int, List Int ) }
    -> Int
    -> Dict Int STEQNodeAUX
    -> ( FOLSemanticTableauAUX, List Int )
closeBranch inconsistence deep nodes =
    ( GTree.leaf
        { f = Insat
        , simp = []
        , t = I
        , subs = Nothing
        , u = 0
        , ut = []
        , i = deep
        , r = IR
        , p1 =
            Just
                ( inconsistence.f1
                , Tuple.first inconsistence.substitutions
                )
        , p2 =
            if inconsistence.f1 == inconsistence.f2 then
                Nothing

            else
                Just
                    ( inconsistence.f2
                    , Tuple.second inconsistence.substitutions
                    )
        }
    , LE.unique <|
        List.concat <|
            List.map (recoverPathFromNode nodes) <|
                LE.unique <|
                    [ inconsistence.f1, inconsistence.f2 ]
                        ++ Tuple.first inconsistence.substitutions
                        ++ Tuple.second inconsistence.substitutions
    )



-- EQUALITY HANDLING


chooseEquality : Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX )
chooseEquality nodes =
    List.head <|
        List.sortWith
            (\( _, x1 ) ( _, x2 ) ->
                compareEqualities
                    (Maybe.withDefault ( Var ( "Err", [], -1 ), Var ( "Err", [], -1 ) ) <| extractEQNEQTerms x1.f)
                    (Maybe.withDefault ( Var ( "Err", [], -1 ), Var ( "Err", [], -1 ) ) <| extractEQNEQTerms x2.f)
            )
        <|
            List.filter (\( _, x ) -> x.t == E && x.u == 0) <|
                Dict.toList nodes


simplifyEqualityWithEqs :
    ( Term, Term, List Int )
    -> Dict Int ( Term, Term )
    -> ( Term, Term, List Int )
simplifyEqualityWithEqs ( t1, t2, simp ) equalities =
    let
        ( ts_, subs ) =
            simplifyTermsWithEqs equalities [ t1, t2 ] simp
    in
    let
        ( t1_, t2_ ) =
            case ts_ of
                [ a, b ] ->
                    ( a, b )

                _ ->
                    --impossible
                    ( t1, t2 )
    in
    case compareTerms t1_ t2_ of
        LT ->
            ( t2_, t1_, subs )

        _ ->
            ( t1_, t2_, subs )


processEquality :
    ( Int, STEQNodeAUX )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processEquality ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    let
        ( lhs, rhs, subs ) =
            simplifyEqualityWithEqs ((\( t1, t2 ) -> ( t1, t2, ni.simp )) <| Maybe.withDefault ( Func ( "Err", [] ) [], Func ( "Err", [] ) [] ) <| extractEQNEQTerms ni.f) equalities
    in
    if lhs /= rhs then
        let
            ( remEqualities_, newEqualities_ ) =
                List.partition
                    (\( _, ( lj, rj ) ) ->
                        List.member lhs (termClosedTerms lj)
                            || List.member lhs (termClosedTerms rj)
                    )
                    (Dict.toList equalities)
        in
        let
            newEqualities =
                newEqualities_ ++ [ ( i, ( lhs, rhs ) ) ]
        in
        let
            remEqualities =
                List.map (\( j, ( t1, t2 ) ) -> ( j, simplifyEqualityWithEqs ( t1, t2, [] ) (Dict.fromList newEqualities) )) remEqualities_
        in
        let
            nodesRemEqs =
                List.indexedMap
                    (\k ( j, ( lj, rj, s ) ) ->
                        ( deep + k, { f = Equal lj rj, simp = s, t = E, u = 0, ut = [], i = deep + k, p1 = Just ( j, [] ), p2 = Nothing, subs = Nothing, r = LL } )
                    )
                    remEqualities

            newUniverse =
                updateUniverseWithEqs (universe ++ termsClosedTerms [ lhs, rhs ]) (Dict.fromList newEqualities)

            newGoals =
                updateGoalsWithEqs goals (Dict.fromList newEqualities)
        in
        let
            relabelNi =
                { ni | f = Equal lhs rhs, simp = subs, u = 1 }

            nodesUpdateGut =
                Dict.map
                    (\_ nj ->
                        if nj.t == G then
                            { nj | ut = updateUniverseWithEqs nj.ut (Dict.fromList newEqualities) }

                        else
                            nj
                    )
                    nodes
        in
        let
            newNodes =
                Dict.union
                    (Dict.insert i relabelNi nodesUpdateGut)
                    (Dict.fromList nodesRemEqs)
        in
        let
            ( subtree, inconsPath ) =
                semanticTableauEqAux (deep + List.length nodesRemEqs) generatedConstants maxConstants maxSize newUniverse newNodes (Dict.fromList newEqualities) newGoals
        in
        if List.member i inconsPath || inconsPath == [] then
            ( GTree.inner relabelNi [ subtree ], inconsPath )

        else
            ( subtree, inconsPath )

    else
        let
            newNodes =
                Dict.remove i nodes
        in
        semanticTableauEqAux deep generatedConstants maxConstants maxSize universe newNodes equalities goals



-- INEQUALITY HANDLING


chooseInequality : Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX )
chooseInequality nodes =
    List.head <|
        List.filter (\( _, x ) -> x.t == NE && x.u == 0) <|
            Dict.toList nodes


processInequality :
    ( Int, STEQNodeAUX )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processInequality ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    let
        ( t1, t2 ) =
            Maybe.withDefault ( Func ( "Err", [] ) [], Func ( "Err", [] ) [] ) <| extractEQNEQTerms ni.f
    in
    let
        ( lhs, rhs, subs ) =
            simplifyEqualityWithEqs ( t1, t2, [] ) equalities
    in
    let
        subgoal =
            if lhs /= rhs then
                [ ( lhs, rhs ) ]

            else
                []

        relabelNi =
            { ni | f = Neg (Equal lhs rhs), simp = subs, u = 1 }
    in
    let
        newGoals =
            removeSubsumedGoals <|
                Dict.insert
                    ( i, i )
                    { subgoals = subgoal, substitutions = ( [], [] ) }
                    goals

        newUniverse =
            updateUniverseWithEqs (universe ++ termsClosedTerms [ lhs, rhs ]) equalities

        newNodes =
            Dict.insert i relabelNi nodes
    in
    let
        ( subtree, inconsPath ) =
            semanticTableauEqAux (deep + 1) generatedConstants maxConstants maxSize newUniverse newNodes equalities newGoals
    in
    if List.member i inconsPath || inconsPath == [] then
        ( GTree.inner relabelNi [ subtree ], inconsPath )

    else
        ( subtree, inconsPath )



-- LITERAL HANDLING


chooseLiteral : Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX )
chooseLiteral nodes =
    List.head <|
        List.filter (\( _, x ) -> x.t == L && x.u == 0) <|
            Dict.toList nodes


extractElemsLiteral : FormulaFOL -> Maybe ( Bool, Ident, List Term )
extractElemsLiteral f =
    case f of
        Pred ps pargs ->
            Just ( True, ps, pargs )

        Neg (Pred ps pargs) ->
            Just ( False, ps, pargs )

        _ ->
            Nothing


processLiteral :
    ( Int, STEQNodeAUX )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processLiteral ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    let
        ( signi, psymbi, ts ) =
            Maybe.withDefault ( False, ( "Err", [] ), [] ) <| extractElemsLiteral ni.f
    in
    let
        arityi =
            List.length ts

        ( ts_, subs ) =
            simplifyTermsWithEqs equalities ts []
    in
    let
        opposableAtoms =
            Dict.map (\_ ( _, _, tsj ) -> tsj) <|
                Dict.filter
                    (\_ ( signj, psymbj, tsj ) -> (signj == not signi) && (psymbj == psymbi) && (List.length tsj == arityi))
                <|
                    Dict.map (\_ v -> Maybe.withDefault ( False, ( "Err", [] ), [] ) <| extractElemsLiteral v.f) <|
                        Dict.filter (\_ v -> v.t == L) nodes
    in
    let
        opposableGoals =
            Dict.map (\k v -> updateGoalWithEqs k v equalities) <|
                Dict.fromList <|
                    List.map
                        (\( idop, tsop ) ->
                            ( ( idop, i )
                            , { subgoals = List.map2 Tuple.pair tsop ts
                              , substitutions = ( [], [] )
                              }
                            )
                        )
                        (Dict.toList opposableAtoms)

        relabelNi =
            if signi then
                { ni | f = Pred psymbi ts_, simp = subs, u = 1 }

            else
                { ni | f = Neg (Pred psymbi ts_), simp = subs, u = 1 }
    in
    let
        newGoals =
            removeSubsumedGoals <| Dict.union goals opposableGoals

        newUniverse =
            List.sortWith compareTerms <|
                LE.unique <|
                    universe
                        ++ termsClosedTerms ts_

        newNodes =
            Dict.insert i relabelNi nodes
    in
    let
        ( subtree, inconsPath ) =
            semanticTableauEqAux (deep + 1) generatedConstants maxConstants maxSize newUniverse newNodes equalities newGoals
    in
    if List.member i inconsPath || inconsPath == [] then
        ( GTree.inner relabelNi [ subtree ], inconsPath )

    else
        ( subtree, inconsPath )



-- ALPHA HANDLING


chooseAlpha : Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX )
chooseAlpha nodes =
    List.head <|
        List.filter (\( _, x ) -> x.t == A && x.u == 0) <|
            Dict.toList nodes


processAlpha :
    ( Int, STEQNodeAUX )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processAlpha ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    case List.head <| List.filter (\( _, n ) -> n.u == 1 && n.f == FOL_SS.ffolNegation ni.f) <| Dict.toList nodes of
        Just ( j, _ ) ->
            closeBranch { f1 = j, f2 = i, substitutions = ( [], [] ) } deep nodes

        Nothing ->
            let
                ( f1, f2 ) =
                    Maybe.withDefault ( Insat, Insat ) <| getAComponents ni.f

                relabelNi =
                    { ni | u = 1 }
            in
            let
                newNodes =
                    Dict.union
                        (Dict.insert i relabelNi nodes)
                        (Dict.fromList <|
                            [ ( deep
                              , { f = f1
                                , simp = []
                                , t = ffolType f1
                                , u = 0
                                , ut = []
                                , i = deep
                                , p1 = Just ( i, [] )
                                , subs = Nothing
                                , p2 = Nothing
                                , r = AR
                                }
                              )
                            , ( deep + 1
                              , { f = f2
                                , simp = []
                                , t = ffolType f2
                                , u = 0
                                , ut = []
                                , i = deep + 1
                                , p1 = Just ( i, [] )
                                , subs = Nothing
                                , p2 = Nothing
                                , r = AR
                                }
                              )
                            ]
                        )
            in
            let
                ( subtree, inconsPath ) =
                    semanticTableauEqAux (deep + 2) generatedConstants maxConstants maxSize universe newNodes equalities goals
            in
            if List.member i inconsPath || inconsPath == [] then
                ( GTree.inner relabelNi [ subtree ], inconsPath )

            else
                ( subtree, inconsPath )



-- BETA HANDLING


chooseBeta : Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX )
chooseBeta nodes =
    List.head <|
        List.filter (\( _, x ) -> x.t == B && x.u == 0) <|
            Dict.toList nodes


processBeta :
    ( Int, STEQNodeAUX )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processBeta ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    case List.head <| List.filter (\( _, n ) -> n.u == 1 && n.f == FOL_SS.ffolNegation ni.f) <| Dict.toList nodes of
        Just ( j, _ ) ->
            closeBranch { f1 = j, f2 = i, substitutions = ( [], [] ) } deep nodes

        Nothing ->
            let
                ( f1, f2 ) =
                    Maybe.withDefault ( Insat, Insat ) <| getBComponents ni.f
            in
            let
                relabelNi =
                    { ni | u = 1 }
            in
            let
                newNodes1 =
                    Dict.insert i relabelNi <|
                        Dict.insert
                            deep
                            { f = f1
                            , simp = []
                            , t = ffolType f1
                            , u = 0
                            , ut = []
                            , i = deep
                            , p1 = Just ( i, [] )
                            , p2 = Nothing
                            , r = BR
                            , subs = Nothing
                            }
                            nodes
            in
            let
                ( subtree, inconsPath ) =
                    semanticTableauEqAux (deep + 1) generatedConstants maxConstants maxSize universe newNodes1 equalities goals
            in
            if inconsPath == [] then
                let
                    subtree2 =
                        GTree.leaf
                            { f = FOL_SS.Taut
                            , simp = []
                            , t = T
                            , subs = Nothing
                            , u = 0
                            , ut = []
                            , i = deep
                            , r = UE
                            , p1 = Nothing
                            , p2 = Nothing
                            }
                in
                ( GTree.inner relabelNi [ subtree, subtree2 ], [] )

            else if List.member i inconsPath then
                let
                    newNodes2 =
                        Dict.insert (deep + 1) { f = f2, simp = [], t = ffolType f2, u = 0, ut = [], i = deep + 1, p1 = Just ( i, [] ), subs = Nothing, p2 = Nothing, r = BR } <|
                            Dict.insert deep
                                { f = FOL_SS.ffolNegation f1
                                , simp = []
                                , t = ffolType (FOL_SS.ffolNegation f1)
                                , u = 0
                                , ut = []
                                , i = deep
                                , p1 = Just ( i, [] )
                                , p2 = Nothing
                                , r = BR
                                , subs = Nothing
                                }
                            <|
                                Dict.insert i relabelNi nodes

                    -- newNodes2 =
                    --     Dict.insert deep { f = f2, simp = [], t = ffolType f2, u = 0, ut = [], i = deep, p1 = Just ( i, [] ), subs = Nothing, p2 = Nothing, r = BR } <|
                    --         Dict.insert i relabelNi nodes
                in
                let
                    ( subtree2, inconsPath2 ) =
                        semanticTableauEqAux (deep + 2) generatedConstants maxConstants maxSize universe newNodes2 equalities goals
                in
                if inconsPath2 == [] then
                    ( GTree.inner relabelNi [ subtree, subtree2 ], [] )

                else if List.member i inconsPath2 then
                    ( GTree.inner relabelNi [ subtree, subtree2 ], LE.unique <| inconsPath ++ inconsPath2 )

                else
                    ( subtree2, inconsPath2 )

            else
                ( subtree, inconsPath )



-- DELTA HANDLING


chooseDelta : Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX )
chooseDelta nodes =
    List.head <|
        List.filter (\( _, x ) -> x.t == D && x.u == 0) <|
            Dict.toList nodes


processDelta :
    ( Int, STEQNodeAUX )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processDelta ( i, ni ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    case List.head <| List.filter (\( _, n ) -> n.u == 1 && n.f == FOL_SS.ffolNegation ni.f) <| Dict.toList nodes of
        Just ( j, _ ) ->
            closeBranch { f1 = j, f2 = i, substitutions = ( [], [] ) } deep nodes

        Nothing ->
            let
                newC =
                    Func ( "κ", [ generatedConstants ] ) []

                ( v, g ) =
                    Maybe.withDefault ( ( "Err", [], -1 ), Insat ) <| getDGVarComponent ni.f
            in
            let
                newF =
                    reduceDN <|
                        FOL_SS.ffolApplySubstitution
                            (Dict.singleton v newC)
                            g

                relabelNi =
                    { ni | u = 1 }
            in
            let
                newNodes =
                    Dict.insert
                        deep
                        { f = newF
                        , simp = []
                        , t = ffolType newF
                        , u = 0
                        , ut = []
                        , i = deep
                        , p1 = Just ( i, [] )
                        , p2 = Nothing
                        , subs = Just ( v, newC )
                        , r = DR
                        }
                        (Dict.insert i relabelNi nodes)
            in
            let
                ( subtree, inconsPath ) =
                    semanticTableauEqAux (deep + 1) (generatedConstants + 1) maxConstants maxSize (insertInUniverse universe newC) newNodes equalities goals
            in
            if List.member i inconsPath || inconsPath == [] then
                ( GTree.inner relabelNi [ subtree ], inconsPath )

            else
                ( subtree, inconsPath )



-- GAMMA HANDLING


chooseGamma : List Term -> Dict Int STEQNodeAUX -> Maybe ( Int, STEQNodeAUX, List Term )
chooseGamma universe nodes =
    LE.last <|
        List.sortBy (\( _, _, unt ) -> List.length unt) <|
            List.filter (\( _, _, unt ) -> (not << List.isEmpty) unt) <|
                List.map (\( i, ni ) -> ( i, ni, listRemoveAll universe ni.ut )) <|
                    List.filter (\( _, ni ) -> ni.t == G) <|
                        Dict.toList nodes


processGamma :
    ( Int, STEQNodeAUX, Term )
    -> Int
    -> Int
    -> Int
    -> Int
    -> List Term
    -> Dict Int STEQNodeAUX
    -> Dict Int ( Term, Term )
    -> Dict ( Int, Int ) Goal
    -> ( FOLSemanticTableauAUX, List Int )
processGamma ( i, ni, t ) deep generatedConstants maxConstants maxSize universe nodes equalities goals =
    case List.head <| List.filter (\( _, n ) -> n.u == 1 && n.f == FOL_SS.ffolNegation ni.f) <| Dict.toList nodes of
        Just ( j, _ ) ->
            closeBranch { f1 = j, f2 = i, substitutions = ( [], [] ) } deep nodes

        Nothing ->
            let
                ( v, g ) =
                    Maybe.withDefault ( ( "Err", [], -1 ), Insat ) <| getDGVarComponent ni.f
            in
            let
                newF =
                    reduceDN <|
                        FOL_SS.ffolApplySubstitution
                            (Dict.singleton v t)
                            g

                relabelNi =
                    { ni | u = 1, ut = ni.ut ++ [ t ] }
            in
            let
                newNodes =
                    Dict.insert
                        deep
                        { f = newF
                        , simp = []
                        , t = ffolType newF
                        , u = 0
                        , ut = []
                        , i = deep
                        , p1 = Just ( i, [] )
                        , p2 = Nothing
                        , subs = Just ( v, t )
                        , r = GR
                        }
                        (Dict.insert i relabelNi nodes)
            in
            let
                ( subtree, inconsPath ) =
                    semanticTableauEqAux (deep + 1) generatedConstants maxConstants maxSize universe newNodes equalities goals
            in
            if List.member i inconsPath || inconsPath == [] then
                ( GTree.inner relabelNi [ subtree ], inconsPath )

            else
                ( subtree, inconsPath )


{-| It gives a String representation of a Semantic Tableau
-}
semanticTableauToString :
    Tree { a | r : STEQRule, i : Int, f : FormulaFOL, p1 : Maybe ( Int, List Int ), simp : List Int, subs : Maybe ( Variable, Term ), p2 : Maybe ( Int, List Int ) }
    -> String
semanticTableauToString t =
    let
        tlines =
            List.map (\l -> ( l, (Maybe.withDefault 0 << List.head << String.indexes "%") l )) <| String.split "\n\n" <| tableauToStringAux 0 t
    in
    let
        maxIndex =
            Maybe.withDefault 0 <| List.maximum <| List.map Tuple.second <| tlines
    in
    let
        tnewlines =
            List.map (\( l, i ) -> String.replace "%" (String.repeat (maxIndex - i) " " ++ "%") l) tlines
    in
    String.join "\n\n" tnewlines


tableauToStringAux :
    Int
    -> Tree { a | r : STEQRule, i : Int, f : FormulaFOL, p1 : Maybe ( Int, List Int ), simp : List Int, subs : Maybe ( Variable, Term ), p2 : Maybe ( Int, List Int ) }
    -> String
tableauToStringAux indent t =
    case GTree.root t of
        Just ( l, ch ) ->
            String.repeat indent "   " ++ tableauNodeToString l ++ (String.join "" <| List.map (tableauToStringAux (indent + 1)) ch)

        Nothing ->
            ""


tableauNodeToString :
    { a | r : STEQRule, i : Int, f : FormulaFOL, p1 : Maybe ( Int, List Int ), simp : List Int, subs : Maybe ( Variable, Term ), p2 : Maybe ( Int, List Int ) }
    -> String
tableauNodeToString ni =
    case ni.r of
        LL ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ ""
                ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                ++ ". "
                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                ++ "\n\n"

        AR ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ "𝛼("
                ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                ++ ")"
                ++ ". "
                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                ++ "\n\n"

        BR ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ "𝛽("
                ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                ++ ")"
                ++ ". "
                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                ++ "\n\n"

        GR ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ "𝛾("
                ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                ++ ")"
                ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs)
                ++ ". "
                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                ++ "\n\n"

        DR ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ "𝛿("
                ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                ++ ")"
                ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs)
                ++ ". "
                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                ++ "\n\n"

        IR ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ (case ni.p2 of
                        Nothing ->
                            case ni.p1 of
                                Just ( id1, simp1 ) ->
                                    "→←" ++ ". " ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp1) ++ "(" ++ String.fromInt id1 ++ ")"

                                Nothing ->
                                    ""

                        Just ( id2, simp2 ) ->
                            case ni.p1 of
                                Just ( id1, simp1 ) ->
                                    (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp1)
                                        ++ "("
                                        ++ String.fromInt id1
                                        ++ ") "
                                        ++ "→←"
                                        ++ ". "
                                        ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp2)
                                        ++ "("
                                        ++ String.fromInt id2
                                        ++ ") "

                                Nothing ->
                                    ""
                   )
                ++ "\n\n"

        IF ->
            String.fromInt ni.i
                ++ ":  "
                ++ FOL_SS.ffolToString ni.f
                ++ "     % "
                ++ "initial-"
                ++ String.fromInt ni.i
                ++ ". "
                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                ++ "\n\n"

        OL ->
            "◯ \n\n"

        UE ->
            "unexplored     \n\n"


translateID : Dict Int Int -> Int -> Int
translateID corresp i =
    Maybe.withDefault i <| Dict.get i corresp


translateList : Dict Int Int -> List Int -> List Int
translateList corresp l =
    List.map (translateID corresp) l


postProcessingSTEQ :
    Int
    -> Dict Int Int
    -> FOLSemanticTableauAUX
    -> List FOLSemanticTableau
postProcessingSTEQ deep corresp tableau =
    case GTree.root tableau of
        Nothing ->
            []

        Just ( l, ch ) ->
            if Dict.member l.i corresp then
                List.concat <| List.map (postProcessingSTEQ deep corresp) ch

            else
                let
                    lsimp =
                        translateList corresp l.simp

                    newCorresp =
                        Dict.insert l.i deep corresp
                in
                let
                    newl =
                        { i = deep
                        , f = l.f
                        , simp = lsimp
                        , p1 = Maybe.map (\( x, y ) -> ( translateID corresp x, translateList corresp y )) l.p1
                        , p2 = Maybe.map (\( x, y ) -> ( translateID corresp x, translateList corresp y )) l.p2
                        , subs = l.subs
                        , r = l.r
                        }
                in
                [ GTree.inner
                    newl
                    (List.concat <| List.map (postProcessingSTEQ (deep + 1) newCorresp) ch)
                ]


updateUniverseWithEqs : List Term -> Dict Int ( Term, Term ) -> List Term
updateUniverseWithEqs universe equalities =
    LE.unique <| List.sortWith compareTerms <| List.map (\u -> Tuple.first <| simplifyTermWithEqs equalities u) universe


updateGoalsWithEqs : Dict ( Int, Int ) Goal -> Dict Int ( Term, Term ) -> Dict ( Int, Int ) Goal
updateGoalsWithEqs goals equalities =
    Dict.map (\( i1, i2 ) g -> updateGoalWithEqs ( i1, i2 ) g equalities) goals


updateGoalWithEqs : ( Int, Int ) -> Goal -> Dict Int ( Term, Term ) -> Goal
updateGoalWithEqs ( i1, i2 ) g equalities =
    if i1 == i2 then
        let
            terms_ =
                simplifyTermsWithEqs equalities (Maybe.withDefault [] <| Maybe.map (\( t1, t2 ) -> [ t1, t2 ]) <| List.head g.subgoals) (Tuple.first g.substitutions)
        in
        let
            subgoals =
                case terms_ of
                    ( [ t1_, t2_ ], _ ) ->
                        if t1_ /= t2_ then
                            [ ( t1_, t2_ ) ]

                        else
                            []

                    _ ->
                        []

            lhs_rhs_subs =
                Tuple.second terms_
        in
        { subgoals = subgoals, substitutions = ( lhs_rhs_subs, lhs_rhs_subs ) }

    else
        let
            ( lhs_subgoals, lhs_subs ) =
                simplifyTermsWithEqs equalities (List.map Tuple.first g.subgoals) (Tuple.first g.substitutions)

            ( rhs_subgoals, rhs_subs ) =
                simplifyTermsWithEqs equalities (List.map Tuple.second g.subgoals) (Tuple.second g.substitutions)
        in
        { subgoals = List.filter (\( x, y ) -> x /= y) <| List.map2 Tuple.pair lhs_subgoals rhs_subgoals, substitutions = ( lhs_subs, rhs_subs ) }


tableauNodeToJSON : STEQNode -> Value -> Value
tableauNodeToJSON ni children =
    case ni.r of
        LL ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel"
                  , JSONE.string <|
                        (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                            ++ "("
                            ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                            ++ ")"
                  )
                , ( "children", children )
                ]

        AR ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝛼("
                            ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                            ++ ")."
                            ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                  )
                , ( "children", children )
                ]

        BR ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝛽("
                            ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                            ++ ")."
                            ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                  )
                , ( "children", children )
                ]

        GR ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝛾("
                            ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                            ++ ")"
                            ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs)
                            ++ "."
                            ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                  )
                , ( "children", children )
                ]

        DR ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel"
                  , JSONE.string <|
                        "𝛿("
                            ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1)
                            ++ ")"
                            ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs)
                            ++ "."
                            ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)
                  )
                , ( "children", children )
                ]

        IR ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel"
                  , JSONE.string <|
                        case ni.p2 of
                            Nothing ->
                                case ni.p1 of
                                    Just ( id1, simp1 ) ->
                                        "→←" ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp1) ++ "(" ++ String.fromInt id1 ++ ")"

                                    Nothing ->
                                        ""

                            Just ( id2, simp2 ) ->
                                case ni.p1 of
                                    Just ( id1, simp1 ) ->
                                        (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp1)
                                            ++ "("
                                            ++ String.fromInt id1
                                            ++ ") "
                                            ++ "→←"
                                            ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp2)
                                            ++ "("
                                            ++ String.fromInt id2
                                            ++ ") "

                                    Nothing ->
                                        ""
                  )
                , ( "children", children )
                ]

        IF ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string <| FOL_SS.ffolToString ni.f )
                , ( "xlabel", JSONE.string "initial" )
                , ( "children", children )
                ]

        OL ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string "◯" )
                , ( "xlabel", JSONE.string "" )
                , ( "children", children )
                ]

        UE ->
            JSONE.object
                [ ( "name", JSONE.int ni.i )
                , ( "label", JSONE.string "!" )
                , ( "xlabel", JSONE.string "unexplored" )
                , ( "children", children )
                ]


{-| It gives a JSON Tree representation for the tableau.
-}
semanticTableauToJSON : FOLSemanticTableau -> Value
semanticTableauToJSON t =
    case GTree.root t of
        Just ( l, ch ) ->
            let
                children =
                    JSONE.list semanticTableauToJSON ch
            in
            tableauNodeToJSON l children

        Nothing ->
            JSONE.null


{-| It gives a DOT representation for the tableau.
-}
semanticTableauToDOT : FOLSemanticTableau -> String
semanticTableauToDOT t =
    "digraph{" ++ (Tuple.first <| semanticTableauNodeToDOTAux 0 -1 t) ++ "}"


semanticTableauNodeToDOTAux : Int -> Int -> FOLSemanticTableau -> ( String, Int )
semanticTableauNodeToDOTAux gid p t =
    case GTree.root t of
        Just ( l, ch ) ->
            semanticTableauNodeToDOTAux2 gid p l ch

        Nothing ->
            ( "", -1 )


semanticTableauNodeToDOTAux2 : Int -> Int -> STEQNode -> List (Tree STEQNode) -> ( String, Int )
semanticTableauNodeToDOTAux2 gid p ni children =
    case children of
        [ c ] ->
            let
                ( res, lgid ) =
                    semanticTableauNodeToDOTAux (gid + 1) gid c
            in
            case ni.r of
                LL ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ((String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp) ++ "(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")") ++ "\"];") ++ res, lgid )

                AR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛼(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res, lgid )

                BR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛽(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res, lgid )

                GR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛾(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")" ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs) ++ "." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res, lgid )

                DR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛿(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")" ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs) ++ "." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res, lgid )

                IF ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid) ++ res, lgid )

                _ ->
                    ( "", -2 )

        [ c1, c2 ] ->
            let
                ( res1, lgid1 ) =
                    semanticTableauNodeToDOTAux (gid + 1) gid c1
            in
            let
                ( res2, lgid2 ) =
                    semanticTableauNodeToDOTAux (lgid1 + 1) gid c2
            in
            case ni.r of
                LL ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ((String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp) ++ "(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")") ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                AR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛼(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                BR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛽(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                GR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛾(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")" ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs) ++ "." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                DR ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ ("𝛿(" ++ (Maybe.withDefault "" <| Maybe.map (String.fromInt << Tuple.first) ni.p1) ++ ")" ++ (Maybe.withDefault "" <| Maybe.map (\( x, y ) -> FOL_SS.substitutionToString <| Dict.singleton x y) ni.subs) ++ "." ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| ni.simp)) ++ "\"];") ++ res1 ++ "\n" ++ res2, lgid2 )

                IF ->
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid) ++ res1 ++ "\n" ++ res2, lgid2 )

                _ ->
                    ( "", -2 )

        _ ->
            case ni.r of
                IR ->
                    let
                        elabel =
                            case ni.p2 of
                                Nothing ->
                                    case ni.p1 of
                                        Just ( id1, simp1 ) ->
                                            "→←" ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp1) ++ "(" ++ String.fromInt id1 ++ ")"

                                        Nothing ->
                                            ""

                                Just ( id2, simp2 ) ->
                                    case ni.p1 of
                                        Just ( id1, simp1 ) ->
                                            (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp1)
                                                ++ "("
                                                ++ String.fromInt id1
                                                ++ ") "
                                                ++ "→←"
                                                ++ (String.join "⚬" <| List.map (\id -> "𝓛𝓛" ++ String.fromInt id) <| simp2)
                                                ++ "("
                                                ++ String.fromInt id2
                                                ++ ") "

                                        Nothing ->
                                            ""
                    in
                    ( String.fromInt gid ++ " [label=\"" ++ FOL_SS.ffolToString ni.f ++ "\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid ++ " [label=\"" ++ elabel ++ "\"];"), gid )

                OL ->
                    ( String.fromInt gid ++ " [label=\"◯\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid), gid )

                UE ->
                    ( String.fromInt gid ++ " [label=\"!\"];\n" ++ (String.fromInt p ++ " -> " ++ String.fromInt gid), gid )

                _ ->
                    ( "", -2 )
