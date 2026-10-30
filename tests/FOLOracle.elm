module FOLOracle exposing
    ( Struct, structure, toLStructure
    , varX, varY, varZ, cA, cB
    , term, groundTerm, formula, closedFormula, closedFormulaEq, closedSet, universalClause, clauseSet, functionFreeClauseSet
    , eval, evalClosed, evalTerm, evalClauses, freeVars, closure
    , extraFunctions, existsExpansion
    , unify
    , isPrenex, quantifierFree
    )

{-| Reference semantics for first-order logic on small finite structures,
written independently of the library, plus fuzzers.

Signature of the generated formulas: constants a, b; function f/1;
predicates P/1, Q/2, R/0; variables X, Y, Z. Function symbols outside this
signature (e.g. Skolem functions) are interpreted by a seeded hash, and
`existsExpansion` searches all their interpretations exhaustively.

-}

import Dict exposing (Dict)
import Fuzz exposing (Fuzzer)
import List.Extra as LE
import LogicUS.FOL.Clauses exposing (ClauseFOL, ClauseFOLAtom(..), ClauseFOLSet)
import LogicUS.FOL.SyntaxSemantics as SS exposing (FormulaFOL(..), Ident, L_Structure, Term(..), Variable)
import Set exposing (Set)



-- SIGNATURE


varX : Variable
varX =
    ( "X", [], 0 )


varY : Variable
varY =
    ( "Y", [], 0 )


varZ : Variable
varZ =
    ( "Z", [], 0 )


cA : Term
cA =
    Func ( "a", [] ) []


cB : Term
cB =
    Func ( "b", [] ) []


fF : Term -> Term
fF t =
    Func ( "f", [] ) [ t ]



-- STRUCTURES


type alias Struct =
    { n : Int
    , a : Int
    , b : Int
    , f : List Int
    , p : List Bool
    , q : List Bool
    , r : Bool
    , seed : Int

    -- explicit interpretation of extra function symbols (by name), if any
    , extra : Dict String (Dict (List Int) Int)
    }


structure : Fuzzer Struct
structure =
    Fuzz.intRange 1 3
        |> Fuzz.andThen
            (\n ->
                let
                    el =
                        Fuzz.intRange 0 (n - 1)
                in
                Fuzz.map5 (\( a, b ) f p ( q, r ) seed -> { n = n, a = a, b = b, f = f, p = p, q = q, r = r, seed = seed, extra = Dict.empty })
                    (Fuzz.pair el el)
                    (Fuzz.listOfLength n el)
                    (Fuzz.listOfLength n Fuzz.bool)
                    (Fuzz.pair (Fuzz.listOfLength (n * n) Fuzz.bool) Fuzz.bool)
                    (Fuzz.intRange 0 100000)
            )


at : Int -> List a -> Maybe a
at i xs =
    List.head (List.drop i xs)


identName : Ident -> String
identName ( s, is ) =
    s ++ "_" ++ String.join "," (List.map String.fromInt is)


hash : Int -> String -> Int
hash seed s =
    String.foldl (\c acc -> modBy 1000003 (acc * 131 + Char.toCode c)) (seed + 7) s


{-| The library's representation of the same structure (only the base signature).
-}
toLStructure : Struct -> L_Structure Int
toLStructure s =
    let
        dom =
            List.range 0 (s.n - 1)
    in
    ( Set.fromList dom
    , { const = Dict.fromList [ ( ( "a", [] ), s.a ), ( ( "b", [] ), s.b ) ]
      , func = Dict.fromList [ ( ( "f", [] ), ( 1, Dict.fromList (List.indexedMap (\i v -> ( [ i ], v )) s.f) ) ) ]
      , pred =
            Dict.fromList
                [ ( ( "P", [] ), ( 1, Set.fromList (List.filterMap (\i -> if at i s.p == Just True then Just [ i ] else Nothing) dom) ) )
                , ( ( "Q", [] ), ( 2, Set.fromList (List.filterMap (\( i, j ) -> if at (i * s.n + j) s.q == Just True then Just [ i, j ] else Nothing) (LE.lift2 Tuple.pair dom dom)) ) )
                , ( ( "R", [] )
                  , ( 0
                    , if s.r then
                        Set.singleton []

                      else
                        Set.empty
                    )
                  )
                ]
      }
    )



-- EVALUATION


evalTerm : Struct -> Dict Variable Int -> Term -> Int
evalTerm s env t =
    case t of
        Var v ->
            Dict.get v env |> Maybe.withDefault 0

        Func ( "a", [] ) [] ->
            s.a

        Func ( "b", [] ) [] ->
            s.b

        Func ( "f", [] ) [ u ] ->
            at (evalTerm s env u) s.f |> Maybe.withDefault 0

        Func id args ->
            let
                vals =
                    List.map (evalTerm s env) args
            in
            case Dict.get (identName id) s.extra |> Maybe.andThen (Dict.get vals) of
                Just v ->
                    v

                Nothing ->
                    modBy s.n (hash s.seed (identName id ++ "(" ++ String.join "," (List.map String.fromInt vals) ++ ")"))


eval : Struct -> Dict Variable Int -> FormulaFOL -> Bool
eval s env f =
    case f of
        Pred ( "P", [] ) [ t ] ->
            at (evalTerm s env t) s.p == Just True

        Pred ( "Q", [] ) [ t1, t2 ] ->
            at (evalTerm s env t1 * s.n + evalTerm s env t2) s.q == Just True

        Pred ( "R", [] ) [] ->
            s.r

        Pred id ts ->
            modBy 2 (hash (s.seed + 1) (identName id ++ String.join "," (List.map (String.fromInt << evalTerm s env) ts))) == 0

        Equal t1 t2 ->
            evalTerm s env t1 == evalTerm s env t2

        Neg g ->
            not (eval s env g)

        Conj g h ->
            eval s env g && eval s env h

        Disj g h ->
            eval s env g || eval s env h

        Impl g h ->
            not (eval s env g) || eval s env h

        Equi g h ->
            eval s env g == eval s env h

        Exists v g ->
            List.any (\o -> eval s (Dict.insert v o env) g) (List.range 0 (s.n - 1))

        Forall v g ->
            List.all (\o -> eval s (Dict.insert v o env) g) (List.range 0 (s.n - 1))

        Insat ->
            False

        Taut ->
            True


evalClosed : Struct -> FormulaFOL -> Bool
evalClosed s f =
    eval s Dict.empty (closure f)


termVars : Term -> Set Variable
termVars t =
    case t of
        Var v ->
            Set.singleton v

        Func _ ts ->
            List.foldl (Set.union << termVars) Set.empty ts


freeVars : FormulaFOL -> Set Variable
freeVars f =
    case f of
        Pred _ ts ->
            List.foldl (Set.union << termVars) Set.empty ts

        Equal t1 t2 ->
            Set.union (termVars t1) (termVars t2)

        Neg g ->
            freeVars g

        Conj g h ->
            Set.union (freeVars g) (freeVars h)

        Disj g h ->
            Set.union (freeVars g) (freeVars h)

        Impl g h ->
            Set.union (freeVars g) (freeVars h)

        Equi g h ->
            Set.union (freeVars g) (freeVars h)

        Exists v g ->
            Set.remove v (freeVars g)

        Forall v g ->
            Set.remove v (freeVars g)

        _ ->
            Set.empty


{-| Universal closure.
-}
closure : FormulaFOL -> FormulaFOL
closure f =
    Set.foldr Forall f (freeVars f)


clauseToFormula : ClauseFOL -> FormulaFOL
clauseToFormula c =
    case c of
        [] ->
            Insat

        _ ->
            SS.sfolDisjunction
                (List.map
                    (\( clauseAtom, pol ) ->
                        let
                            a =
                                case clauseAtom of
                                    P id ts ->
                                        Pred id ts

                                    Eq t1 t2 ->
                                        Equal t1 t2
                        in
                        if pol then
                            a

                        else
                            Neg a
                    )
                    c
                )


{-| A clause set is true when every clause is true for every value of its variables.
-}
evalClauses : Struct -> ClauseFOLSet -> Bool
evalClauses s cs =
    List.all (evalClosed s << clauseToFormula) cs



-- EXTRA FUNCTION SYMBOLS (e.g. Skolem)


termFuncs : Term -> List ( String, Int )
termFuncs t =
    case t of
        Var _ ->
            []

        Func id args ->
            ( identName id, List.length args ) :: List.concatMap termFuncs args


formulaFuncs : FormulaFOL -> List ( String, Int )
formulaFuncs f =
    case f of
        Pred _ ts ->
            List.concatMap termFuncs ts

        Equal t1 t2 ->
            termFuncs t1 ++ termFuncs t2

        Neg g ->
            formulaFuncs g

        Conj g h ->
            formulaFuncs g ++ formulaFuncs h

        Disj g h ->
            formulaFuncs g ++ formulaFuncs h

        Impl g h ->
            formulaFuncs g ++ formulaFuncs h

        Equi g h ->
            formulaFuncs g ++ formulaFuncs h

        Exists _ g ->
            formulaFuncs g

        Forall _ g ->
            formulaFuncs g

        _ ->
            []


{-| Function symbols (name, arity) outside the base signature.
-}
extraFunctions : List FormulaFOL -> List ( String, Int )
extraFunctions fs =
    fs
        |> List.concatMap formulaFuncs
        |> LE.unique
        |> List.filter (\( name, _ ) -> not (List.member name [ "a_", "b_", "f_" ]))


{-| Is there an interpretation of the extra function symbols (keeping the rest
of the structure) that makes every formula true? `Nothing` when the search
space is too big to enumerate.
-}
existsExpansion : Struct -> List FormulaFOL -> Maybe Bool
existsExpansion s fs =
    let
        dom =
            List.range 0 (s.n - 1)

        tuples k =
            List.foldl (\_ acc -> LE.lift2 (::) dom acc) [ [] ] (List.range 1 k)

        slots =
            extraFunctions fs |> List.concatMap (\( name, k ) -> List.map (Tuple.pair name) (tuples k))

        size =
            s.n ^ List.length slots
    in
    if size > 20000 then
        Nothing

    else
        let
            assignments =
                List.foldl (\_ acc -> LE.lift2 (::) dom acc) [ [] ] slots

            build values =
                List.map2 Tuple.pair slots values
                    |> List.foldl
                        (\( ( name, args ), v ) d ->
                            Dict.update name (\m -> Just (Dict.insert args v (Maybe.withDefault Dict.empty m))) d
                        )
                        Dict.empty
        in
        Just (List.any (\vals -> List.all (evalClosed { s | extra = build vals }) fs) assignments)



-- FUZZERS


term : Int -> Fuzzer Term
term depth =
    if depth <= 0 then
        Fuzz.oneOfValues [ Var varX, Var varY, Var varZ, cA, cB ]

    else
        Fuzz.frequency
            [ ( 3, term 0 )
            , ( 1, Fuzz.map fF (Fuzz.lazy (\_ -> term (depth - 1))) )
            ]


groundTerm : Int -> Fuzzer Term
groundTerm depth =
    if depth <= 0 then
        Fuzz.oneOfValues [ cA, cB ]

    else
        Fuzz.frequency
            [ ( 2, groundTerm 0 )
            , ( 1, Fuzz.map fF (Fuzz.lazy (\_ -> groundTerm (depth - 1))) )
            ]


atom : Bool -> Fuzzer FormulaFOL
atom withEq =
    Fuzz.frequency
        ([ ( 3, Fuzz.map (\t -> Pred ( "P", [] ) [ t ]) (term 1) )
         , ( 3, Fuzz.map2 (\t1 t2 -> Pred ( "Q", [] ) [ t1, t2 ]) (term 1) (term 1) )
         , ( 1, Fuzz.constant (Pred ( "R", [] ) []) )
         , ( 0.3, Fuzz.constant Insat )
         , ( 0.3, Fuzz.constant Taut )
         ]
            ++ (if withEq then
                    [ ( 3, Fuzz.map2 Equal (term 1) (term 1) ) ]

                else
                    []
               )
        )


formulaWith : Bool -> Int -> Fuzzer FormulaFOL
formulaWith withEq depth =
    if depth <= 0 then
        atom withEq

    else
        let
            sub =
                Fuzz.lazy (\_ -> formulaWith withEq (depth - 1))

            var =
                Fuzz.oneOfValues [ varX, varY, varZ ]
        in
        Fuzz.frequency
            [ ( 2, atom withEq )
            , ( 2, Fuzz.map Neg sub )
            , ( 2, Fuzz.map2 Conj sub sub )
            , ( 2, Fuzz.map2 Disj sub sub )
            , ( 1, Fuzz.map2 Impl sub sub )
            , ( 1, Fuzz.map2 Equi sub sub )
            , ( 2, Fuzz.map2 Forall var sub )
            , ( 2, Fuzz.map2 Exists var sub )
            ]


formula : Int -> Fuzzer FormulaFOL
formula =
    formulaWith False


closedFormula : Int -> Fuzzer FormulaFOL
closedFormula depth =
    Fuzz.map closure (formulaWith False depth)


closedFormulaEq : Int -> Fuzzer FormulaFOL
closedFormulaEq depth =
    Fuzz.map closure (formulaWith True depth)


closedSet : Int -> Int -> Fuzzer (List FormulaFOL)
closedSet maxSize depth =
    Fuzz.listOfLengthBetween 1 maxSize (closedFormula depth)


literal : Bool -> Fuzzer ( ClauseFOLAtom, Bool )
literal withFunctions =
    let
        t =
            if withFunctions then
                term 1

            else
                term 0
    in
    Fuzz.pair
        (Fuzz.frequency
            [ ( 3, Fuzz.map (\x -> P ( "P", [] ) [ x ]) t )
            , ( 2, Fuzz.map2 (\x y -> P ( "Q", [] ) [ x, y ]) t t )
            , ( 1, Fuzz.constant (P ( "R", [] ) []) )
            ]
        )
        Fuzz.bool


universalClause : Bool -> Fuzzer ClauseFOL
universalClause withFunctions =
    Fuzz.listOfLengthBetween 1 3 (literal withFunctions)


clauseSet : Fuzzer ClauseFOLSet
clauseSet =
    Fuzz.listOfLengthBetween 1 5 (universalClause True)


functionFreeClauseSet : Fuzzer ClauseFOLSet
functionFreeClauseSet =
    Fuzz.listOfLengthBetween 1 4 (universalClause False)



-- UNIFICATION (Robinson)


applySubst : Dict Variable Term -> Term -> Term
applySubst s t =
    case t of
        Var v ->
            case Dict.get v s of
                Just u ->
                    applySubst s u

                Nothing ->
                    t

        Func id args ->
            Func id (List.map (applySubst s) args)


occurs : Variable -> Term -> Bool
occurs v t =
    Set.member v (termVars t)


{-| A most general unifier of two lists of terms, as a triangular substitution
fully applied (Nothing if they do not unify).
-}
unify : List ( Term, Term ) -> Maybe (Dict Variable Term)
unify eqs =
    let
        go pending s =
            case pending of
                [] ->
                    Just s

                ( t1, t2 ) :: rest ->
                    case ( applySubst s t1, applySubst s t2 ) of
                        ( Var v, Var w ) ->
                            if v == w then
                                go rest s

                            else
                                go rest (Dict.insert v (Var w) s)

                        ( Var v, u ) ->
                            if occurs v u then
                                Nothing

                            else
                                go rest (Dict.insert v u s)

                        ( u, Var v ) ->
                            if occurs v u then
                                Nothing

                            else
                                go rest (Dict.insert v u s)

                        ( Func g xs, Func h ys ) ->
                            if g == h && List.length xs == List.length ys then
                                go (List.map2 Tuple.pair xs ys ++ rest) s

                            else
                                Nothing
    in
    go eqs Dict.empty |> Maybe.map (\s -> Dict.map (\_ t -> applySubst s t) s)



-- SHAPES


quantifierFree : FormulaFOL -> Bool
quantifierFree f =
    case f of
        Exists _ _ ->
            False

        Forall _ _ ->
            False

        Neg g ->
            quantifierFree g

        Conj g h ->
            quantifierFree g && quantifierFree h

        Disj g h ->
            quantifierFree g && quantifierFree h

        Impl g h ->
            quantifierFree g && quantifierFree h

        Equi g h ->
            quantifierFree g && quantifierFree h

        _ ->
            True


isPrenex : FormulaFOL -> Bool
isPrenex f =
    case f of
        Exists _ g ->
            isPrenex g

        Forall _ g ->
            isPrenex g

        _ ->
            quantifierFree f
