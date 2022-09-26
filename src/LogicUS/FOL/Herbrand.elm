module LogicUS.FOL.Herbrand exposing
    ( Signature, ffolSignature, sfolSignature
    , signatureHerbrandUniverse, ffolHerbrandUniverse, sfolHerbrandUniverse, signatureHerbrandBase, ffolHerbrandBase, sfolHerbrandBase, signatureHerbrandInterpretations, ffolHerbrandInterpretations, sfolHerbrandInterpretations, ffolInterpretsHerbrand, sfolInterpretsHerbrand, ffolHerbrandModels, sfolHerbrandModels, ffolHerbrandExtension, sfolHerbrandExtension
    )

{-| The module provides the tools for applying Herbrand works over First Order Logic


# Signatures

@docs Signature, ffolSignature, sfolSignature


# Herbrand Works

@docs signatureHerbrandUniverse, ffolHerbrandUniverse, sfolHerbrandUniverse, signatureHerbrandBase, ffolHerbrandBase, sfolHerbrandBase, signatureHerbrandInterpretations, ffolHerbrandInterpretations, sfolHerbrandInterpretations, ffolInterpretsHerbrand, sfolInterpretsHerbrand, ffolHerbrandModels, sfolHerbrandModels, ffolHerbrandExtension, sfolHerbrandExtension

-}

import Dict exposing (Dict)
import List
import List.Extra exposing (cartesianProduct)
import LogicUS.FOL.AuxiliarFuctions exposing (powerset, uniqueConcatList)
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), SetFOL, Term(..))
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), SetPL)
import Set exposing (Set)


{-| A signature is a 3-tuple with the constants, the functions symbols with its arity and the predicate symbols with its arity that apears in one (or a set of) opened formula(s).
-}
type alias Signature =
    ( Set ( String, List Int ), Dict ( String, List Int ) Int, Dict ( String, List Int ) Int )



-- Union of 2 signatures


union2Signatures : Signature -> Signature -> Signature
union2Signatures ( cs1, fs1, ps1 ) ( cs2, fs2, ps2 ) =
    let
        cs =
            Set.union cs1 cs2

        fs =
            Dict.union fs1 fs2

        ps =
            Dict.union ps1 ps2
    in
    ( cs, fs, ps )



-- Signature of a term


signatureTerm : Term -> Signature
signatureTerm t =
    case t of
        Var _ ->
            ( Set.empty, Dict.empty, Dict.empty )

        Func f [] ->
            ( Set.singleton f, Dict.empty, Dict.empty )

        Func f terms ->
            List.foldl (\x ac -> union2Signatures ac (signatureTerm x)) ( Set.empty, Dict.singleton f (List.length terms), Dict.empty ) terms


{-| It calculates the signature associated to a Herbrand formula (opened and without equality)
-}
ffolSignature : FormulaFOL -> Maybe Signature
ffolSignature f =
    case f of
        FOL_SS.Pred p terms ->
            Just <| List.foldl (\x ac -> union2Signatures ac (signatureTerm x)) ( Set.empty, Dict.empty, Dict.singleton p (List.length terms) ) terms

        FOL_SS.Equal _ _ ->
            Nothing

        FOL_SS.Neg x ->
            ffolSignature x

        FOL_SS.Conj x y ->
            Maybe.map2 union2Signatures (ffolSignature x) (ffolSignature y)

        FOL_SS.Disj x y ->
            Maybe.map2 union2Signatures (ffolSignature x) (ffolSignature y)

        FOL_SS.Impl x y ->
            Maybe.map2 union2Signatures (ffolSignature x) (ffolSignature y)

        FOL_SS.Equi x y ->
            Maybe.map2 union2Signatures (ffolSignature x) (ffolSignature y)

        FOL_SS.Forall _ _ ->
            Nothing

        FOL_SS.Exists _ _ ->
            Nothing

        FOL_SS.Insat ->
            Just ( Set.empty, Dict.empty, Dict.empty )

        FOL_SS.Taut ->
            Just ( Set.empty, Dict.empty, Dict.empty )


{-| It calculates the signature of a set of opened formulas
-}
sfolSignature : SetFOL -> Maybe Signature
sfolSignature ls =
    List.foldl
        (\f ac -> Maybe.map2 union2Signatures ac (ffolSignature f))
        (Just ( Set.empty, Dict.empty, Dict.empty ))
        ls


{-| It generates the Herbrand Universe of n-order according to a Signature
-}
signatureHerbrandUniverse : Signature -> Int -> List Term
signatureHerbrandUniverse ( cs, fs, ps ) n =
    if n <= 0 then
        if Set.isEmpty cs then
            [ Func ( "ç", [ 0 ] ) [] ]

        else
            List.map (\x -> Func x []) <| Set.toList <| cs

    else
        let
            uH_prev =
                signatureHerbrandUniverse ( cs, fs, ps ) (n - 1)
        in
        List.foldl (\x ac -> uniqueConcatList ac x) uH_prev <| List.map (\( f, a ) -> List.map (\ts -> Func f ts) (List.Extra.cartesianProduct (List.repeat a uH_prev))) <| Dict.toList fs


{-| It generates the Herbrand Universe of an opened formula
-}
ffolHerbrandUniverse : FormulaFOL -> Int -> Maybe (List Term)
ffolHerbrandUniverse f n =
    Maybe.map (\s -> signatureHerbrandUniverse s n) (ffolSignature f)


{-| It generates the Herbrand Universe of a set of opened formulas
-}
sfolHerbrandUniverse : List FormulaFOL -> Int -> Maybe (List Term)
sfolHerbrandUniverse fs n =
    Maybe.map (\s -> signatureHerbrandUniverse s n) (sfolSignature fs)


{-| It generates the Herbrand Base of n-order from a signature. That is, the set of all possible atoms for a signature wich corresponds to the applicatiion of each symbol of predicate (of arity k) over each k-tuple of elements of n-order universe Herbrand
-}
signatureHerbrandBase : Signature -> Int -> List FormulaFOL
signatureHerbrandBase ( cs, fs, ps ) n =
    let
        uH =
            signatureHerbrandUniverse ( cs, fs, ps ) n
    in
    List.foldl (\x ac -> uniqueConcatList ac x) [] <| List.map (\( p, a ) -> List.map (\ts -> Pred p ts) (List.Extra.cartesianProduct (List.repeat a uH))) <| Dict.toList <| ps


{-| It generates a the Herbrand Base of n-order from an opened formula. That is, a set of all posible atoms formed with the predicate symbosl of a formula, cosidering all the posible substitutions with the n-order Herbrand Unviverse elements.
-}
ffolHerbrandBase : FormulaFOL -> Int -> Maybe (List FormulaFOL)
ffolHerbrandBase f n =
    Maybe.map (\s -> signatureHerbrandBase s n) (ffolSignature f)


{-| It generates a the Herbrand Base of n-order from a set of opened formulas. That is, a set of opened and closed formulas where all posible substitutions with the n-order Herbrand Unviverse elements.
-}
sfolHerbrandBase : SetFOL -> Int -> Maybe (List FormulaFOL)
sfolHerbrandBase fs n =
    Maybe.map (\s -> signatureHerbrandBase s n) (sfolSignature fs)


{-| It generates all the possible Herbrand Interpretations of n-order from a signature. That is, all the possible subsets of the n-order Herbrand Basis associated to the signature.
-}
signatureHerbrandInterpretations : Signature -> Int -> List (List FormulaFOL)
signatureHerbrandInterpretations s n =
    powerset <| signatureHerbrandBase s n


{-| It generates all the possible Herbrand Interpretations of n-order from a opened formula. That is, all the possible subsets of the n-order Herbrand Basis associated to the formula
-}
ffolHerbrandInterpretations : FormulaFOL -> Int -> Maybe (List (List FormulaFOL))
ffolHerbrandInterpretations f n =
    Maybe.map (\s -> signatureHerbrandInterpretations s n) (ffolSignature f)


{-| It generates all the possible Herbrand Interpretations of n-order from a set of opened formulas. That is, all the possible subsets of the n-order Herbrand Basis associated to the formula
-}
sfolHerbrandInterpretations : SetFOL -> Int -> Maybe (List (List FormulaFOL))
sfolHerbrandInterpretations fs n =
    Maybe.map (\s -> signatureHerbrandInterpretations s n) (sfolSignature fs)


{-| It valuates a Formula regarding to a Herbrand Interpretation and Herbrand Universe
-}
ffolInterpretsHerbrand : FormulaFOL -> List FormulaFOL -> List Term -> Maybe Bool
ffolInterpretsHerbrand f iH uH =
    case f of
        FOL_SS.Pred _ _ ->
            Just <| List.member f iH

        FOL_SS.Equal _ _ ->
            Nothing

        FOL_SS.Neg f1 ->
            Maybe.map not (ffolInterpretsHerbrand f1 iH uH)

        FOL_SS.Conj f1 f2 ->
            let
                if1 =
                    ffolInterpretsHerbrand f1 iH uH

                if2 =
                    ffolInterpretsHerbrand f2 iH uH
            in
            Maybe.map2 (&&) if1 if2

        FOL_SS.Disj f1 f2 ->
            let
                if1 =
                    ffolInterpretsHerbrand f1 iH uH

                if2 =
                    ffolInterpretsHerbrand f2 iH uH
            in
            Maybe.map2 (||) if1 if2

        FOL_SS.Impl f1 f2 ->
            let
                if1 =
                    ffolInterpretsHerbrand f1 iH uH

                if2 =
                    ffolInterpretsHerbrand f2 iH uH
            in
            Maybe.map2 (\a b -> not a || b) if1 if2

        FOL_SS.Equi f1 f2 ->
            let
                if1 =
                    ffolInterpretsHerbrand f1 iH uH

                if2 =
                    ffolInterpretsHerbrand f2 iH uH
            in
            Maybe.map2 (==) if1 if2

        FOL_SS.Forall _ _ ->
            Nothing

        FOL_SS.Exists _ _ ->
            Nothing

        FOL_SS.Taut ->
            Just True

        FOL_SS.Insat ->
            Just False


{-| It valuates a set of opened formulas regarding to a Herbrand Interpretation and Herbrand Universe
-}
sfolInterpretsHerbrand : SetFOL -> List FormulaFOL -> List Term -> Maybe Bool
sfolInterpretsHerbrand fs iH uH =
    List.foldl (Maybe.map2 (&&)) (Just True) <| List.map (\f -> ffolInterpretsHerbrand f iH uH) fs


{-| It searches Herbrand Models of n-order from a opened formula.
-}
ffolHerbrandModels : FormulaFOL -> Int -> Maybe ( List Term, List (List FormulaFOL) )
ffolHerbrandModels f n =
    let
        uH =
            ffolHerbrandUniverse f n
    in
    let
        ms =
            Maybe.map (List.filter (\i -> Maybe.withDefault False <| ffolInterpretsHerbrand f i (Maybe.withDefault [] uH))) <| ffolHerbrandInterpretations f n
    in
    Maybe.map2 Tuple.pair uH ms


{-| It searches Herbrand Models of n-order from a set of opened formulas.
-}
sfolHerbrandModels : SetFOL -> Int -> Maybe ( List Term, List (List FormulaFOL) )
sfolHerbrandModels fs n =
    let
        uH =
            sfolHerbrandUniverse fs n
    in
    let
        ms =
            Maybe.map (List.filter (\i -> Maybe.withDefault False <| sfolInterpretsHerbrand fs i (Maybe.withDefault [] uH))) <| sfolHerbrandInterpretations fs n
    in
    Maybe.map2 Tuple.pair uH ms


{-| It calculates the n-order Herbrand Extension vinculated to an opened formula. That is it gives a set of propositional formulas partially equiconsistent with the FOL formula
-}
ffolHerbrandExtension : FormulaFOL -> Int -> Maybe (List FormulaPL)
ffolHerbrandExtension f n =
    let
        uH =
            ffolHerbrandUniverse f n
    in
    Maybe.map (herbrandExtensionAux f) uH


herbrandExtensionAux : FormulaFOL -> List Term -> List FormulaPL
herbrandExtensionAux f uH =
    let
        vs =
            FOL_SS.ffolVarSymbols f
    in
    let
        substitutions =
            List.map (\x -> List.map2 (\y z -> ( y, z )) vs x) <| cartesianProduct <| List.repeat (List.length vs) uH
    in
    List.map (\xs -> Maybe.withDefault PL_SS.Insat <| ffolTofpl <| FOL_SS.ffolApplySubstitution (Dict.fromList xs) f) substitutions


{-| It calculates the n-order Herbrand Extension vinculated to a set of opened formulas. That is it gives a set of propositional formulas partially equiconsistent with the FOL formula
-}
sfolHerbrandExtension : SetFOL -> Int -> Maybe SetPL
sfolHerbrandExtension fs n =
    Maybe.map (\uH -> List.concat <| List.map (\f -> herbrandExtensionAux f uH) fs) <| sfolHerbrandUniverse fs n


ffolTofpl : FormulaFOL -> Maybe FormulaPL
ffolTofpl f =
    case f of
        FOL_SS.Pred _ _ ->
            Just <| PL_SS.Atom ( FOL_SS.ffolToString f, [] )

        FOL_SS.Equal _ _ ->
            Nothing

        FOL_SS.Neg x ->
            Maybe.map PL_SS.Neg <| ffolTofpl x

        FOL_SS.Conj x y ->
            Maybe.map2 PL_SS.Conj (ffolTofpl x) (ffolTofpl y)

        FOL_SS.Disj x y ->
            Maybe.map2 PL_SS.Disj (ffolTofpl x) (ffolTofpl y)

        FOL_SS.Impl x y ->
            Maybe.map2 PL_SS.Impl (ffolTofpl x) (ffolTofpl y)

        FOL_SS.Equi x y ->
            Maybe.map2 PL_SS.Equi (ffolTofpl x) (ffolTofpl y)

        FOL_SS.Forall _ _ ->
            Nothing

        FOL_SS.Exists _ _ ->
            Nothing

        FOL_SS.Insat ->
            Just PL_SS.Insat

        FOL_SS.Taut ->
            Just PL_SS.Taut
