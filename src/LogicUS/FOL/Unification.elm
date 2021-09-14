module LogicUS.FOL.Unification exposing (termMGU, termsMGU, atomsMGU)

{-| This module allows to calculate the Maximum General Unificator (MGU)


# MGU

@docs termMGU, termsMGU, atomsMGU

-}

import Dict exposing (..)
import List
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), Substitution, Term(..))


{-| It calculates a Maximum General Unificator between two terms, if it exists.
-}
termMGU : Term -> Term -> Maybe Substitution
termMGU t1 t2 =
    case t1 of
        Var x ->
            case t2 of
                Var y ->
                    if x == y then
                        Just Dict.empty

                    else
                        Just <| Dict.fromList [ ( x, t2 ) ]

                Func _ _ ->
                    if List.member x (FOL_SS.termVarSymbols t2) then
                        Nothing

                    else
                        Just <| Dict.fromList [ ( x, t2 ) ]

        Func f fts ->
            case t2 of
                Var y ->
                    if List.member y (FOL_SS.termVarSymbols t1) then
                        Nothing

                    else
                        Just <| Dict.fromList [ ( y, t1 ) ]

                Func g gts ->
                    if f == g then
                        termsMGU fts gts

                    else
                        Nothing


{-| It calculates a Maximum General Unificator for a list of terms if it exists.
-}
termsMGU : List Term -> List Term -> Maybe Substitution
termsMGU lt1 lt2 =
    case ( lt1, lt2 ) of
        ( [], [] ) ->
            Just Dict.empty

        ( _ :: _, [] ) ->
            Nothing

        ( [], _ :: _ ) ->
            Nothing

        ( t :: ts, r :: rs ) ->
            let
                s1_ =
                    termMGU t r
            in
            case s1_ of
                Just s1 ->
                    let
                        s2_ =
                            termsMGU (List.map (\x -> FOL_SS.termApplySubstitution s1 x) ts) (List.map (\x -> FOL_SS.termApplySubstitution s1 x) rs)
                    in
                    Maybe.map finalizelistTermMGU (Maybe.map (\s -> FOL_SS.substitutionComposition s s1) s2_)

                _ ->
                    Nothing


finalizelistTermMGU : Substitution -> Substitution
finalizelistTermMGU s =
    let
        sf =
            Dict.filter (\x tr -> Var x /= tr) s
    in
    case List.filter (\( x, _ ) -> List.member x (FOL_SS.termsVarSymbols <| Dict.values <| Dict.remove x sf)) <| Dict.toList sf of
        [] ->
            sf

        ( k, v ) :: _ ->
            FOL_SS.substitutionComposition
                (Dict.remove k sf)
                (Dict.singleton k v)


{-| It calculates a Maximum General Unificator for two atoms if it exists.
-}
atomsMGU : FormulaFOL -> FormulaFOL -> Maybe Substitution
atomsMGU a1 a2 =
    case ( a1, a2 ) of
        ( Pred p1 ts1, Pred p2 ts2 ) ->
            if p1 == p2 then
                termsMGU ts1 ts2

            else
                Nothing

        _ ->
            Nothing
