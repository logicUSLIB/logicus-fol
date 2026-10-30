module LogicUS.FOL.AuxiliarFuctions exposing (cleanSpaces, listRemoveAll, parserErrorToString, powerset, replaceBySubscript, replaceBySuperscript, subscriptLetters, uniqueConcatList)

import Dict exposing (Dict)
import List.Extra as LE
import Parser exposing (DeadEnd, Problem(..))
import String.Extra as SE



-- It concatenates two lists avoiding elements from second list that are in the first one.


uniqueConcatList : List a -> List a -> List a
uniqueConcatList xs ys =
    List.foldl
        (\x ac ->
            if List.member x ac then
                ac

            else
                ac ++ [ x ]
        )
        xs
        ys


listRemoveAll : List a -> List a -> List a
listRemoveAll l1 l2 =
    List.filter (\x -> not <| List.member x l2) l1



-- It generates all possible sublists of a list of elements


powerset : List a -> List (List a)
powerset =
    List.foldr (\x acc -> acc ++ List.map ((::) x) acc) [ [] ]



-- It removes the spaces of a string


cleanSpaces : String -> String
cleanSpaces x =
    String.join "" <| String.split " " <| SE.clean x



-- It replaces numbers in a string by the proper subscript.


replaceBySubscript : String -> String
replaceBySubscript s =
    let
        dictSubscripts =
            Dict.fromList [ ( '0', '₀' ), ( '1', '₁' ), ( '2', '₂' ), ( '3', '₃' ), ( '4', '₄' ), ( '5', '₅' ), ( '6', '₆' ), ( '7', '₇' ), ( '8', '₈' ), ( '9', '₉' ), ( ',', ' ' ) ]
    in
    String.fromList <| List.map (\x -> Maybe.withDefault x <| Dict.get x dictSubscripts) <| String.toList s


replaceBySuperscript : String -> String
replaceBySuperscript s =
    let
        dictSuperscripts =
            Dict.fromList [ ( '0', '⁰' ), ( '1', '¹' ), ( '2', '²' ), ( '3', '³' ), ( '4', '⁴' ), ( '5', '⁵' ), ( '6', '⁶' ), ( '7', '⁷' ), ( '8', '⁸' ), ( '9', '⁹' ) ]
    in
    String.fromList <| List.map (\x -> Maybe.withDefault x <| Dict.get x dictSuperscripts) <| String.toList s


subscriptLetters : Dict Char Char
subscriptLetters =
    Dict.fromList <| LE.zip [ 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'r', 's', 't', 'u', 'v', 'w', 'x' ] [ 'ₕ', 'ᵢ', 'ⱼ', 'ₖ', 'ₗ', 'ₘ', 'ₙ', 'ₒ', 'ₚ', 'ᵣ', 'ₛ', 'ₜ', 'ᵤ', 'ᵥ', 'ᵥ', 'ᵥ', 'ₓ' ]


-- It gives a readable message for a parser failure: the text read before the error (spaces are removed
-- before parsing, so a column number would not match what the user typed) and what was expected there.
-- `wrap` is the number of characters added before the user's input (e.g. an opening parenthesis).


parserErrorToString : String -> Int -> List DeadEnd -> String
parserErrorToString input wrap deadEnds =
    let
        furthest =
            deadEnds |> List.map .col |> List.maximum |> Maybe.withDefault 1

        expected =
            deadEnds
                |> List.filter (\d -> d.col == furthest)
                |> List.filterMap (.problem >> problemToString)
                |> LE.unique

        -- the wrapper adds `wrap` characters on each side of the user's input
        before =
            String.slice wrap (min (furthest - 1) (String.length input - wrap)) input

        location =
            if String.isEmpty before then
                "Syntax error at the beginning"

            else
                "Syntax error after \"" ++ before ++ "\""
    in
    case expected of
        [] ->
            location

        [ e ] ->
            location ++ ": expected " ++ e

        es ->
            location ++ ": expected one of " ++ String.join ", " es


problemToString : Problem -> Maybe String
problemToString p =
    case p of
        Expecting s ->
            Just ("'" ++ s ++ "'")

        ExpectingSymbol s ->
            Just ("'" ++ s ++ "'")

        ExpectingKeyword s ->
            Just ("'" ++ s ++ "'")

        ExpectingInt ->
            Just "an integer"

        ExpectingNumber ->
            Just "a number"

        ExpectingFloat ->
            Just "a number"

        ExpectingHex ->
            Just "a number"

        ExpectingOctal ->
            Just "a number"

        ExpectingBinary ->
            Just "a number"

        ExpectingVariable ->
            Just "a symbol"

        ExpectingEnd ->
            Just "the end of the input"

        UnexpectedChar ->
            Just "a valid character"

        Problem s ->
            Just s

        BadRepeat ->
            Nothing
