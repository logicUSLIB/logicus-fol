module LogicUS.FOL.Clauses exposing
    ( ClauseFOLAtom(..), ClauseFOLLiteral, ClauseFOL, ClauseFOLSet
    , cfolAtomVarSymbols, cfolVarSymbols, cfolAtomSymbol, cfolLiteralSymbols, cfolAtomApplySubstitution, cfolApplySubstitution, cfolSort, cfolUnion, cfolSubsumes, cfolIsTautology, cfolIsPositive, cfolIsNegative, csfolRemoveEqClauses, csfolRemoveTautClauses, csfolRemoveSubsumedClauses
    , clauseFOLAtomToAtom, clauseFOLLitToLiteral, cfolFromCNF, ffolToClauses, sfolToClauses
    , cfolReadFromString, cfolReadExtraction, cfolToInputString
    , cfolToString, cfolToMathString, csfolToString, csfolToMathString
    )

{-| The module provides the tools for express formulas in their Clausal Form.


# Types

@docs ClauseFOLAtom, ClauseFOLLiteral, ClauseFOL, ClauseFOLSet


# Work with clauses

@docs cfolAtomVarSymbols, cfolVarSymbols, cfolAtomSymbol, cfolLiteralSymbols, cfolAtomApplySubstitution, cfolApplySubstitution, cfolSort, cfolUnion, cfolSubsumes, cfolIsTautology, cfolIsPositive, cfolIsNegative, csfolRemoveEqClauses, csfolRemoveTautClauses, csfolRemoveSubsumedClauses


# Formulas and Clauses

@docs clauseFOLAtomToAtom, clauseFOLLitToLiteral, cfolFromCNF, ffolToClauses, sfolToClauses


# Clauses Parser

@docs cfolReadFromString, cfolReadExtraction, cfolToInputString


# Clauses Representation

@docs cfolToString, cfolToMathString, csfolToString, csfolToMathString

-}

--=========--
-- IMPORTS --
--=========--

import LogicUS.AUX.AuxiliarFuctions exposing (cleanSpaces, uniqueConcatList)
import LogicUS.FOL.NormalForms as FOL_NF
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), SetFOL, Substitution, Term(..), Variable)
import Parser exposing ((|.), (|=), Parser, Trailing(..))
import Set exposing (Set)



--=======--
-- TYPES --
--=======--


{-| It represent An Atom of a clause as a Predicate (P) or as a equality (E)
-}
type ClauseFOLAtom
    = P ( String, List Int ) (List Term)
    | Eq Term Term


{-| It represent a literal of a clause as a tuple with the symbol of the literal (string) and the sign of the literal (False:negative literal, True:positive literal).
-}
type alias ClauseFOLLiteral =
    ( ClauseFOLAtom, Bool )


{-| It represent a set of clause literals.
-}
type alias ClauseFOL =
    List ClauseFOLLiteral


{-| It represent a set of ClauseFOL
-}
type alias ClauseFOLSet =
    List ClauseFOL



-----------------------
-- Auxiliar functions -
-----------------------
-- It compare two clause literals by the comparision of their symbols and in equality conditions comparing their signs (False < True).


compareClauseFOLAtoms : ClauseFOLAtom -> ClauseFOLAtom -> Order
compareClauseFOLAtoms a1 a2 =
    case a1 of
        P ( s1, is1 ) _ ->
            case a2 of
                P ( s2, is2 ) _ ->
                    case compare s1 s2 of
                        LT ->
                            LT

                        GT ->
                            GT

                        EQ ->
                            compare is1 is2

                Eq _ _ ->
                    LT

        Eq _ _ ->
            case a2 of
                P _ _ ->
                    GT

                Eq _ _ ->
                    EQ


compareClauseFOLLiterals : ClauseFOLLiteral -> ClauseFOLLiteral -> Order
compareClauseFOLLiterals ( a1, sign1 ) ( a2, sign2 ) =
    if sign1 then
        if sign2 then
            compareClauseFOLAtoms a1 a2

        else
            LT

    else if sign2 then
        GT

    else
        compareClauseFOLAtoms a1 a2



-------------------
-- Work functions -
-------------------


{-| It gives the variables that appears in a clause atom
-}
cfolAtomVarSymbols : ClauseFOLAtom -> List Variable
cfolAtomVarSymbols ca =
    case ca of
        P _ ts ->
            FOL_SS.termsVarSymbols ts

        Eq t1 t2 ->
            FOL_SS.termsVarSymbols [ t1, t2 ]


{-| It gives the symbol of the predicate of the atom ("=" is reserved for equality)
-}
cfolAtomSymbol : ClauseFOLAtom -> ( String, List Int )
cfolAtomSymbol ca =
    case ca of
        P x _ ->
            x

        Eq _ _ ->
            ( "=", [] )


{-| It gives the variables that appears in a clause
-}
cfolVarSymbols : ClauseFOL -> Set Variable
cfolVarSymbols c =
    Set.fromList <| List.concat <| List.map (cfolAtomVarSymbols << Tuple.first) c


{-| It gives the symbols of literals that appears in a clause
-}
cfolLiteralSymbols : ClauseFOL -> Set ( String, List Int )
cfolLiteralSymbols c =
    Set.fromList <| List.map (cfolAtomSymbol << Tuple.first) c


{-| It applies a Substitution over a clause atom
-}
cfolAtomApplySubstitution : Substitution -> ClauseFOLAtom -> ClauseFOLAtom
cfolAtomApplySubstitution s ca =
    case ca of
        P x ts ->
            P x (List.map (FOL_SS.termApplySubstitution s) ts)

        Eq t1 t2 ->
            Eq (FOL_SS.termApplySubstitution s t1) (FOL_SS.termApplySubstitution s t2)


{-| It applies a substitution over a clause
-}
cfolApplySubstitution : Substitution -> ClauseFOL -> ClauseFOL
cfolApplySubstitution s c =
    List.map (\( a, sign ) -> ( cfolAtomApplySubstitution s a, sign )) c


{-| It sorts the literals of the clause by alphabetical order.
-}
cfolSort : ClauseFOL -> ClauseFOL
cfolSort cs =
    List.sortWith compareClauseFOLLiterals cs


{-| It calculates the union of two clauses
-}
cfolUnion : ClauseFOL -> ClauseFOL -> ClauseFOL
cfolUnion c1 c2 =
    List.sortWith compareClauseFOLLiterals <| uniqueConcatList [] (c1 ++ c2)


{-| Indicates if the first clause subsumes the second, that is, if the first is entirely contained in the second.
-}
cfolSubsumes : ClauseFOL -> ClauseFOL -> Bool
cfolSubsumes c1 c2 =
    List.all (\x -> List.member x c2) c1


{-| Indicates if the clause is a tautology, that is if it contains a literal and its complement.
-}
cfolIsTautology : ClauseFOL -> Bool
cfolIsTautology c =
    List.any (\( a, sign ) -> List.member ( a, not sign ) c) c


{-| Indicates if the clause is enterly positive, this is with all its literals positive
-}
cfolIsPositive : ClauseFOL -> Bool
cfolIsPositive c =
    List.all Tuple.second c


{-| Indicates if the clause is enterly negative, this is with all its literals negative
-}
cfolIsNegative : ClauseFOL -> Bool
cfolIsNegative c =
    List.all (not << Tuple.second) c


{-| It removes clauses that are equal from a list of clauses
-}
csfolRemoveEqClauses : ClauseFOLSet -> ClauseFOLSet
csfolRemoveEqClauses xs =
    uniqueConcatList [] <| List.map cfolSort xs


{-| It removes clauses that are tautological clauses
-}
csfolRemoveTautClauses : ClauseFOLSet -> ClauseFOLSet
csfolRemoveTautClauses cs =
    List.filter (not << cfolIsTautology) <| List.map cfolSort cs


{-| It removes clauses that are subsumed by other from the list
-}
csfolRemoveSubsumedClauses : ClauseFOLSet -> ClauseFOLSet
csfolRemoveSubsumedClauses cs =
    List.foldl
        (\c ac ->
            if List.any (\x -> cfolSubsumes x c) ac then
                ac

            else
                List.filter (not << cfolSubsumes c) ac ++ [ c ]
        )
        []
        (List.map cfolSort cs)


{-| It converts a ClauseFOLAtom to an Atom (FormulaFOL)
-}
clauseFOLAtomToAtom : ClauseFOLAtom -> FormulaFOL
clauseFOLAtomToAtom ca =
    case ca of
        P a ts ->
            Pred a ts

        Eq t1 t2 ->
            Equal t1 t2


{-| It converts a ClauseFOLLiteral to a Literal (FormulaFOL)
-}
clauseFOLLitToLiteral : ClauseFOLLiteral -> FormulaFOL
clauseFOLLitToLiteral ( a, sign ) =
    case a of
        P p ts ->
            if sign then
                Pred p ts

            else
                Neg (Pred p ts)

        Eq t1 t2 ->
            if sign then
                Equal t1 t2

            else
                Neg (Equal t1 t2)



-- From formulas to clauses


{-| It pass a CNF formula (opened) to a Set of clausses
-}
cfolFromCNF : FormulaFOL -> Maybe ClauseFOLSet
cfolFromCNF f =
    let
        cfolFromCNFAux g =
            case g of
                Pred p ts ->
                    Just [ [ ( P p ts, True ) ] ]

                Neg (Pred p ts) ->
                    Just [ [ ( P p ts, False ) ] ]

                Equal t1 t2 ->
                    Just [ [ ( Eq t1 t2, True ) ] ]

                Neg (Equal t1 t2) ->
                    Just [ [ ( Eq t1 t2, False ) ] ]

                Disj g1 g2 ->
                    Maybe.map (\c -> [ c ]) <|
                        Maybe.map cfolSort <|
                            Maybe.map2 uniqueConcatList
                                (Maybe.map List.concat <| cfolFromCNFAux g1)
                                (Maybe.map List.concat <| cfolFromCNFAux g2)

                Insat ->
                    Just [ [] ]

                Taut ->
                    Just []

                _ ->
                    Nothing
    in
    case f of
        Conj f1 f2 ->
            Maybe.map2 uniqueConcatList (cfolFromCNF f1) (cfolFromCNF f2)

        Pred p ts ->
            Just [ [ ( P p ts, True ) ] ]

        Neg (Pred p ts) ->
            Just [ [ ( P p ts, False ) ] ]

        Equal t1 t2 ->
            Just [ [ ( Eq t1 t2, True ) ] ]

        Neg (Equal t1 t2) ->
            Just [ [ ( Eq t1 t2, False ) ] ]

        Disj f1 f2 ->
            Maybe.map (\c -> [ c ]) <|
                Maybe.map cfolSort <|
                    Maybe.map2 uniqueConcatList
                        (Maybe.map List.concat <| cfolFromCNFAux f1)
                        (Maybe.map List.concat <| cfolFromCNFAux f2)

        Insat ->
            Just [ [] ]

        Taut ->
            Just []

        _ ->
            Nothing


{-| Express a formula as a Set of clauses.
-}
ffolToClauses : FormulaFOL -> ClauseFOLSet
ffolToClauses f =
    Maybe.withDefault [ [] ] <| cfolFromCNF <| FOL_NF.ffolToCNF f


{-| Express a set of formulas as a Set of clauses.
-}
sfolToClauses : SetFOL -> ClauseFOLSet
sfolToClauses fs =
    List.foldl (\f ac -> uniqueConcatList ac <| Maybe.withDefault [ [] ] <| cfolFromCNF f) [] <| FOL_NF.sfolToCNF fs



--========--
-- PARSER --
--========--


{-| It reads the Cc from a string. It returns a tuple with may be a formula (if it can be read it) and a message of error it it cannot.
-}
cfolReadFromString : String -> ( Maybe ClauseFOL, String, String )
cfolReadFromString x =
    let
        clean_x =
            cleanSpaces x
    in
    case String.left 1 <| clean_x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        "{" ->
            case Parser.run cfolParser clean_x of
                Ok y ->
                    ( (Maybe.Just << cfolSort) y, "", "" )

                Err y ->
                    ( Maybe.Nothing, clean_x, "Error: " ++ String.replace "\"" "'" (Debug.toString y) )

        _ ->
            case Parser.run cfolParser ("{" ++ clean_x ++ "}") of
                Ok y ->
                    ( Maybe.Just y, "", "" )

                Err y ->
                    ( Maybe.Nothing, "{" ++ clean_x ++ "}", "Error: " ++ String.replace "\"" "'" (Debug.toString y) )


{-| It extracts the clause readed. If it is Nothing then it returns an empty clause
-}
cfolReadExtraction : ( Maybe ClauseFOL, String, String ) -> ClauseFOL
cfolReadExtraction ( c, _, _ ) =
    cfolSort <| Maybe.withDefault [] c


{-| It gives the corresponding input syntax of a clause
-}
cfolToInputString : ClauseFOL -> String
cfolToInputString c =
    case c of
        [] ->
            "{}"

        _ ->
            "{" ++ (String.join "," <| List.map (FOL_SS.ffolToInputString << clauseFOLLitToLiteral) <| cfolSort c) ++ "}"



--- Parser Builder Functions
-- It defines the syntax of a propositional variable that can be subscripting or not


folVariableParser : Parser Variable
folVariableParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable folVarSubSuperIndexedParser
        , Parser.succeed identity
            |= Parser.backtrackable folVarSubindexedParser
        , Parser.succeed identity
            |= Parser.backtrackable folVarSupindexedParser
        , Parser.succeed (\x -> ( x, [], 0 ))
            |= folTermNameParser
        ]


folVarSubindexedParser : Parser Variable
folVarSubindexedParser =
    Parser.succeed (\x y -> ( x, y, 0 ))
        |= folTermNameParser
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }


folVarSupindexedParser : Parser Variable
folVarSupindexedParser =
    Parser.succeed (\x y -> ( x, [], y ))
        |= folTermNameParser
        |. Parser.symbol "^{"
        |= Parser.int
        |. Parser.symbol "}"


folVarSubSuperIndexedParser : Parser Variable
folVarSubSuperIndexedParser =
    Parser.succeed (\x y z -> ( x, y, z ))
        |= folTermNameParser
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }
        |. Parser.symbol "^{"
        |= Parser.int
        |. Parser.symbol "}"


folTermNameParser : Parser String
folTermNameParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isLower
        |. Parser.chompWhile Char.isAlpha
        |> Parser.getChompedString


folTermIdentifierParser : Parser ( String, List Int )
folTermIdentifierParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable folTermIdentifierSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= folTermNameParser
        ]


folTermIdentifierSubindexedParser : Parser ( String, List Int )
folTermIdentifierSubindexedParser =
    Parser.succeed Tuple.pair
        |= folTermNameParser
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }


folPredNameParser : Parser String
folPredNameParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isUpper
        |. Parser.chompWhile Char.isAlpha
        |> Parser.getChompedString


folPredIdentifierParser : Parser ( String, List Int )
folPredIdentifierParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable folPredIdentifierSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= folPredNameParser
        ]


folPredIdentifierSubindexedParser : Parser ( String, List Int )
folPredIdentifierSubindexedParser =
    Parser.succeed Tuple.pair
        |= folPredNameParser
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }


folTermParser : Parser Term
folTermParser =
    Parser.oneOf
        [ Parser.succeed Func
            |. Parser.symbol "_"
            |= folTermIdentifierParser
            |= folListTermParser
        , Parser.succeed Var
            |= folVariableParser
        ]


folListTermParser : Parser (List Term)
folListTermParser =
    Parser.oneOf
        [ Parser.succeed identity
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> folEnumerationTermParser)
            |. Parser.symbol ")"
        , Parser.succeed []
        ]


folEnumerationTermParser : Parser (List Term)
folEnumerationTermParser =
    folTermParser |> Parser.andThen (folEnumerationTermParserAux [])


folEnumerationTermParserAux : List Term -> Term -> Parser (List Term)
folEnumerationTermParserAux ts t =
    Parser.oneOf
        [ Parser.succeed identity
            |. Parser.symbol ","
            |= folTermParser
            |> Parser.andThen (\newt -> folEnumerationTermParserAux (ts ++ [ newt ]) t)
        , Parser.lazy (\_ -> Parser.succeed (t :: ts))
        ]


cfolParser : Parser ClauseFOL
cfolParser =
    Parser.succeed identity
        |= cfolParserAux
        |. Parser.end


cfolParserAux : Parser ClauseFOL
cfolParserAux =
    Parser.sequence
        { start = "{"
        , separator = ","
        , end = "}"
        , spaces = Parser.spaces
        , item = literalParser
        , trailing = Optional
        }


literalParser : Parser ClauseFOLLiteral
literalParser =
    Parser.oneOf
        [ Parser.succeed (\t1 t2 -> ( Eq t1 t2, False ))
            |. Parser.oneOf
                [ Parser.symbol "¬("
                , Parser.symbol "-("
                ]
            |= folTermParser
            |. Parser.symbol "="
            |= folTermParser
            |. Parser.symbol ")"
        , Parser.succeed (\x ts -> ( P x ts, False ))
            |. Parser.oneOf
                [ Parser.symbol "¬"
                , Parser.symbol "-"
                ]
            |= folPredIdentifierParser
            |= folListTermParser
        , Parser.succeed (\x ts -> ( P x ts, True ))
            |= folPredIdentifierParser
            |= folListTermParser
        , Parser.succeed (\t1 t2 -> ( Eq t1 t2, True ))
            |= folTermParser
            |. Parser.symbol "="
            |= folTermParser
        ]



--================--
-- REPRESENTATION --
--================--


{-| It generates the String representation of a ClauseFOL using unicode symbols.
-}
cfolToString : ClauseFOL -> String
cfolToString c =
    if List.isEmpty c then
        "□"

    else
        "{" ++ (String.join "," <| List.map (FOL_SS.ffolToString << clauseFOLLitToLiteral) <| cfolSort c) ++ "}"


{-| It generates the Latex string of a ClauseFOL. The result requires a math enviroment to be displayed.
-}
cfolToMathString : ClauseFOL -> String
cfolToMathString c =
    if List.isEmpty c then
        "\\Box"

    else
        "\\{" ++ (String.join "," <| List.map (FOL_SS.ffolToMathString << clauseFOLLitToLiteral) <| cfolSort c) ++ "\\}"


{-| It generates the String representation of a Set of Clauses using unicode symbols.
-}
csfolToString : ClauseFOLSet -> String
csfolToString cs =
    "{" ++ (String.join "," <| List.map (cfolToString << cfolSort) cs) ++ "}"


{-| It generates the Latex string of a Set of Clauses. The result requires a math enviroment to be displayed.
-}
csfolToMathString : ClauseFOLSet -> String
csfolToMathString cs =
    "\\lbrace" ++ (String.join ", \\, " <| List.map (\x -> (cfolToMathString << cfolSort) x) cs) ++ "\\rbrace"
