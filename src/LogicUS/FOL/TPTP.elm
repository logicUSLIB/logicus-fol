module LogicUS.FOL.TPTP exposing
    ( TPTPProblem, tptpProblem, ffolToTPTP
    , szsStatus
    )

{-| The module translates formulas to the [TPTP](https://www.tptp.org) syntax (FOF), the input language of most
automated theorem provers and model finders for first order logic, such as E, Vampire or the online service
SystemOnTPTP. It is meant for problems too big for the didactic algorithms of the library: the problem is sent to
an external prover and its answer (an SZS status) is read back.


# Problems

@docs TPTPProblem, tptpProblem, ffolToTPTP


# Answers

@docs szsStatus

-}

import Dict exposing (Dict)
import LogicUS.FOL.SyntaxSemantics exposing (FormulaFOL(..), Ident, SetFOL, Term(..), Variable)
import Set exposing (Set)


{-| A problem in TPTP syntax. `input` is the text to give to the prover and `symbols` maps each TPTP symbol back to
the identifier of the original formulas (TPTP requires functors in lower case, so `P` becomes `p`).
-}
type alias TPTPProblem =
    { input : String
    , symbols : Dict String Ident
    }


{-| It builds a TPTP problem from a set of axioms and, optionally, a conjecture.

  - With a conjecture, provers try to prove that it follows from the axioms (SZS status `Theorem`) or find a
    counter-model (`CounterSatisfiable`).
  - Without it, they decide whether the axioms are satisfiable (`Satisfiable`/`Unsatisfiable`).

```
tptpProblem { axioms = [ ffolRead "!A[X](P(X) -> Q(X))", ffolRead "P(a)" ], conjecture = Just (ffolRead "Q(a)") }
    |> .input
    == "fof(ax1, axiom, ![X]: (p(X) => q(X))).\nfof(ax2, axiom, p(a)).\nfof(goal, conjecture, q(a)).\n"
```

-}
tptpProblem : { axioms : SetFOL, conjecture : Maybe FormulaFOL } -> TPTPProblem
tptpProblem { axioms, conjecture } =
    let
        all =
            axioms ++ Maybe.withDefault [] (Maybe.map List.singleton conjecture)

        names =
            symbolNames all

        line role name f =
            "fof(" ++ name ++ ", " ++ role ++ ", " ++ formulaToTPTP names f ++ ").\n"
    in
    { input =
        String.concat (List.indexedMap (\i f -> line "axiom" ("ax" ++ String.fromInt (i + 1)) f) axioms)
            ++ (case conjecture of
                    Just g ->
                        line "conjecture" "goal" g

                    Nothing ->
                        ""
               )
    , symbols = Dict.fromList (List.map (\( key, n ) -> ( n, originalIdent key )) (Dict.toList names))
    }


{-| It translates a single formula to TPTP syntax (symbols renamed as in `tptpProblem`).

    ffolToTPTP (ffolRead "!A[X] !E[Y] (s(X, Y) = e)") == "![X]: ?[Y]: (s(X, Y) = e)"

-}
ffolToTPTP : FormulaFOL -> String
ffolToTPTP f =
    formulaToTPTP (symbolNames [ f ]) f


{-| It extracts the SZS status from the output of a prover (e.g. `Theorem`, `CounterSatisfiable`, `Unsatisfiable`,
`Satisfiable`, `Timeout`, `GaveUp`), if there is one.

    szsStatus "...\n# SZS status Theorem for problem.p\n..." == Just "Theorem"

-}
szsStatus : String -> Maybe String
szsStatus output =
    output
        |> String.lines
        |> List.filterMap
            (\l ->
                case String.words (String.replace "%" " " (String.replace "#" " " l)) of
                    "SZS" :: "status" :: status :: _ ->
                        Just status

                    _ ->
                        Nothing
            )
        |> List.head



-- SYMBOLS


type Kind
    = Predicate
    | Function


{-| TPTP names for every predicate and function symbol, keyed by `keyOf`. Names are lower case, readable and
unique: a clash (e.g. predicate `P` and constant `p`) is solved with a numeric suffix.
-}
symbolNames : SetFOL -> Dict Ident String
symbolNames fs =
    fs
        |> List.concatMap formulaSymbols
        |> uniqueKeep
        |> List.foldl
            (\( kind, id ) ( acc, used ) ->
                let
                    name =
                        freshName (lowerWord id) used 1
                in
                ( Dict.insert (keyOf kind id) name acc, Set.insert name used )
            )
            ( Dict.empty, Set.empty )
        |> Tuple.first


{-| Predicates and functions live in different name spaces in LogicUS, so the key carries the kind.
-}
keyOf : Kind -> Ident -> Ident
keyOf kind ( s, is ) =
    case kind of
        Predicate ->
            ( "p\u{0000}" ++ s, is )

        Function ->
            ( "f\u{0000}" ++ s, is )


originalIdent : Ident -> Ident
originalIdent ( k, is ) =
    ( String.dropLeft 2 k, is )


lookupName : Dict Ident String -> Kind -> Ident -> String
lookupName names kind id =
    Dict.get (keyOf kind id) names |> Maybe.withDefault (lowerWord id)


freshName : String -> Set String -> Int -> String
freshName base used i =
    let
        candidate =
            if i == 1 then
                base

            else
                base ++ "_" ++ String.fromInt i
    in
    if Set.member candidate used then
        freshName base used (i + 1)

    else
        candidate


uniqueKeep : List ( Kind, Ident ) -> List ( Kind, Ident )
uniqueKeep xs =
    List.foldl
        (\x acc ->
            if List.member x acc then
                acc

            else
                acc ++ [ x ]
        )
        []
        xs


{-| A TPTP `lower_word`: a lower case letter followed by letters, digits and underscores.
-}
lowerWord : Ident -> String
lowerWord ( s, is ) =
    let
        clean =
            String.toList s
                |> List.map
                    (\c ->
                        if Char.isAlphaNum c && Char.toCode c < 128 then
                            String.fromChar c

                        else if c == '_' then
                            "_"

                        else
                            "u" ++ String.fromInt (Char.toCode c)
                    )
                |> String.concat

        first =
            String.left 1 clean

        start =
            if String.all Char.isAlpha first && first /= "" then
                String.toLower first ++ String.dropLeft 1 clean

            else
                "s" ++ clean
    in
    start ++ indicesSuffix is


indicesSuffix : List Int -> String
indicesSuffix is =
    String.concat (List.map (\i -> "_" ++ String.fromInt i) is)


{-| A TPTP `upper_word` for a variable.
-}
varName : Variable -> String
varName ( s, is, prime ) =
    let
        clean =
            String.filter (\c -> Char.isAlphaNum c && Char.toCode c < 128) s

        start =
            case String.uncons clean of
                Just ( c, rest ) ->
                    String.fromChar (Char.toUpper c) ++ rest

                Nothing ->
                    "V"
    in
    start
        ++ indicesSuffix is
        ++ (if prime > 0 then
                "_p" ++ String.fromInt prime

            else
                ""
           )


termSymbols : Term -> List ( Kind, Ident )
termSymbols t =
    case t of
        Var _ ->
            []

        Func id ts ->
            ( Function, id ) :: List.concatMap termSymbols ts


formulaSymbols : FormulaFOL -> List ( Kind, Ident )
formulaSymbols f =
    case f of
        Pred id ts ->
            ( Predicate, id ) :: List.concatMap termSymbols ts

        Equal t1 t2 ->
            termSymbols t1 ++ termSymbols t2

        Neg g ->
            formulaSymbols g

        Conj g h ->
            formulaSymbols g ++ formulaSymbols h

        Disj g h ->
            formulaSymbols g ++ formulaSymbols h

        Impl g h ->
            formulaSymbols g ++ formulaSymbols h

        Equi g h ->
            formulaSymbols g ++ formulaSymbols h

        Exists _ g ->
            formulaSymbols g

        Forall _ g ->
            formulaSymbols g

        _ ->
            []



-- PRINTING


termToTPTP : Dict Ident String -> Term -> String
termToTPTP names t =
    case t of
        Var v ->
            varName v

        Func id [] ->
            lookupName names Function id

        Func id ts ->
            lookupName names Function id ++ "(" ++ String.join ", " (List.map (termToTPTP names) ts) ++ ")"


{-| Formulas are printed with explicit parentheses around every binary connective, so no precedence rule of TPTP
matters.
-}
formulaToTPTP : Dict Ident String -> FormulaFOL -> String
formulaToTPTP names f =
    let
        go g =
            case g of
                Pred id [] ->
                    lookupName names Predicate id

                Pred id ts ->
                    lookupName names Predicate id ++ "(" ++ String.join ", " (List.map (termToTPTP names) ts) ++ ")"

                Equal t1 t2 ->
                    termToTPTP names t1 ++ " = " ++ termToTPTP names t2

                Neg (Equal t1 t2) ->
                    termToTPTP names t1 ++ " != " ++ termToTPTP names t2

                Neg h ->
                    "~ " ++ unary h

                Conj a b ->
                    "(" ++ go a ++ " & " ++ go b ++ ")"

                Disj a b ->
                    "(" ++ go a ++ " | " ++ go b ++ ")"

                Impl a b ->
                    "(" ++ go a ++ " => " ++ go b ++ ")"

                Equi a b ->
                    "(" ++ go a ++ " <=> " ++ go b ++ ")"

                Forall v h ->
                    "![" ++ varName v ++ "]: " ++ unary h

                Exists v h ->
                    "?[" ++ varName v ++ "]: " ++ unary h

                Taut ->
                    "$true"

                Insat ->
                    "$false"

        -- operands of ~ and of quantifiers must be unitary: wrap equalities
        unary h =
            case h of
                Equal _ _ ->
                    "(" ++ go h ++ ")"

                Neg (Equal _ _) ->
                    "(" ++ go h ++ ")"

                _ ->
                    go h
    in
    let
        out =
            go f
    in
    -- strip one redundant outer pair of parentheses for readability
    if String.startsWith "(" out && String.endsWith ")" out && balancedInside (String.slice 1 -1 out) then
        String.slice 1 -1 out

    else
        out


balancedInside : String -> Bool
balancedInside s =
    String.foldl
        (\c ( depth, ok ) ->
            if not ok then
                ( depth, ok )

            else if c == '(' then
                ( depth + 1, ok )

            else if c == ')' then
                ( depth - 1, depth - 1 >= 0 )

            else
                ( depth, ok )
        )
        ( 0, True )
        s
        |> (\( d, ok ) -> ok && d == 0)
