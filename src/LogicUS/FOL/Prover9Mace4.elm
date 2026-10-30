module LogicUS.FOL.Prover9Mace4 exposing
    ( P9M4Problem, p9m4Problem
    , prover9Result, mace4Models
    )

{-| The module connects the library with [Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/): Prover9
searches for proofs in first order logic with equality, and Mace4 searches for finite models and counter-models.

The functions build the input file for both programs and read their answers back. Mace4 models are returned as
`L_Structure Int`, so they can be shown and checked with the rest of the library (e.g. `ffolValuation`).

Running the programs is up to the application (a server, a WebAssembly build, a local installation...).


# Problems

@docs P9M4Problem, p9m4Problem


# Answers

@docs prover9Result, mace4Models

-}

import Dict exposing (Dict)
import List.Extra as LE
import LogicUS.FOL.SyntaxSemantics exposing (FormulaFOL(..), Ident, L_Structure, SetFOL, Term(..), Variable)
import Parser exposing ((|.), (|=), Parser)
import Set exposing (Set)


{-| An input file for Prover9 and Mace4. `symbols` maps the names used in the file back to the identifiers of the
original formulas.
-}
type alias P9M4Problem =
    { input : String
    , symbols : Dict String Ident
    , arities : Dict String ( Bool, Int )
    }


{-| It builds the input file from a list of assumptions and a list of goals. Prover9 tries to prove the goals from the
assumptions; Mace4 searches for a model of the assumptions that falsifies the goals (a counter-model). With no goals,
Mace4 simply searches for models of the assumptions.

    p9m4Problem { assumptions = [ ffolRead "!A[X](P(X) -> Q(X))", ffolRead "P(a)" ], goals = [ ffolRead "Q(a)" ] }
        |> .input
        == "formulas(assumptions).\n(all X (P(X) -> Q(X))).\nP(a).\nend_of_list.\n\nformulas(goals).\nQ(a).\nend_of_list.\n"

-}
p9m4Problem : { assumptions : SetFOL, goals : SetFOL } -> P9M4Problem
p9m4Problem { assumptions, goals } =
    let
        names =
            symbolNames (assumptions ++ goals)

        section title fs =
            "formulas(" ++ title ++ ").\n" ++ String.concat (List.map (\f -> formulaToP9 names f ++ ".\n") fs) ++ "end_of_list.\n"
    in
    { input =
        section "assumptions" assumptions
            ++ (if List.isEmpty goals then
                    ""

                else
                    "\n" ++ section "goals" goals
               )
    , symbols = Dict.fromList (List.map (\( key, n ) -> ( n, originalIdent key )) (Dict.toList names))
    , arities =
        (assumptions ++ goals)
            |> List.concatMap formulaArities
            |> List.map (\( kind, id, k ) -> ( lookupName names kind id, ( kind == Predicate, k ) ))
            |> Dict.fromList
    }


{-| It reads the result of a Prover9 run: `Just True` if a proof was found, `Just False` if the search ended without
one (`SEARCH FAILED`, which does not mean that the goal is false), and `Nothing` if the output says neither (e.g. it
was stopped by a time limit).
-}
prover9Result : String -> Maybe Bool
prover9Result output =
    if String.contains "THEOREM PROVED" output then
        Just True

    else if String.contains "SEARCH FAILED" output then
        Just False

    else
        Nothing


{-| It extracts the models of a Mace4 output (the `interpretation(...)` blocks in its standard format) as structures
for the symbols of the problem. Note that Mace4 only searches domains of size 2 or more. The elements of the universe are `0, 1, ..., n-1`. Mace4 leaves out the symbols that
its simplifications made irrelevant; they get an arbitrary interpretation (constant `0`, empty relations), which does
not change the truth of the problem's formulas.

    mace4Models problem mace4Output
        |> List.map (ffolValuation (ffolRead "Q(a)"))
        == [ Just False ]

-}
mace4Models : P9M4Problem -> String -> List (L_Structure Int)
mace4Models problem output =
    output
        |> String.split "interpretation("
        |> List.drop 1
        |> List.filterMap (\block -> Parser.run interpretationParser ("interpretation(" ++ block) |> Result.toMaybe)
        |> List.map (\( n, entries ) -> toStructure problem.symbols ( n, entries ++ missingEntries problem.arities n entries ))


{-| Default entries for the symbols of the problem that Mace4 did not print.
-}
missingEntries : Dict String ( Bool, Int ) -> Int -> List Entry -> List Entry
missingEntries arities n entries =
    let
        printed =
            List.map .name entries
    in
    arities
        |> Dict.toList
        |> List.filter (\( name, _ ) -> not (List.member name printed))
        |> List.map
            (\( name, ( isPred, k ) ) ->
                { kind =
                    if isPred then
                        "relation"

                    else
                        "function"
                , name = name
                , arity = k
                , values = List.repeat (n ^ k) 0
                }
            )



-- MACE4 MODELS


type alias Entry =
    { kind : String
    , name : String
    , arity : Int
    , values : List Int
    }


interpretationParser : Parser ( Int, List Entry )
interpretationParser =
    Parser.succeed Tuple.pair
        |. Parser.symbol "interpretation("
        |. ws
        |= Parser.int
        |. ws
        |. Parser.symbol ","
        |. Parser.chompUntil "],"
        |. Parser.symbol "],"
        |. ws
        |= Parser.sequence
            { start = "["
            , separator = ","
            , end = "]"
            , spaces = ws
            , item = entryParser
            , trailing = Parser.Forbidden
            }


{-| Blanks, including the tabs Mace4 uses in its tables (`Parser.spaces` does not accept tabs).
-}
ws : Parser ()
ws =
    Parser.chompWhile (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t')


entryParser : Parser Entry
entryParser =
    Parser.succeed (\kind ( name, arity ) values -> { kind = kind, name = name, arity = arity, values = values })
        |= Parser.oneOf [ Parser.map (\_ -> "function") (Parser.keyword "function"), Parser.map (\_ -> "relation") (Parser.keyword "relation") ]
        |. Parser.symbol "("
        |= symbolParser
        |. ws
        |. Parser.symbol ","
        |. ws
        |= Parser.sequence
            { start = "["
            , separator = ","
            , end = "]"
            , spaces = ws
            , item = Parser.int
            , trailing = Parser.Forbidden
            }
        |. ws
        |. Parser.symbol ")"


{-| A symbol with its argument placeholders: `a`, `f(_)`, `R(_,_)`. The arity is the number of `_`.
-}
symbolParser : Parser ( String, Int )
symbolParser =
    Parser.succeed (\name args -> ( name, String.length (String.filter ((==) '_') args) ))
        |= (Parser.getChompedString <| Parser.chompWhile (\c -> c /= '(' && c /= ',' && c /= ' '))
        |= Parser.oneOf
            [ Parser.getChompedString (Parser.symbol "(" |. Parser.chompUntil ")" |. Parser.symbol ")")
            , Parser.succeed ""
            ]


toStructure : Dict String Ident -> ( Int, List Entry ) -> L_Structure Int
toStructure symbols ( n, entries ) =
    let
        ident name =
            Dict.get name symbols |> Maybe.withDefault ( name, [] )

        tuples k =
            -- row-major order, first argument most significant, as Mace4 prints the tables
            List.foldr (\_ acc -> LE.lift2 (::) (List.range 0 (n - 1)) acc) [ [] ] (List.range 1 k)

        add e acc =
            case ( e.kind, e.arity ) of
                ( "function", 0 ) ->
                    { acc | const = Dict.insert (ident e.name) (Maybe.withDefault 0 (List.head e.values)) acc.const }

                ( "function", k ) ->
                    { acc | func = Dict.insert (ident e.name) ( k, Dict.fromList (List.map2 Tuple.pair (tuples k) e.values) ) acc.func }

                ( _, k ) ->
                    { acc
                        | pred =
                            Dict.insert (ident e.name)
                                ( k
                                , List.map2 Tuple.pair (tuples k) e.values
                                    |> List.filter (\( _, v ) -> v == 1)
                                    |> List.map Tuple.first
                                    |> Set.fromList
                                )
                                acc.pred
                    }
    in
    ( Set.fromList (List.range 0 (n - 1))
    , List.foldl add { const = Dict.empty, func = Dict.empty, pred = Dict.empty } entries
    )



-- SYMBOLS


type Kind
    = Predicate
    | Function


{-| Names for every symbol. Prover9 reads unquantified symbols starting with u-z as variables, so function symbols
are renamed to avoid that; predicates keep their name. Clashes get a numeric suffix.
-}
symbolNames : SetFOL -> Dict Ident String
symbolNames fs =
    fs
        |> List.concatMap formulaSymbols
        |> LE.unique
        |> List.foldl
            (\( kind, id ) ( acc, used ) ->
                let
                    name =
                        freshName (baseName kind id) used 1
                in
                ( Dict.insert (keyOf kind id) name acc, Set.insert name used )
            )
            ( Dict.empty, Set.empty )
        |> Tuple.first


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
    Dict.get (keyOf kind id) names |> Maybe.withDefault (baseName kind id)


baseName : Kind -> Ident -> String
baseName kind ( s, is ) =
    let
        clean =
            String.toList s
                |> List.map
                    (\c ->
                        if (Char.isAlphaNum c && Char.toCode c < 128) || c == '_' then
                            String.fromChar c

                        else
                            "u" ++ String.fromInt (Char.toCode c)
                    )
                |> String.concat

        withIndices =
            clean ++ String.concat (List.map (\i -> "_" ++ String.fromInt i) is)
    in
    case kind of
        Predicate ->
            if String.all Char.isAlpha (String.left 1 withIndices) && withIndices /= "" then
                withIndices

            else
                "P" ++ withIndices

        Function ->
            case String.uncons withIndices of
                Just ( c, _ ) ->
                    if Char.isAlpha c && not (List.member (Char.toLower c) [ 'u', 'v', 'w', 'x', 'y', 'z' ]) then
                        withIndices

                    else
                        "c_" ++ withIndices

                Nothing ->
                    "c_"


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


formulaArities : FormulaFOL -> List ( Kind, Ident, Int )
formulaArities f =
    let
        termAr t =
            case t of
                Var _ ->
                    []

                Func id ts ->
                    ( Function, id, List.length ts ) :: List.concatMap termAr ts
    in
    case f of
        Pred id ts ->
            ( Predicate, id, List.length ts ) :: List.concatMap termAr ts

        Equal t1 t2 ->
            termAr t1 ++ termAr t2

        Neg g ->
            formulaArities g

        Conj g h ->
            formulaArities g ++ formulaArities h

        Disj g h ->
            formulaArities g ++ formulaArities h

        Impl g h ->
            formulaArities g ++ formulaArities h

        Equi g h ->
            formulaArities g ++ formulaArities h

        Exists _ g ->
            formulaArities g

        Forall _ g ->
            formulaArities g

        _ ->
            []


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


{-| Quantified variables keep a readable upper case name (Prover9 accepts any name for an explicitly quantified
variable).
-}
varName : Variable -> String
varName ( s, is, prime ) =
    let
        clean =
            String.filter (\c -> Char.isAlphaNum c && Char.toCode c < 128) s
    in
    (if clean == "" then
        "V"

     else
        clean
    )
        ++ String.concat (List.map (\i -> "_" ++ String.fromInt i) is)
        ++ (if prime > 0 then
                "_p" ++ String.fromInt prime

            else
                ""
           )


termToP9 : Dict Ident String -> Term -> String
termToP9 names t =
    case t of
        Var v ->
            varName v

        Func id [] ->
            lookupName names Function id

        Func id ts ->
            lookupName names Function id ++ "(" ++ String.join "," (List.map (termToP9 names) ts) ++ ")"


formulaToP9 : Dict Ident String -> FormulaFOL -> String
formulaToP9 names f =
    case f of
        Pred id [] ->
            lookupName names Predicate id

        Pred id ts ->
            lookupName names Predicate id ++ "(" ++ String.join "," (List.map (termToP9 names) ts) ++ ")"

        Equal t1 t2 ->
            "(" ++ termToP9 names t1 ++ " = " ++ termToP9 names t2 ++ ")"

        Neg (Equal t1 t2) ->
            "(" ++ termToP9 names t1 ++ " != " ++ termToP9 names t2 ++ ")"

        Neg g ->
            "-" ++ formulaToP9 names g

        Conj g h ->
            "(" ++ formulaToP9 names g ++ " & " ++ formulaToP9 names h ++ ")"

        Disj g h ->
            "(" ++ formulaToP9 names g ++ " | " ++ formulaToP9 names h ++ ")"

        Impl g h ->
            "(" ++ formulaToP9 names g ++ " -> " ++ formulaToP9 names h ++ ")"

        Equi g h ->
            "(" ++ formulaToP9 names g ++ " <-> " ++ formulaToP9 names h ++ ")"

        Forall v g ->
            "(all " ++ varName v ++ " " ++ formulaToP9 names g ++ ")"

        Exists v g ->
            "(exists " ++ varName v ++ " " ++ formulaToP9 names g ++ ")"

        Taut ->
            "$T"

        Insat ->
            "$F"
