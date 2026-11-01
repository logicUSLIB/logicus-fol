module LogicUS.FOL.Deduction exposing
    ( Schema(..), TermSchema(..), Premise(..), Condition(..), Rule, System
    , readSystem, ruleToString, systemToString, findRule
    , readFormula, formulaToString, formulaToInputString
    , ProofLine, Problem, LineReport, ProofReport
    , readProof, proofToString, checkProof
    , Hint, HintKind(..), hints
    )

{-| Deduction systems for first-order logic given by their rules, and proofs checked with them. It extends
`LogicUS.PL.Deduction` (package logicus-pl) with quantifiers and equality: the rules and the proofs are written in the
same way.

A **system** is a list of rules written as schemas, so that each exercise can say which rules may be used:

    rule ∧I : A, B ⊢ A ∧ B
    rule →I : [A] B ⊢ A → B
    rule ∨E : A ∨ B, [A] C, [B] C ⊢ C
    rule ∀I : A[x/a] ⊢ ∀x A          if a fresh
    rule ∀E : ∀x A ⊢ A[x/t]
    rule =E : t = s, A[x/t] ⊢ A[x/s]
    axiom A1 : A → (B → A)

In a schema, a capital letter (`A`, `B`, `C1`...) stands for any formula; after a quantifier or before `/` in a
substitution, a lower-case name (`x`, `y`) stands for any variable; elsewhere a lower-case name (`t`, `s`, `a`) stands
for any term. `A[x/t]` is the formula `A` with the free occurrences of `x` replaced by `t` (the replacement must not
capture variables). A premise `[A] B` is a subproof that assumes `A` and ends in `B`; the rule closes it. The side
conditions are `a fresh` (`a` is a variable or a constant that does not occur in the conclusion, in the formula `A` of
`A[x/a]`, in the premises of the proof nor in its open assumptions) and `x not free in A`. `⊢` can be written `|-`,
and the connectives as in the formulas of the library (`&`, `|`, `->`, `<->`, `¬`, `!A`, `!E`, `!F`, `!T`).

A **proof** is written in the style of Fitch, a line per formula, with bars for the subproofs:

    1  !E[X]P(X)              premise
    2  !A[X](P(X) -> Q(X))    premise
    3  | P(a)                 assumption
    4  | P(a) -> Q(a)         ∀E 2
    5  | Q(a)                 →E 4, 3
    6  | !E[X]Q(X)            ∃I 5
    7  !E[X]Q(X)              ∃E 1, 3-6

Lines are cited by their number, and closed subproofs by their first and last lines (`3-6`). A line can cite the lines
above it that are not inside a closed subproof. An assumption opens a new subproof; a line with fewer bars closes the
subproofs deeper than it. The line numbers at the beginning are optional (lines are numbered by their position), and
`%` can separate the formula from its justification. `premise` and `assumption` can also be written `premisa`/`P` and
`supuesto`/`A`/`hyp`.

The formulas are read with the syntax of `LogicUS.FOL.SyntaxSemantics` (`!A[X](P(X) -> Q(X))`, `a = b`).

The module also gives **hints**: the rules of the system that can be applied at the end of a proof (to its lines, to
its closed subproofs or closing the current one) and those that would give a target formula.


# Systems

@docs Schema, TermSchema, Premise, Condition, Rule, System
@docs readSystem, ruleToString, systemToString, findRule


# Formulas

@docs readFormula, formulaToString, formulaToInputString


# Proofs

@docs ProofLine, Problem, LineReport, ProofReport
@docs readProof, proofToString, checkProof


# Hints

@docs Hint, HintKind, hints

-}

import Dict exposing (Dict)
import List.Extra as LE
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), Term(..), Variable)
import LogicUS.PL.Deduction as PLD
import Set exposing (Set)



--===========--
--  SYSTEMS  --
--===========--


{-| A formula schema. `SMeta "A"` stands for any formula, `SAll "x" s` for `∀x s` (`x` stands for any variable) and
`SSubst s "x" t` for `s[x/t]`.
-}
type Schema
    = SMeta String
    | SBot
    | STop
    | SNot Schema
    | SAnd Schema Schema
    | SOr Schema Schema
    | SImp Schema Schema
    | SIff Schema Schema
    | SAll String Schema
    | SEx String Schema
    | SEq TermSchema TermSchema
    | SSubst Schema String TermSchema


{-| A term in a schema: a variable (`TVar "x"`, bound by a quantifier of the schema) or any term (`TMeta "t"`).
-}
type TermSchema
    = TVar String
    | TMeta String


{-| A premise of a rule: a formula, or a subproof from an assumption to a formula.
-}
type Premise
    = PFormula Schema
    | PSubproof Schema Schema


{-| A side condition of a rule.
-}
type Condition
    = Fresh String
    | NotFree String String


{-| A rule: its name, its premises, its conclusion and its side conditions. An axiom is a rule without premises.
-}
type alias Rule =
    { name : String
    , premises : List Premise
    , conclusion : Schema
    , conditions : List Condition
    }


{-| A deduction system: the rules that can be used.
-}
type alias System =
    List Rule



-- READING SCHEMAS


type Token
    = TkIdent String
    | TkSym String


symbols : List ( String, String )
symbols =
    -- longest first
    [ ( "<->", "↔" )
    , ( "|-", "⊢" )
    , ( "->", "→" )
    , ( "!A", "∀" )
    , ( "!E", "∃" )
    , ( "!F", "⊥" )
    , ( "!T", "⊤" )
    , ( "_|_", "⊥" )
    , ( "↔", "↔" )
    , ( "→", "→" )
    , ( "⊢", "⊢" )
    , ( "∧", "∧" )
    , ( "&", "∧" )
    , ( "∨", "∨" )
    , ( "|", "∨" )
    , ( "¬", "¬" )
    , ( "~", "¬" )
    , ( "-", "¬" )
    , ( "∀", "∀" )
    , ( "∃", "∃" )
    , ( "⊥", "⊥" )
    , ( "⊤", "⊤" )
    , ( "(", "(" )
    , ( ")", ")" )
    , ( "[", "[" )
    , ( "]", "]" )
    , ( "/", "/" )
    , ( ",", "," )
    , ( "=", "=" )
    ]


tokenize : String -> Result String (List Token)
tokenize src =
    let
        isIdentChar c =
            Char.isAlphaNum c || c == '_' || c == '\''

        go s acc =
            case String.uncons s of
                Nothing ->
                    Ok (List.reverse acc)

                Just ( c, rest ) ->
                    if c == ' ' || c == '\t' then
                        go rest acc

                    else if Char.isAlpha c then
                        let
                            name =
                                String.fromChar c ++ takeWhile isIdentChar rest
                        in
                        go (String.dropLeft (String.length name) s) (TkIdent name :: acc)

                    else
                        case LE.find (\( sym, _ ) -> String.startsWith sym s) symbols of
                            Just ( sym, canon ) ->
                                go (String.dropLeft (String.length sym) s) (TkSym canon :: acc)

                            Nothing ->
                                Err ("unexpected symbol '" ++ String.fromChar c ++ "'")
    in
    go src []


takeWhile : (Char -> Bool) -> String -> String
takeWhile p s =
    case String.uncons s of
        Just ( c, rest ) ->
            if p c then
                String.cons c (takeWhile p rest)

            else
                ""

        Nothing ->
            ""


isFormulaMeta : String -> Bool
isFormulaMeta name =
    case String.uncons name of
        Just ( c, _ ) ->
            Char.isUpper c

        Nothing ->
            False



-- Recursive descent: iff < imp (right) < or < and < unary. Each function returns the rest of the tokens.


type alias P a =
    List Token -> Result String ( a, List Token )


parseSchema : P Schema
parseSchema ts =
    parseIff ts


parseIff : P Schema
parseIff ts =
    parseImp ts
        |> Result.andThen
            (\( l, rest ) ->
                case rest of
                    (TkSym "↔") :: rest2 ->
                        parseIff rest2 |> Result.map (\( r, rest3 ) -> ( SIff l r, rest3 ))

                    _ ->
                        Ok ( l, rest )
            )


parseImp : P Schema
parseImp ts =
    parseOr ts
        |> Result.andThen
            (\( l, rest ) ->
                case rest of
                    (TkSym "→") :: rest2 ->
                        parseImp rest2 |> Result.map (\( r, rest3 ) -> ( SImp l r, rest3 ))

                    _ ->
                        Ok ( l, rest )
            )


parseOr : P Schema
parseOr ts =
    let
        loop l rest =
            case rest of
                (TkSym "∨") :: rest2 ->
                    parseAnd rest2 |> Result.andThen (\( r, rest3 ) -> loop (SOr l r) rest3)

                _ ->
                    Ok ( l, rest )
    in
    parseAnd ts |> Result.andThen (\( l, rest ) -> loop l rest)


parseAnd : P Schema
parseAnd ts =
    let
        loop l rest =
            case rest of
                (TkSym "∧") :: rest2 ->
                    parseUnary rest2 |> Result.andThen (\( r, rest3 ) -> loop (SAnd l r) rest3)

                _ ->
                    Ok ( l, rest )
    in
    parseUnary ts |> Result.andThen (\( l, rest ) -> loop l rest)


parseUnary : P Schema
parseUnary ts =
    case ts of
        (TkSym "¬") :: rest ->
            parseUnary rest |> Result.map (\( s, rest2 ) -> ( SNot s, rest2 ))

        (TkSym "∀") :: rest ->
            parseBinder rest |> Result.andThen (\( x, rest2 ) -> parseUnary rest2 |> Result.map (\( s, rest3 ) -> ( SAll x s, rest3 )))

        (TkSym "∃") :: rest ->
            parseBinder rest |> Result.andThen (\( x, rest2 ) -> parseUnary rest2 |> Result.map (\( s, rest3 ) -> ( SEx x s, rest3 )))

        _ ->
            parsePostfix ts


parseBinder : P String
parseBinder ts =
    case ts of
        (TkSym "[") :: (TkIdent x) :: (TkSym "]") :: rest ->
            Ok ( x, rest )

        (TkIdent x) :: rest ->
            Ok ( x, rest )

        _ ->
            Err "expected a variable after the quantifier"


parsePostfix : P Schema
parsePostfix ts =
    let
        loop s rest =
            case rest of
                (TkSym "[") :: (TkIdent x) :: (TkSym "/") :: (TkIdent t) :: (TkSym "]") :: rest2 ->
                    loop (SSubst s x (TMeta t)) rest2

                _ ->
                    Ok ( s, rest )
    in
    parsePrimary ts |> Result.andThen (\( s, rest ) -> loop s rest)


parsePrimary : P Schema
parsePrimary ts =
    case ts of
        (TkSym "(") :: rest ->
            parseSchema rest
                |> Result.andThen
                    (\( s, rest2 ) ->
                        case rest2 of
                            (TkSym ")") :: rest3 ->
                                Ok ( s, rest3 )

                            _ ->
                                Err "expected ')'"
                    )

        (TkSym "⊥") :: rest ->
            Ok ( SBot, rest )

        (TkSym "⊤") :: rest ->
            Ok ( STop, rest )

        (TkIdent a) :: (TkSym "=") :: (TkIdent b) :: rest ->
            Ok ( SEq (TMeta a) (TMeta b), rest )

        (TkIdent a) :: rest ->
            if isFormulaMeta a then
                Ok ( SMeta a, rest )

            else
                Err ("'" ++ a ++ "' is not a formula (formulas are written with capital letters: A, B...)")

        (TkSym s) :: _ ->
            Err ("unexpected '" ++ s ++ "'")

        [] ->
            Err "the schema is incomplete"



-- The names bound by quantifiers are variables, and so are the names before '/' in substitutions.


fixVariables : Schema -> Schema
fixVariables s =
    let
        vars =
            schemaVarNames s

        fixT t =
            case t of
                TMeta n ->
                    if Set.member n vars then
                        TVar n

                    else
                        t

                TVar _ ->
                    t

        go x =
            case x of
                SNot a ->
                    SNot (go a)

                SAnd a b ->
                    SAnd (go a) (go b)

                SOr a b ->
                    SOr (go a) (go b)

                SImp a b ->
                    SImp (go a) (go b)

                SIff a b ->
                    SIff (go a) (go b)

                SAll v a ->
                    SAll v (go a)

                SEx v a ->
                    SEx v (go a)

                SEq a b ->
                    SEq (fixT a) (fixT b)

                SSubst a v t ->
                    SSubst (go a) v (fixT t)

                _ ->
                    x
    in
    go s


schemaVarNames : Schema -> Set String
schemaVarNames s =
    case s of
        SNot a ->
            schemaVarNames a

        SAnd a b ->
            Set.union (schemaVarNames a) (schemaVarNames b)

        SOr a b ->
            Set.union (schemaVarNames a) (schemaVarNames b)

        SImp a b ->
            Set.union (schemaVarNames a) (schemaVarNames b)

        SIff a b ->
            Set.union (schemaVarNames a) (schemaVarNames b)

        SAll v a ->
            Set.insert v (schemaVarNames a)

        SEx v a ->
            Set.insert v (schemaVarNames a)

        SSubst a v _ ->
            Set.insert v (schemaVarNames a)

        _ ->
            Set.empty


parsePremises : P (List Premise)
parsePremises ts =
    let
        one tks =
            case tks of
                (TkSym "[") :: rest ->
                    parseSchema rest
                        |> Result.andThen
                            (\( a, rest2 ) ->
                                case rest2 of
                                    (TkSym "]") :: rest3 ->
                                        parseSchema rest3 |> Result.map (\( c, rest4 ) -> ( PSubproof a c, rest4 ))

                                    _ ->
                                        Err "expected ']' after the assumption"
                            )

                _ ->
                    parseSchema tks |> Result.map (\( s, rest ) -> ( PFormula s, rest ))

        loop acc tks =
            one tks
                |> Result.andThen
                    (\( p, rest ) ->
                        case rest of
                            (TkSym ",") :: rest2 ->
                                loop (p :: acc) rest2

                            _ ->
                                Ok ( List.reverse (p :: acc), rest )
                    )
    in
    case ts of
        (TkSym "⊢") :: _ ->
            Ok ( [], ts )

        _ ->
            loop [] ts


parseConditions : String -> Result String (List Condition)
parseConditions src =
    src
        |> String.split ","
        |> List.map String.words
        |> List.filter (not << List.isEmpty)
        |> List.foldr
            (\ws acc ->
                case ( ws, acc ) of
                    ( [ a, "fresh" ], Ok cs ) ->
                        Ok (Fresh a :: cs)

                    ( [ x, "not", "free", "in", f ], Ok cs ) ->
                        Ok (NotFree x f :: cs)

                    ( _, Err e ) ->
                        Err e

                    _ ->
                        Err ("unknown condition: " ++ String.join " " ws ++ " (use 'a fresh' or 'x not free in A')")
            )
            (Ok [])


readRule : String -> Result String Rule
readRule line =
    let
        body =
            String.trim <|
                if String.startsWith "rule " line then
                    String.dropLeft 5 line

                else if String.startsWith "axiom " line then
                    String.dropLeft 6 line

                else
                    line

        ( name, rest ) =
            case String.indexes ":" body of
                i :: _ ->
                    ( String.trim (String.left i body), String.dropLeft (i + 1) body )

                [] ->
                    ( "", body )

        ( ruleText, condText ) =
            case String.indexes " if " rest of
                i :: _ ->
                    ( String.left i rest, Just (String.dropLeft (i + 4) rest) )

                [] ->
                    ( rest, Nothing )

        withTurnstile =
            if String.contains "⊢" ruleText || String.contains "|-" ruleText then
                ruleText

            else
                "⊢ " ++ ruleText
    in
    if name == "" || String.contains " " name then
        Err "a rule is written 'rule NAME : premises ⊢ conclusion' (the name without spaces)"

    else
        tokenize withTurnstile
            |> Result.andThen parsePremises
            |> Result.andThen
                (\( ps, rest2 ) ->
                    case rest2 of
                        (TkSym "⊢") :: rest3 ->
                            parseSchema rest3
                                |> Result.andThen
                                    (\( c, rest4 ) ->
                                        if List.isEmpty rest4 then
                                            Ok ( ps, c )

                                        else
                                            Err "unexpected text after the conclusion"
                                    )

                        _ ->
                            Err "expected '⊢' between the premises and the conclusion"
                )
            |> Result.andThen
                (\( ps, c ) ->
                    Maybe.withDefault (Ok []) (Maybe.map parseConditions condText)
                        |> Result.map
                            (\conds ->
                                let
                                    vars =
                                        List.foldl (\p acc -> Set.union acc (premiseVarNames p)) (schemaVarNames c) ps

                                    fixP p =
                                        case p of
                                            PFormula s ->
                                                PFormula (fixWith vars s)

                                            PSubproof a b ->
                                                PSubproof (fixWith vars a) (fixWith vars b)
                                in
                                { name = name, premises = List.map fixP ps, conclusion = fixWith vars c, conditions = conds }
                            )
                )
            |> Result.mapError (\e -> name ++ ": " ++ e)


premiseVarNames : Premise -> Set String
premiseVarNames p =
    case p of
        PFormula s ->
            schemaVarNames s

        PSubproof a b ->
            Set.union (schemaVarNames a) (schemaVarNames b)


fixWith : Set String -> Schema -> Schema
fixWith vars s =
    let
        fixT t =
            case t of
                TMeta n ->
                    if Set.member n vars then
                        TVar n

                    else
                        t

                TVar _ ->
                    t

        go x =
            case x of
                SNot a ->
                    SNot (go a)

                SAnd a b ->
                    SAnd (go a) (go b)

                SOr a b ->
                    SOr (go a) (go b)

                SImp a b ->
                    SImp (go a) (go b)

                SIff a b ->
                    SIff (go a) (go b)

                SAll v a ->
                    SAll v (go a)

                SEx v a ->
                    SEx v (go a)

                SEq a b ->
                    SEq (fixT a) (fixT b)

                SSubst a v t ->
                    SSubst (go a) v (fixT t)

                _ ->
                    x
    in
    go (fixVariables s)


{-| It reads a system: a rule per line (`rule NAME : premises ⊢ conclusion [if conditions]`, or
`axiom NAME : formula`). Empty lines and lines starting with `#` or `--` are ignored. The errors say the line.
-}
readSystem : String -> Result String System
readSystem src =
    src
        |> String.lines
        |> List.indexedMap Tuple.pair
        |> List.filter (\( _, l ) -> not (String.isEmpty (String.trim l) || String.startsWith "#" (String.trim l) || String.startsWith "--" (String.trim l)))
        |> List.foldr
            (\( i, l ) acc ->
                case ( readRule (String.trim l), acc ) of
                    ( Ok r, Ok rs ) ->
                        Ok (r :: rs)

                    ( Err e, _ ) ->
                        Err ("line " ++ String.fromInt (i + 1) ++ ": " ++ e)

                    ( _, Err e ) ->
                        Err e
            )
            (Ok [])



-- WRITING SCHEMAS


schemaToString : Schema -> String
schemaToString s =
    let
        prec x =
            case x of
                SIff _ _ ->
                    1

                SImp _ _ ->
                    2

                SOr _ _ ->
                    3

                SAnd _ _ ->
                    4

                _ ->
                    5

        par p x =
            if prec x < p then
                "(" ++ schemaToString x ++ ")"

            else
                schemaToString x

        term t =
            case t of
                TVar v ->
                    v

                TMeta m ->
                    m
    in
    case s of
        SMeta a ->
            a

        SBot ->
            "⊥"

        STop ->
            "⊤"

        SNot a ->
            "¬" ++ par 5 a

        SAnd a b ->
            par 4 a ++ " ∧ " ++ par 5 b

        SOr a b ->
            par 3 a ++ " ∨ " ++ par 4 b

        SImp a b ->
            par 3 a ++ " → " ++ par 2 b

        SIff a b ->
            par 2 a ++ " ↔ " ++ par 1 b

        SAll v a ->
            "∀" ++ v ++ " " ++ par 5 a

        SEx v a ->
            "∃" ++ v ++ " " ++ par 5 a

        SEq a b ->
            term a ++ " = " ++ term b

        SSubst a v t ->
            par 5 a ++ "[" ++ v ++ "/" ++ term t ++ "]"


{-| It writes a rule as `readSystem` reads it.
-}
ruleToString : Rule -> String
ruleToString r =
    let
        premise p =
            case p of
                PFormula s ->
                    schemaToString s

                PSubproof a b ->
                    "[" ++ schemaToString a ++ "] " ++ schemaToString b

        cond c =
            case c of
                Fresh a ->
                    a ++ " fresh"

                NotFree x a ->
                    x ++ " not free in " ++ a
    in
    (if List.isEmpty r.premises then
        "axiom " ++ r.name ++ " : " ++ schemaToString r.conclusion

     else
        "rule " ++ r.name ++ " : " ++ String.join ", " (List.map premise r.premises) ++ " ⊢ " ++ schemaToString r.conclusion
    )
        ++ (if List.isEmpty r.conditions then
                ""

            else
                "   if " ++ String.join ", " (List.map cond r.conditions)
           )


{-| It writes a system as `readSystem` reads it.
-}
systemToString : System -> String
systemToString sys =
    String.join "\n" (List.map ruleToString sys)


normalizeName : String -> String
normalizeName n =
    n
        |> String.replace "<->" "↔"
        |> String.replace "->" "→"
        |> String.replace "&" "∧"
        |> String.replace "\\/" "∨"
        |> String.replace "~" "¬"
        |> String.replace "_|_" "⊥"
        |> String.toLower


{-| It finds a rule of a system by its name. The name can use the ASCII forms of the connectives (`->I` for `→I`),
and upper and lower case are not distinguished.
-}
findRule : System -> String -> Maybe Rule
findRule sys name =
    LE.find (\r -> normalizeName r.name == normalizeName name) sys



--============--
--  FORMULAS  --
--============--


{-| It reads a formula in the syntax of `LogicUS.FOL.SyntaxSemantics`.
-}
readFormula : String -> Result String FormulaFOL
readFormula s =
    case FOL_SS.ffolReadFromString s of
        ( Just f, _, _ ) ->
            Ok f

        ( Nothing, _, e ) ->
            Err ("the formula cannot be read (" ++ e ++ ")")


{-| It writes a formula (with `ffolToString`).
-}
formulaToString : FormulaFOL -> String
formulaToString =
    FOL_SS.ffolToString


{-| It writes a formula in the syntax that `readFormula` reads.
-}
formulaToInputString : FormulaFOL -> String
formulaToInputString =
    FOL_SS.ffolToInputString



--============--
--  MATCHING  --
--============--


type alias Env =
    { forms : Dict String FormulaFOL
    , vars : Dict String Variable
    , terms : Dict String Term
    }


emptyEnv : Env
emptyEnv =
    { forms = Dict.empty, vars = Dict.empty, terms = Dict.empty }



-- A substitution A[x/t] waiting for its parts.


type alias Deferred =
    ( Schema, FormulaFOL )


matchTerm : TermSchema -> Term -> Env -> Maybe Env
matchTerm ts t env =
    case ts of
        TVar x ->
            case t of
                Var v ->
                    case Dict.get x env.vars of
                        Just v2 ->
                            if v == v2 then
                                Just env

                            else
                                Nothing

                        Nothing ->
                            Just { env | vars = Dict.insert x v env.vars }

                _ ->
                    Nothing

        TMeta m ->
            case Dict.get m env.terms of
                Just t2 ->
                    if t == t2 then
                        Just env

                    else
                        Nothing

                Nothing ->
                    Just { env | terms = Dict.insert m t env.terms }


matchS : Schema -> FormulaFOL -> ( Env, List Deferred ) -> Maybe ( Env, List Deferred )
matchS s f ( env, defs ) =
    let
        both a b x y =
            matchS a x ( env, defs ) |> Maybe.andThen (matchS b y)

        bindVar x v e =
            case Dict.get x e.vars of
                Just v2 ->
                    if v == v2 then
                        Just e

                    else
                        Nothing

                Nothing ->
                    Just { e | vars = Dict.insert x v e.vars }
    in
    case ( s, f ) of
        ( SMeta a, _ ) ->
            case Dict.get a env.forms of
                Just g ->
                    if g == f then
                        Just ( env, defs )

                    else
                        Nothing

                Nothing ->
                    Just ( { env | forms = Dict.insert a f env.forms }, defs )

        ( SBot, Insat ) ->
            Just ( env, defs )

        ( STop, Taut ) ->
            Just ( env, defs )

        ( SNot a, Neg x ) ->
            matchS a x ( env, defs )

        ( SAnd a b, Conj x y ) ->
            both a b x y

        ( SOr a b, Disj x y ) ->
            both a b x y

        ( SImp a b, Impl x y ) ->
            both a b x y

        ( SIff a b, Equi x y ) ->
            both a b x y

        ( SAll x a, Forall v g ) ->
            bindVar x v env |> Maybe.andThen (\e -> matchS a g ( e, defs ))

        ( SEx x a, Exists v g ) ->
            bindVar x v env |> Maybe.andThen (\e -> matchS a g ( e, defs ))

        ( SEq a b, Equal x y ) ->
            matchTerm a x env |> Maybe.andThen (matchTerm b y) |> Maybe.map (\e -> ( e, defs ))

        ( SSubst _ _ _, _ ) ->
            Just ( env, ( s, f ) :: defs )

        _ ->
            Nothing



-- The formula of a schema whose parts are all known.


instantiate : Env -> Schema -> Maybe FormulaFOL
instantiate env s =
    let
        two c a b =
            Maybe.map2 c (instantiate env a) (instantiate env b)

        term t =
            case t of
                TVar x ->
                    Maybe.map Var (Dict.get x env.vars)

                TMeta m ->
                    Dict.get m env.terms
    in
    case s of
        SMeta a ->
            Dict.get a env.forms

        SBot ->
            Just Insat

        STop ->
            Just Taut

        SNot a ->
            Maybe.map Neg (instantiate env a)

        SAnd a b ->
            two Conj a b

        SOr a b ->
            two Disj a b

        SImp a b ->
            two Impl a b

        SIff a b ->
            two Equi a b

        SAll x a ->
            Maybe.map2 Forall (Dict.get x env.vars) (instantiate env a)

        SEx x a ->
            Maybe.map2 Exists (Dict.get x env.vars) (instantiate env a)

        SEq a b ->
            Maybe.map2 Equal (term a) (term b)

        SSubst a x t ->
            Maybe.map3 (\g v tm -> substitute v tm g) (instantiate env a) (Dict.get x env.vars) (term t)



-- A[x/t] when t is free for x in A; otherwise Nothing.


substituteSafe : Variable -> Term -> FormulaFOL -> Maybe FormulaFOL
substituteSafe v t f =
    if freeFor v t f Set.empty then
        Just (substitute v t f)

    else
        Nothing


substitute : Variable -> Term -> FormulaFOL -> FormulaFOL
substitute v t f =
    FOL_SS.ffolApplySubstitution (Dict.singleton v t) f



-- No variable of t is bound at a free occurrence of v.


freeFor : Variable -> Term -> FormulaFOL -> Set Variable -> Bool
freeFor v t f bound =
    let
        tvars =
            Set.fromList (FOL_SS.termVarSymbols t)

        atomOk ts =
            if List.member v (FOL_SS.termsVarSymbols ts) && not (Set.member v bound) then
                Set.isEmpty (Set.intersect bound tvars)

            else
                True
    in
    case f of
        Pred _ ts ->
            atomOk ts

        Equal a b ->
            atomOk [ a, b ]

        Neg a ->
            freeFor v t a bound

        Conj a b ->
            freeFor v t a bound && freeFor v t b bound

        Disj a b ->
            freeFor v t a bound && freeFor v t b bound

        Impl a b ->
            freeFor v t a bound && freeFor v t b bound

        Equi a b ->
            freeFor v t a bound && freeFor v t b bound

        Forall w a ->
            w == v || freeFor v t a (Set.insert w bound)

        Exists w a ->
            w == v || freeFor v t a (Set.insert w bound)

        _ ->
            True



-- The term t such that g[v/t] = f, if any: Just Nothing when v does not occur free in g (any t).


solveTerm : Variable -> FormulaFOL -> FormulaFOL -> Maybe (Maybe Term)
solveTerm v g f =
    let
        merge a b =
            case ( a, b ) of
                ( Just Nothing, x ) ->
                    x

                ( x, Just Nothing ) ->
                    x

                ( Just (Just t1), Just (Just t2) ) ->
                    if t1 == t2 then
                        a

                    else
                        Nothing

                _ ->
                    Nothing

        terms ts1 ts2 =
            if List.length ts1 == List.length ts2 then
                List.foldl merge (Just Nothing) (List.map2 term ts1 ts2)

            else
                Nothing

        term t1 t2 =
            case t1 of
                Var w ->
                    if w == v then
                        Just (Just t2)

                    else if t1 == t2 then
                        Just Nothing

                    else
                        Nothing

                Func n ts1 ->
                    case t2 of
                        Func m ts2 ->
                            if n == m then
                                terms ts1 ts2

                            else
                                Nothing

                        _ ->
                            Nothing

        go a b =
            case ( a, b ) of
                ( Pred p ts1, Pred q ts2 ) ->
                    if p == q then
                        terms ts1 ts2

                    else
                        Nothing

                ( Equal a1 a2, Equal b1 b2 ) ->
                    terms [ a1, a2 ] [ b1, b2 ]

                ( Neg x, Neg y ) ->
                    go x y

                ( Conj x1 x2, Conj y1 y2 ) ->
                    merge (go x1 y1) (go x2 y2)

                ( Disj x1 x2, Disj y1 y2 ) ->
                    merge (go x1 y1) (go x2 y2)

                ( Impl x1 x2, Impl y1 y2 ) ->
                    merge (go x1 y1) (go x2 y2)

                ( Equi x1 x2, Equi y1 y2 ) ->
                    merge (go x1 y1) (go x2 y2)

                ( Forall w x, Forall w2 y ) ->
                    if w /= w2 then
                        Nothing

                    else if w == v then
                        if x == y then
                            Just Nothing

                        else
                            Nothing

                    else
                        go x y

                ( Exists w x, Exists w2 y ) ->
                    if w /= w2 then
                        Nothing

                    else if w == v then
                        if x == y then
                            Just Nothing

                        else
                            Nothing

                    else
                        go x y

                ( Insat, Insat ) ->
                    Just Nothing

                ( Taut, Taut ) ->
                    Just Nothing

                _ ->
                    Nothing
    in
    go g f



-- A formula g and a variable v such that g[v/t1] = f1 and g[v/t2] = f2 (Leibniz law): the positions where f1 has
-- t1 and f2 has t2 become v.


antiUnify : Variable -> Term -> Term -> FormulaFOL -> FormulaFOL -> Maybe FormulaFOL
antiUnify v t1 t2 f1 f2 =
    let
        term a b =
            if a == b then
                Just a

            else if a == t1 && b == t2 then
                Just (Var v)

            else
                case ( a, b ) of
                    ( Func n as1, Func m bs1 ) ->
                        if n == m && List.length as1 == List.length bs1 then
                            Maybe.map (Func n) (all (List.map2 term as1 bs1))

                        else
                            Nothing

                    _ ->
                        Nothing

        all ms =
            List.foldr (Maybe.map2 (::)) (Just []) ms

        two c x1 x2 y1 y2 =
            Maybe.map2 c (go x1 y1) (go x2 y2)

        go a b =
            case ( a, b ) of
                ( Pred p ts1, Pred q ts2 ) ->
                    if p == q && List.length ts1 == List.length ts2 then
                        Maybe.map (Pred p) (all (List.map2 term ts1 ts2))

                    else
                        Nothing

                ( Equal a1 a2, Equal b1 b2 ) ->
                    Maybe.map2 Equal (term a1 b1) (term a2 b2)

                ( Neg x, Neg y ) ->
                    Maybe.map Neg (go x y)

                ( Conj x1 x2, Conj y1 y2 ) ->
                    two Conj x1 x2 y1 y2

                ( Disj x1 x2, Disj y1 y2 ) ->
                    two Disj x1 x2 y1 y2

                ( Impl x1 x2, Impl y1 y2 ) ->
                    two Impl x1 x2 y1 y2

                ( Equi x1 x2, Equi y1 y2 ) ->
                    two Equi x1 x2 y1 y2

                ( Forall w x, Forall w2 y ) ->
                    if w == w2 then
                        Maybe.map (Forall w) (go x y)

                    else
                        Nothing

                ( Exists w x, Exists w2 y ) ->
                    if w == w2 then
                        Maybe.map (Exists w) (go x y)

                    else
                        Nothing

                ( Insat, Insat ) ->
                    Just Insat

                ( Taut, Taut ) ->
                    Just Taut

                _ ->
                    Nothing
    in
    go f1 f2


freshVariable : List FormulaFOL -> Variable
freshVariable fs =
    let
        used =
            Set.fromList (List.concatMap FOL_SS.ffolVarSymbols fs)

        candidates =
            List.map (\n -> ( n, [], 0 )) [ "X", "Y", "Z", "U", "V", "W" ]
                ++ List.map (\i -> ( "X", [ i ], 0 )) (List.range 1 100)
    in
    Maybe.withDefault ( "X", [ 999 ], 0 ) (LE.find (\v -> not (Set.member v used)) candidates)


termOf : Env -> TermSchema -> Maybe Term
termOf env t =
    case t of
        TVar x ->
            Maybe.map Var (Dict.get x env.vars)

        TMeta m ->
            Dict.get m env.terms


bindTerm : TermSchema -> Term -> Env -> Maybe Env
bindTerm =
    matchTerm



-- Solves the waiting substitutions. `partial` leaves unsolved the ones that cannot be solved (for hints).


resolve : Bool -> ( Env, List Deferred ) -> Maybe ( Env, List Deferred )
resolve partial ( env, defs ) =
    let
        step d =
            case d of
                ( SSubst a x t, f ) ->
                    case ( instantiate env a, Dict.get x env.vars ) of
                        ( Just g, Just v ) ->
                            case termOf env t of
                                Just tm ->
                                    Just
                                        (if substituteSafe v tm g == Just f then
                                            Just env

                                         else
                                            Nothing
                                        )

                                Nothing ->
                                    case solveTerm v g f of
                                        Just (Just tm) ->
                                            Just
                                                (if substituteSafe v tm g == Just f then
                                                    bindTerm t tm env

                                                 else
                                                    Nothing
                                                )

                                        Just Nothing ->
                                            -- v does not occur free in g: g itself, for any t
                                            Just
                                                (if g == f then
                                                    Just env

                                                 else
                                                    Nothing
                                                )

                                        Nothing ->
                                            Just Nothing

                        _ ->
                            Nothing

                _ ->
                    Just Nothing
    in
    case pickFirst step defs of
        Just ( Just env2, rest ) ->
            resolve partial ( env2, rest )

        Just ( Nothing, _ ) ->
            Nothing

        Nothing ->
            -- nothing can be solved directly: Leibniz law (two substitutions of the same unknown formula)
            case leibniz env defs of
                Just ( env2, rest ) ->
                    resolve partial ( env2, rest )

                Nothing ->
                    if List.isEmpty defs || partial then
                        Just ( env, defs )

                    else
                        Nothing



-- The first element for which f gives an answer, and the other elements.


pickFirst : (a -> Maybe b) -> List a -> Maybe ( b, List a )
pickFirst f xs =
    let
        go before rest =
            case rest of
                [] ->
                    Nothing

                x :: more ->
                    case f x of
                        Just r ->
                            Just ( r, List.reverse before ++ more )

                        Nothing ->
                            go (x :: before) more
    in
    go [] xs


leibniz : Env -> List Deferred -> Maybe ( Env, List Deferred )
leibniz env defs =
    let
        unknownA d =
            case d of
                ( SSubst (SMeta a) x t, f ) ->
                    if Dict.member a env.forms || Dict.member x env.vars then
                        Nothing

                    else
                        Maybe.map (\tm -> ( a, x, ( tm, f ) )) (termOf env t)

                _ ->
                    Nothing

        cands =
            List.filterMap unknownA defs
    in
    case cands of
        ( a, x, ( t1, f1 ) ) :: rest ->
            case LE.find (\( a2, x2, _ ) -> a2 == a && x2 == x) rest of
                Just ( _, _, ( t2, f2 ) ) ->
                    let
                        v =
                            freshVariable [ f1, f2 ]
                    in
                    antiUnify v t1 t2 f1 f2
                        |> Maybe.map
                            (\g ->
                                ( { env | forms = Dict.insert a g env.forms, vars = Dict.insert x v env.vars }, defs )
                            )

                Nothing ->
                    Nothing

        [] ->
            Nothing



-- Matching of a rule: the formula premises with lines, the subproofs with (assumption, end) and the conclusion.


type Item
    = ILine Int FormulaFOL
    | IBox Int Int FormulaFOL FormulaFOL


matchPremise : Premise -> Item -> ( Env, List Deferred ) -> Maybe ( Env, List Deferred )
matchPremise p item st =
    case ( p, item ) of
        ( PFormula s, ILine _ f ) ->
            matchS s f st

        ( PSubproof a c, IBox _ _ fa fc ) ->
            matchS a fa st |> Maybe.andThen (matchS c fc)

        _ ->
            Nothing



--==========--
--  PROOFS  --
--==========--


{-| A line of a proof: its depth (the number of open subproofs it is in), its formula, its rule (`premise`,
`assumption` or the name of a rule) and the lines it cites (`"1, 3"`, `"3-5"`). It is the same as in
`LogicUS.PL.Deduction`.
-}
type alias ProofLine =
    PLD.ProofLine


{-| An exercise: its premises and the formula to prove (if any).
-}
type alias Problem =
    { premises : List FormulaFOL
    , goal : Maybe FormulaFOL
    }


{-| The verdict on a line: its number, its formula (if it could be read) and whether it is correct, with an
explanation.
-}
type alias LineReport =
    { number : Int
    , formula : Maybe FormulaFOL
    , ok : Bool
    , message : String
    }


{-| The verdict on a proof: a report per line, whether the proof is complete (every line is correct and the last one
is the goal, out of every subproof) and a sentence that sums it up.
-}
type alias ProofReport =
    { lines : List LineReport
    , complete : Bool
    , message : String
    }


isPremiseWord : String -> Bool
isPremiseWord w =
    List.member (String.toLower w) [ "premise", "premisa", "p", "pr", "prem" ]


isAssumptionWord : String -> Bool
isAssumptionWord w =
    List.member (String.toLower w) [ "assumption", "supuesto", "a", "hyp", "hip", "hipótesis", "hipotesis", "sup" ]


{-| It reads a proof written as text, a line per formula (see the beginning of the module). It is
`LogicUS.PL.Deduction.readProof`.
-}
readProof : String -> List ProofLine
readProof =
    PLD.readProof


{-| It writes a proof as text, with its line numbers and bars.
-}
proofToString : List ProofLine -> String
proofToString =
    PLD.proofToString


type Ref
    = RLine Int
    | RRange Int Int


readRefs : String -> Result String (List Ref)
readRefs s =
    s
        |> String.replace "–" "-"
        |> String.replace " " ","
        |> String.split ","
        |> List.filter (not << String.isEmpty)
        |> List.foldr
            (\part acc ->
                case ( String.split "-" part, acc ) of
                    ( [ a ], Ok rs ) ->
                        case String.toInt a of
                            Just n ->
                                Ok (RLine n :: rs)

                            Nothing ->
                                Err ("'" ++ part ++ "' is not a line number")

                    ( [ a, b ], Ok rs ) ->
                        case ( String.toInt a, String.toInt b ) of
                            ( Just n, Just m ) ->
                                Ok (RRange n m :: rs)

                            _ ->
                                Err ("'" ++ part ++ "' is not a range of lines")

                    ( _, Err e ) ->
                        Err e

                    _ ->
                        Err ("'" ++ part ++ "' is not a line number")
            )
            (Ok [])



-- The structure of a proof: for each line, the subproofs it is in (their first lines, outermost first); for each
-- subproof, its last line.


type alias Structure =
    { paths : Dict Int (List Int)
    , ends : Dict Int Int
    , errors : Dict Int String
    , openAtEnd : List Int
    }


type Just
    = JPremise
    | JAssumption
    | JRule String


justification : ProofLine -> Just
justification l =
    if isPremiseWord l.rule && String.isEmpty (String.trim l.refs) then
        JPremise

    else if isAssumptionWord l.rule && String.isEmpty (String.trim l.refs) then
        JAssumption

    else
        JRule l.rule


structure : List ProofLine -> Structure
structure ls =
    let
        step ( n, l ) ( st, stack ) =
            let
                closeTo d stk acc =
                    if List.length stk > d then
                        case stk of
                            b :: more ->
                                closeTo d more { acc | ends = Dict.insert b (n - 1) acc.ends }

                            [] ->
                                ( stk, acc )

                    else
                        ( stk, acc )

                current =
                    List.length stack
            in
            case justification l of
                JAssumption ->
                    if l.depth < 1 || l.depth > current + 1 then
                        ( { st | errors = Dict.insert n "an assumption opens a subproof: it has one bar more than the line it follows, or as many as a subproof that ends before it" st.errors, paths = Dict.insert n (List.reverse stack) st.paths }, stack )

                    else
                        let
                            ( stk, st2 ) =
                                closeTo (l.depth - 1) stack st
                        in
                        ( { st2 | paths = Dict.insert n (List.reverse (n :: stk)) st2.paths }, n :: stk )

                _ ->
                    if l.depth > current then
                        ( { st | errors = Dict.insert n "this line has more bars than the open subproofs (a subproof starts with an assumption)" st.errors, paths = Dict.insert n (List.reverse stack) st.paths }, stack )

                    else
                        let
                            ( stk, st2 ) =
                                closeTo l.depth stack st
                        in
                        ( { st2 | paths = Dict.insert n (List.reverse stk) st2.paths }, stk )

        ( final, openStack ) =
            List.foldl step ( { paths = Dict.empty, ends = Dict.empty, errors = Dict.empty, openAtEnd = [] }, [] ) (List.indexedMap (\i l -> ( i + 1, l )) ls)

        lastN =
            List.length ls
    in
    { final | ends = List.foldl (\b acc -> Dict.insert b lastN acc) final.ends openStack, openAtEnd = openStack }


isPrefix : List a -> List a -> Bool
isPrefix xs ys =
    List.take (List.length xs) ys == xs



-- The lines and closed subproofs that the line n can cite (lines before it out of closed subproofs).


accessible : Structure -> Dict Int FormulaFOL -> Int -> List Int -> ( List Item, List Int )
accessible st forms n path =
    let
        lines =
            List.range 1 (n - 1)
                |> List.filter (\i -> isPrefix (Maybe.withDefault [] (Dict.get i st.paths)) path)

        boxes =
            Dict.toList st.ends
                |> List.filter
                    (\( b, e ) ->
                        e < n && isPrefix (List.reverse (List.drop 1 (List.reverse (Maybe.withDefault [] (Dict.get b st.paths))))) path
                    )

        lineItems =
            List.filterMap (\i -> Maybe.map (ILine i) (Dict.get i forms)) lines

        boxItems =
            List.filterMap (\( b, e ) -> Maybe.map2 (IBox b e) (Dict.get b forms) (Dict.get e forms)) boxes
    in
    ( lineItems ++ boxItems, lines )


refToItem : Structure -> Dict Int FormulaFOL -> Int -> List Int -> Ref -> Result String Item
refToItem st forms n path ref =
    case ref of
        RLine i ->
            if i >= n || i < 1 then
                Err ("line " ++ String.fromInt n ++ " can only cite lines above it, not " ++ String.fromInt i)

            else if not (isPrefix (Maybe.withDefault [] (Dict.get i st.paths)) path) then
                Err ("line " ++ String.fromInt i ++ " is inside a closed subproof, and cannot be used here")

            else
                case Dict.get i forms of
                    Just f ->
                        Ok (ILine i f)

                    Nothing ->
                        Err ("line " ++ String.fromInt i ++ " cannot be read")

        RRange a b ->
            case Dict.get a st.ends of
                Nothing ->
                    Err ("line " ++ String.fromInt a ++ " does not open a subproof (an assumption does)")

                Just e ->
                    if e /= b then
                        Err ("the subproof that starts at line " ++ String.fromInt a ++ " ends at line " ++ String.fromInt e ++ ", not at " ++ String.fromInt b)

                    else if e >= n then
                        Err ("the subproof " ++ String.fromInt a ++ "-" ++ String.fromInt b ++ " is not closed before line " ++ String.fromInt n)

                    else if not (isPrefix (List.reverse (List.drop 1 (List.reverse (Maybe.withDefault [] (Dict.get a st.paths))))) path) then
                        Err ("the subproof " ++ String.fromInt a ++ "-" ++ String.fromInt b ++ " is inside a closed subproof, and cannot be used here")

                    else
                        case ( Dict.get a forms, Dict.get b forms ) of
                            ( Just fa, Just fb ) ->
                                Ok (IBox a b fa fb)

                            _ ->
                                Err ("the subproof " ++ String.fromInt a ++ "-" ++ String.fromInt b ++ " has lines that cannot be read")



-- The open assumptions and premises at line n.


openFormulas : Structure -> Dict Int FormulaFOL -> List ProofLine -> List Int -> List FormulaFOL
openFormulas st forms ls path =
    let
        premises =
            ls
                |> List.indexedMap (\i l -> ( i + 1, l ))
                |> List.filter (\( _, l ) -> justification l == JPremise)
                |> List.filterMap (\( i, _ ) -> Dict.get i forms)
    in
    premises ++ List.filterMap (\b -> Dict.get b forms) path


termsOfFormula : FormulaFOL -> List Term
termsOfFormula f =
    let
        sub t =
            case t of
                Func _ ts ->
                    t :: List.concatMap sub ts

                Var _ ->
                    [ t ]

        atom ts =
            List.concatMap sub ts
    in
    case f of
        Pred _ ts ->
            atom ts

        Equal a b ->
            atom [ a, b ]

        Neg a ->
            termsOfFormula a

        Conj a b ->
            termsOfFormula a ++ termsOfFormula b

        Disj a b ->
            termsOfFormula a ++ termsOfFormula b

        Impl a b ->
            termsOfFormula a ++ termsOfFormula b

        Equi a b ->
            termsOfFormula a ++ termsOfFormula b

        Forall _ a ->
            termsOfFormula a

        Exists _ a ->
            termsOfFormula a

        _ ->
            []



-- Whether a term occurs (free, for variables) in a formula.


occursIn : Term -> FormulaFOL -> Bool
occursIn t f =
    case t of
        Var v ->
            List.member v (FOL_SS.ffolFreeVars f)

        _ ->
            List.member t (termsOfFormula f)



-- The side conditions of a rule, once matched: Nothing if they hold, or the reason why not.


checkConditions : Rule -> Env -> FormulaFOL -> List FormulaFOL -> Maybe String
checkConditions rule env concl open =
    let
        -- the formulas A of the substitutions A[x/a] of the rule
        bodiesWith a =
            List.filterMap
                (\s ->
                    case s of
                        SSubst (SMeta f) _ (TMeta m) ->
                            if m == a then
                                Dict.get f env.forms

                            else
                                Nothing

                        _ ->
                            Nothing
                )
                (List.concatMap premiseSchemas rule.premises)

        one c =
            case c of
                Fresh a ->
                    case Dict.get a env.terms of
                        Just t ->
                            let
                                tStr =
                                    FOL_SS.termToString t

                                simple =
                                    case t of
                                        Var _ ->
                                            True

                                        Func _ [] ->
                                            True

                                        _ ->
                                            False
                            in
                            if not simple then
                                Just (tStr ++ " must be a variable or a constant")

                            else if occursIn t concl then
                                Just (tStr ++ " cannot occur in the conclusion of " ++ rule.name)

                            else if List.any (occursIn t) (bodiesWith a) then
                                Just (tStr ++ " must be new: it occurs in the formula that " ++ rule.name ++ " generalizes")

                            else
                                case LE.find (occursIn t) open of
                                    Just f ->
                                        Just (tStr ++ " must be new: it occurs in the premise or open assumption " ++ FOL_SS.ffolToString f)

                                    Nothing ->
                                        Nothing

                        Nothing ->
                            Nothing

                NotFree x a ->
                    case ( Dict.get x env.vars, Dict.get a env.forms ) of
                        ( Just v, Just f ) ->
                            if List.member v (FOL_SS.ffolFreeVars f) then
                                Just (FOL_SS.termToString (Var v) ++ " cannot occur free in " ++ FOL_SS.ffolToString f)

                            else
                                Nothing

                        _ ->
                            Nothing
    in
    List.head (List.filterMap one rule.conditions)


premiseSchemas : Premise -> List Schema
premiseSchemas p =
    let
        subs s =
            case s of
                SSubst _ _ _ ->
                    [ s ]

                SNot a ->
                    subs a

                SAnd a b ->
                    subs a ++ subs b

                SOr a b ->
                    subs a ++ subs b

                SImp a b ->
                    subs a ++ subs b

                SIff a b ->
                    subs a ++ subs b

                SAll _ a ->
                    subs a

                SEx _ a ->
                    subs a

                _ ->
                    []
    in
    case p of
        PFormula s ->
            subs s

        PSubproof a b ->
            subs a ++ subs b



-- The ways of matching the cited items with the premises (in any order), with the conclusion.


matchRule : Rule -> List Item -> Maybe FormulaFOL -> Bool -> List ( Env, List Deferred )
matchRule rule items concl partial =
    let
        start =
            case concl of
                Just f ->
                    matchS rule.conclusion f ( emptyEnv, [] )

                Nothing ->
                    Just ( emptyEnv, [] )

        assign ps its st =
            case ps of
                [] ->
                    if List.isEmpty its then
                        [ st ]

                    else
                        []

                p :: more ->
                    its
                        |> LE.select
                        |> List.concatMap
                            (\( it, others ) ->
                                case matchPremise p it st of
                                    Just st2 ->
                                        assign more others st2

                                    Nothing ->
                                        []
                            )
    in
    case start of
        Just st ->
            assign rule.premises items st
                |> List.filterMap (resolve partial)

        Nothing ->
            []


{-| It checks a proof with the rules of a system. The premises of the proof must be premises of the problem (if it
has any), and the proof is complete when it ends with the goal.
-}
checkProof : System -> Problem -> List ProofLine -> ProofReport
checkProof sys problem ls =
    let
        numbered =
            List.indexedMap (\i l -> ( i + 1, l )) ls

        parsed =
            List.map (\( n, l ) -> ( n, readFormula l.formula )) numbered

        forms =
            Dict.fromList (List.filterMap (\( n, r ) -> Result.toMaybe r |> Maybe.map (Tuple.pair n)) parsed)

        st =
            structure ls

        checkLine ( n, l ) =
            let
                path =
                    Maybe.withDefault [] (Dict.get n st.paths)

                formula =
                    Dict.get n forms

                report ok msg =
                    { number = n, formula = formula, ok = ok, message = msg }
            in
            case ( readFormula l.formula, Dict.get n st.errors ) of
                ( Err e, _ ) ->
                    report False e

                ( _, Just e ) ->
                    report False e

                ( Ok f, Nothing ) ->
                    case justification l of
                        JPremise ->
                            if l.depth /= 0 then
                                report False "a premise cannot be inside a subproof"

                            else if not (List.isEmpty problem.premises) && not (List.member f problem.premises) then
                                report False "this formula is not a premise of the exercise"

                            else
                                report True "premise"

                        JAssumption ->
                            report True "assumption"

                        JRule name ->
                            if String.isEmpty name then
                                report False "the line needs a justification: premise, assumption, or a rule and the lines it uses"

                            else
                                case findRule sys name of
                                    Nothing ->
                                        report False ("the rule " ++ name ++ " is not one of the rules of this system")

                                    Just rule ->
                                        case readRefs l.refs of
                                            Err e ->
                                                report False e

                                            Ok refs ->
                                                case collect (List.map (refToItem st forms n path) refs) of
                                                    Err e ->
                                                        report False e

                                                    Ok items ->
                                                        checkStep rule items f (openFormulas st forms ls path) report
    in
    let
        lineReports =
            List.map checkLine numbered

        lastOk =
            case List.reverse numbered of
                ( n, l ) :: _ ->
                    if l.depth /= 0 || not (List.isEmpty st.openAtEnd) then
                        Err "the proof ends inside a subproof"

                    else
                        case problem.goal of
                            Just g ->
                                if Dict.get n forms == Just g then
                                    Ok ()

                                else
                                    Err ("the proof does not end with the goal " ++ FOL_SS.ffolToString g)

                            Nothing ->
                                Ok ()

                [] ->
                    Err "the proof is empty"

        allOk =
            List.all .ok lineReports

        message =
            case ( allOk, lastOk ) of
                ( True, Ok () ) ->
                    "The proof is correct and complete."

                ( True, Err e ) ->
                    "Every line is correct, but " ++ e ++ "."

                ( False, _ ) ->
                    let
                        bad =
                            List.filter (not << .ok) lineReports |> List.map (String.fromInt << .number)
                    in
                    "Wrong lines: " ++ String.join ", " bad ++ "."
    in
    { lines = lineReports, complete = allOk && lastOk == Ok (), message = message }


collect : List (Result String a) -> Result String (List a)
collect rs =
    List.foldr (Result.map2 (::)) (Ok []) rs


checkStep : Rule -> List Item -> FormulaFOL -> List FormulaFOL -> (Bool -> String -> LineReport) -> LineReport
checkStep rule items f open report =
    if List.length items /= List.length rule.premises then
        report False
            (rule.name
                ++ " uses "
                ++ String.fromInt (List.length rule.premises)
                ++ (if List.length rule.premises == 1 then
                        " premise"

                    else
                        " premises"
                   )
                ++ (if List.isEmpty rule.premises then
                        ""

                    else
                        ": " ++ String.join ", " (List.map premiseToString rule.premises)
                   )
            )

    else
        case matchRule rule items (Just f) False of
            [] ->
                report False (rule.name ++ " (" ++ ruleShape rule ++ ") does not give this formula from " ++ String.join ", " (List.map itemRef items))

            matches ->
                case List.filterMap (\( env, _ ) -> checkConditions rule env f open) matches of
                    reasons ->
                        if List.length reasons < List.length matches then
                            report True rule.name

                        else
                            report False (Maybe.withDefault "a side condition does not hold" (List.head reasons))


ruleShape : Rule -> String
ruleShape rule =
    String.join ", " (List.map premiseToString rule.premises) ++ " ⊢ " ++ schemaToString rule.conclusion


premiseToString : Premise -> String
premiseToString p =
    case p of
        PFormula s ->
            schemaToString s

        PSubproof a b ->
            "[" ++ schemaToString a ++ "] " ++ schemaToString b



--=========--
--  HINTS  --
--=========--


{-| The kind of a hint: a rule applied to the accessible lines and subproofs, a rule that closes the current
subproof, or a rule that would give the target.
-}
type HintKind
    = Forward
    | CloseSubproof
    | Backward


{-| A hint: the rule, the lines it uses (`refs`), the formula it gives (`result`; unknown parts are written `?A`,
`?t`), the same formula in the syntax of the proofs (`input`, empty when it has unknown parts), for backward hints
what is still needed and the assumptions of the subproofs it needs (in the syntax of the proofs, when they are
known), and a sentence that explains it.
-}
type alias Hint =
    { kind : HintKind
    , rule : String
    , refs : String
    , result : String
    , input : String
    , needs : List String
    , assumptions : List String
    , text : String
    }


partialToString : Env -> Schema -> String
partialToString env s =
    case instantiate (withPlaceholders env s) s of
        Just f ->
            FOL_SS.ffolToString f

        Nothing ->
            schemaToString s



-- The unknown parts of a schema become placeholders ?A, ?t, ?x, so that it can be written.


withPlaceholders : Env -> Schema -> Env
withPlaceholders env s =
    let
        term t e =
            case t of
                TVar x ->
                    if Dict.member x e.vars then
                        e

                    else
                        { e | vars = Dict.insert x ( "?" ++ x, [], 0 ) e.vars }

                TMeta m ->
                    if Dict.member m e.terms then
                        e

                    else
                        { e | terms = Dict.insert m (Func ( "?" ++ m, [] ) []) e.terms }

        go x e =
            case x of
                SMeta a ->
                    if Dict.member a e.forms then
                        e

                    else
                        { e | forms = Dict.insert a (Pred ( "?" ++ a, [] ) []) e.forms }

                SNot a ->
                    go a e

                SAnd a b ->
                    go b (go a e)

                SOr a b ->
                    go b (go a e)

                SImp a b ->
                    go b (go a e)

                SIff a b ->
                    go b (go a e)

                SAll v a ->
                    go a (term (TVar v) e)

                SEx v a ->
                    go a (term (TVar v) e)

                SEq a b ->
                    term b (term a e)

                SSubst a v t ->
                    term t (term (TVar v) (go a e))

                _ ->
                    e
    in
    go s env


itemRef : Item -> String
itemRef it =
    case it of
        ILine n _ ->
            String.fromInt n

        IBox a b _ _ ->
            String.fromInt a ++ "-" ++ String.fromInt b


{-| The rules of the system that can be used at the end of a proof:

  - `CloseSubproof`: a rule that closes the subproof that is open at the end, using it;
  - `Backward`: a rule whose conclusion is the target (or the goal of the problem, when no subproof is open), with
    what it still needs; the parts of the premises that are lines of the proof are taken from them;
  - `Forward`: a rule whose premises are lines and closed subproofs that can be cited there, when its result is
    useful: part of the target or of a cited line, or ⊥.

Only the correct lines are used. Rules that only copy a line, and results that are already lines that can be cited,
are left out. At most `limit` hints of each kind are given.

-}
hints : System -> Problem -> List ProofLine -> Maybe FormulaFOL -> Int -> List Hint
hints sys problem ls target limit =
    let
        n =
            List.length ls + 1

        -- only the correct lines can be used
        forms =
            (checkProof sys problem ls).lines
                |> List.filterMap
                    (\r ->
                        if r.ok then
                            Maybe.map (Tuple.pair r.number) r.formula

                        else
                            Nothing
                    )
                |> Dict.fromList

        st =
            structure ls

        path =
            List.reverse st.openAtEnd

        ( items, _ ) =
            accessible st forms n path

        available =
            List.filterMap
                (\it ->
                    case it of
                        ILine _ f ->
                            Just f

                        _ ->
                            Nothing
                )
                items

        open =
            openFormulas st forms ls path

        goal =
            case target of
                Just t ->
                    Just t

                Nothing ->
                    if List.isEmpty path then
                        problem.goal

                    else
                        Nothing

        -- the parts of the goal that could be lines (without variables bound in the goal)
        goalParts =
            case goal of
                Just g ->
                    let
                        free =
                            FOL_SS.ffolFreeVars g
                    in
                    List.filter (\h -> List.all (\v -> List.member v free) (FOL_SS.ffolFreeVars h)) (subformulas g)

                Nothing ->
                    []

        useful rule =
            not (List.length rule.premises == 1 && rule.premises == [ PFormula rule.conclusion ])

        refsOf chosen =
            String.join ", " (List.map itemRef chosen)

        -- applications of a rule to some items (the conclusion is left free)
        applications rule its =
            if List.length rule.premises > List.length its then
                []

            else
                choose (List.length rule.premises) its
                    |> List.concatMap (\chosen -> matchRule rule chosen Nothing True |> List.map (\m -> ( chosen, m )))

        -- the formulas that an application gives: its conclusion, or the parts of the target that it can give; a
        -- conclusion that only lacks terms (∀E) is given with placeholders (P(?t))
        resultsOf rule openFs ( chosen, ( env, defs ) ) =
            let
                valid f e =
                    not (List.member f available) && checkConditions rule e f openFs == Nothing

                fromGoal =
                    goalParts
                        |> List.filterMap
                            (\g ->
                                matchS rule.conclusion g ( env, defs )
                                    |> Maybe.andThen (resolve False)
                                    |> Maybe.andThen
                                        (\( e2, _ ) ->
                                            if valid g e2 then
                                                Just ( chosen, Just g, FOL_SS.ffolToString g )

                                            else
                                                Nothing
                                        )
                            )
            in
            case ( instantiate env rule.conclusion, defs ) of
                ( Just f, [] ) ->
                    if valid f env then
                        [ ( chosen, Just f, FOL_SS.ffolToString f ) ]

                    else
                        []

                _ ->
                    if List.isEmpty fromGoal && Set.isEmpty (Set.diff (schemaMetas rule.conclusion) (Set.fromList (Dict.keys env.forms))) then
                        [ ( chosen, Nothing, partialToString env rule.conclusion ) ]

                    else
                        fromGoal

        relevant chosen mf =
            case mf of
                Nothing ->
                    True

                Just f ->
                    relevantFormula chosen f

        relevantFormula chosen f =
            f
                == Insat
                || List.member f goalParts
                || List.any
                    (\it ->
                        case it of
                            ILine _ g ->
                                List.member f (subformulas g)

                            IBox _ _ a c ->
                                List.member f (subformulas a ++ subformulas c)
                    )
                    chosen

        hint kind rule chosen mf res txt =
            { kind = kind, rule = rule.name, refs = refsOf chosen, result = res, input = Maybe.withDefault "" (Maybe.map formulaToInputString mf), needs = [], assumptions = [], text = txt }

        forward =
            sys
                |> List.filter (\r -> useful r && not (List.isEmpty r.premises))
                |> List.concatMap
                    (\rule ->
                        applications rule items
                            |> List.concatMap (resultsOf rule open)
                            |> List.filter (\( chosen, mf, _ ) -> relevant chosen mf)
                            |> LE.uniqueBy (\( c, _, res ) -> ( List.map itemRef c, res ))
                            |> List.map (\( chosen, mf, res ) -> hint Forward rule chosen mf res (rule.name ++ " " ++ refsOf chosen ++ " gives " ++ res))
                    )
                |> List.take limit

        closeParts =
            case ( target, problem.goal ) of
                ( Just t, _ ) ->
                    subformulas t

                ( Nothing, Just g ) ->
                    subformulas g

                _ ->
                    []

        -- closing the innermost subproof at the last line
        closing =
            case st.openAtEnd of
                b :: _ ->
                    let
                        outerPath =
                            List.take (List.length path - 1) path

                        ( outerItems, _ ) =
                            accessible st forms n outerPath

                        outerOpen =
                            openFormulas st forms ls outerPath
                    in
                    case Maybe.map2 (IBox b (n - 1)) (Dict.get b forms) (Dict.get (n - 1) forms) of
                        Just box ->
                            sys
                                |> List.filter (\r -> List.any isSubproof r.premises)
                                |> List.concatMap
                                    (\rule ->
                                        applications rule (box :: List.filter (\it -> itemRef it /= itemRef box) outerItems)
                                            |> List.filter (\( chosen, _ ) -> List.member box chosen)
                                            |> List.concatMap (resultsOf rule outerOpen)
                                            |> List.filter
                                                (\( _, mf, _ ) ->
                                                    case mf of
                                                        Just f ->
                                                            f == Insat || List.member f closeParts || List.any (\g -> List.member f (subformulas g)) available

                                                        Nothing ->
                                                            False
                                                )
                                            |> LE.uniqueBy (\( c, _, res ) -> ( List.map itemRef c, res ))
                                            |> List.map
                                                (\( chosen, mf, res ) ->
                                                    hint CloseSubproof rule chosen mf res ("close the subproof " ++ itemRef box ++ " and apply " ++ rule.name ++ " " ++ refsOf chosen ++ ": " ++ res)
                                                )
                                    )
                                |> List.take limit

                        Nothing ->
                            []

                [] ->
                    []

        lineOf f =
            LE.findMap
                (\it ->
                    case it of
                        ILine i f2 ->
                            if f2 == f then
                                Just i

                            else
                                Nothing

                        _ ->
                            Nothing
                )
                items

        -- the ways of taking the formula premises of a rule from the lines (or leaving them to be proved)
        fill state ps =
            case ps of
                [] ->
                    [ Tuple.first state ]

                (PFormula s) :: more ->
                    let
                        fromLines =
                            available
                                |> List.filterMap (\f -> matchS s f state |> Maybe.andThen (resolve True))
                    in
                    (fromLines ++ [ state ]) |> List.concatMap (\st2 -> fill st2 more)

                (PSubproof _ _) :: more ->
                    fill state more

        backward =
            case goal |> Maybe.andThen (\g -> if List.member g available then Nothing else Just g) of
                Just g ->
                    let
                        gs =
                            FOL_SS.ffolToString g
                    in
                    sys
                        |> List.filter useful
                        |> List.concatMap
                            (\rule ->
                                case matchS rule.conclusion g ( emptyEnv, [] ) |> Maybe.andThen (resolve True) of
                                    Just state ->
                                        fill state rule.premises
                                            |> List.map (\e -> ( rule, e ))

                                    Nothing ->
                                        []
                            )
                        |> List.filterMap
                            (\( rule, env ) ->
                                let
                                    formulaPremises =
                                        List.filterMap
                                            (\p ->
                                                case p of
                                                    PFormula s ->
                                                        Just s

                                                    _ ->
                                                        Nothing
                                            )
                                            rule.premises

                                    have =
                                        List.filterMap (\s -> instantiate env s |> Maybe.andThen lineOf) formulaPremises

                                    structural =
                                        case rule.conclusion of
                                            SMeta _ ->
                                                False

                                            SSubst _ _ _ ->
                                                False

                                            _ ->
                                                True

                                    subproofOnly =
                                        List.isEmpty formulaPremises && not (List.isEmpty rule.premises)

                                    -- the premises that contain the conclusion (A → B in →E): one of them must be a line
                                    concMetas =
                                        schemaMetas rule.conclusion

                                    major =
                                        List.filter (\sch -> not (Set.isEmpty (Set.intersect concMetas (schemaMetas sch)))) formulaPremises

                                    majorAvailable =
                                        if List.isEmpty major then
                                            not (List.isEmpty have)

                                        else
                                            List.any (\sch -> instantiate env sch |> Maybe.andThen lineOf |> (/=) Nothing) major

                                    need p =
                                        case p of
                                            PFormula s ->
                                                case instantiate env s |> Maybe.andThen lineOf of
                                                    Just i ->
                                                        partialToString env s ++ " (line " ++ String.fromInt i ++ ")"

                                                    Nothing ->
                                                        partialToString env s

                                            PSubproof a c ->
                                                "a subproof from the assumption " ++ partialToString env a ++ " to " ++ partialToString env c

                                    needs =
                                        List.map need rule.premises
                                in
                                if checkConditions rule env g open /= Nothing then
                                    Nothing

                                else if structural || subproofOnly || majorAvailable then
                                    Just
                                        ( List.length have
                                        , { kind = Backward
                                          , rule = rule.name
                                          , refs = ""
                                          , result = gs
                                          , input = formulaToInputString g
                                          , needs = needs
                                          , assumptions =
                                                List.filterMap
                                                    (\p ->
                                                        case p of
                                                            PSubproof a _ ->
                                                                Maybe.map formulaToInputString (instantiate env a)

                                                            _ ->
                                                                Nothing
                                                    )
                                                    rule.premises
                                          , text =
                                                if List.isEmpty needs then
                                                    rule.name ++ " gives " ++ gs ++ " directly"

                                                else
                                                    rule.name ++ " gives " ++ gs ++ " from " ++ String.join "; " needs
                                          }
                                        )

                                else
                                    Nothing
                            )
                        |> LE.uniqueBy (\( _, h ) -> h.text)
                        |> List.sortBy (\( k, _ ) -> negate k)
                        |> List.map Tuple.second
                        |> List.take limit

                Nothing ->
                    []
        backwardDone =
            List.filter (\h -> not (List.isEmpty h.needs) && List.all (String.endsWith ")") h.needs && List.all (String.contains "(line ") h.needs) backward
                |> List.map (\h -> ( h.rule, h.result ))
    in
    closing ++ backward ++ List.filter (\h -> not (List.member ( h.rule, h.result ) backwardDone)) forward


schemaMetas : Schema -> Set String
schemaMetas s =
    case s of
        SMeta a ->
            Set.singleton a

        SNot a ->
            schemaMetas a

        SAnd a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SOr a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SImp a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SIff a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SAll _ a ->
            schemaMetas a

        SEx _ a ->
            schemaMetas a

        SSubst a _ _ ->
            schemaMetas a

        _ ->
            Set.empty


subformulas : FormulaFOL -> List FormulaFOL
subformulas f =
    f
        :: (case f of
                Neg a ->
                    subformulas a

                Conj a b ->
                    subformulas a ++ subformulas b

                Disj a b ->
                    subformulas a ++ subformulas b

                Impl a b ->
                    subformulas a ++ subformulas b

                Equi a b ->
                    subformulas a ++ subformulas b

                Forall _ a ->
                    subformulas a

                Exists _ a ->
                    subformulas a

                _ ->
                    []
           )


isSubproof : Premise -> Bool
isSubproof p =
    case p of
        PSubproof _ _ ->
            True

        _ ->
            False



-- The sublists of k elements (in order).


choose : Int -> List a -> List (List a)
choose k xs =
    if k == 0 then
        [ [] ]

    else
        case xs of
            [] ->
                []

            x :: rest ->
                List.map ((::) x) (choose (k - 1) rest) ++ choose k rest
