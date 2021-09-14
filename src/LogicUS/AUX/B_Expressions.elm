module LogicUS.AUX.B_Expressions exposing (B_Expr(..), evaluateBExpr, expressionB, parseBExpr, toMathStringBExpr, toStringBExpr, varsInB_Expr)

import Dict exposing (Dict)
import LogicUS.AUX.A_Expressions exposing (..)
import LogicUS.AUX.AuxiliarFuctions exposing (uniqueConcatList)
import Parser exposing (..)


type Comparator
    = EQ
    | NE
    | GT
    | LT
    | GE
    | LE


type alias Condition =
    { comp : Comparator
    , e1 : A_Expr
    , e2 : A_Expr
    }


createCondition : A_Expr -> Comparator -> A_Expr -> Condition
createCondition f c s =
    { comp = c, e1 = f, e2 = s }


compCondition : Parser Comparator
compCondition =
    oneOf
        [ succeed GE
            |. symbol ">="
        , succeed LE
            |. symbol "<="
        , succeed NE
            |. symbol "!="
        , succeed GT
            |. symbol ">"
        , succeed LT
            |. symbol "<"
        , succeed EQ
            |. symbol "="
        ]


condition : Parser Condition
condition =
    succeed createCondition
        |= expressionA
        |= compCondition
        |= expressionA


evalCond : Condition -> Dict String Int -> Maybe Bool
evalCond c vals =
    case c.comp of
        EQ ->
            Maybe.map2 (==) (evaluateAExpr c.e1 vals) (evaluateAExpr c.e2 vals)

        NE ->
            Maybe.map2 (/=) (evaluateAExpr c.e1 vals) (evaluateAExpr c.e2 vals)

        GT ->
            Maybe.map2 (>) (evaluateAExpr c.e1 vals) (evaluateAExpr c.e2 vals)

        LT ->
            Maybe.map2 (<) (evaluateAExpr c.e1 vals) (evaluateAExpr c.e2 vals)

        GE ->
            Maybe.map2 (>=) (evaluateAExpr c.e1 vals) (evaluateAExpr c.e2 vals)

        LE ->
            Maybe.map2 (<=) (evaluateAExpr c.e1 vals) (evaluateAExpr c.e2 vals)


type B_Expr
    = T
    | F
    | And B_Expr B_Expr
    | Or B_Expr B_Expr
    | Not B_Expr
    | Cond Condition


type B_Operator
    = AndOp
    | OrOp


operatorB : Parser B_Operator
operatorB =
    oneOf
        [ Parser.map (\_ -> AndOp) (symbol "AND")
        , Parser.map (\_ -> OrOp) (symbol "OR")
        ]


evaluateBExpr : B_Expr -> Dict String Int -> Maybe Bool
evaluateBExpr expr vals =
    case expr of
        T ->
            Just True

        F ->
            Just False

        And e1 e2 ->
            Maybe.map2 (&&) (evaluateBExpr e1 vals) (evaluateBExpr e2 vals)

        Or e1 e2 ->
            Maybe.map2 (||) (evaluateBExpr e1 vals) (evaluateBExpr e2 vals)

        Not e ->
            Maybe.map not (evaluateBExpr e vals)

        Cond c ->
            evalCond c vals


varsInB_Expr : B_Expr -> List String
varsInB_Expr expr =
    case expr of
        T ->
            []

        F ->
            []

        And e1 e2 ->
            uniqueConcatList (varsInB_Expr e1) (varsInB_Expr e2)

        Or e1 e2 ->
            uniqueConcatList (varsInB_Expr e1) (varsInB_Expr e2)

        Not e1 ->
            varsInB_Expr e1

        Cond c ->
            uniqueConcatList (varsInA_Expr c.e1) (varsInA_Expr c.e2)


parseBExpr : String -> ( Maybe B_Expr, String )
parseBExpr str =
    if str == "" then
        ( Nothing, "Empty expression" )

    else
        case run expressionB str of
            Ok y ->
                ( Just y, "" )

            Err m ->
                ( Nothing, Debug.toString m )


termBExpr : Parser B_Expr
termBExpr =
    oneOf
        [ succeed T
            |. symbol "T"
        , succeed F
            |. symbol "F"
        , succeed Not
            |. symbol "NOT"
            |= lazy (\_ -> expressionB)
        , succeed Cond
            |. symbol "["
            |= condition
            |. symbol "]"
        , succeed identity
            |. symbol "("
            |= lazy (\_ -> expressionB)
            |. symbol ")"
        ]


expressionB : Parser B_Expr
expressionB =
    termBExpr |> andThen (expressionBAux [])


expressionBAux : List ( B_Expr, B_Operator ) -> B_Expr -> Parser B_Expr
expressionBAux revOps bExpr =
    oneOf
        [ succeed Tuple.pair
            |= operatorB
            |= termBExpr
            |> andThen (\( op, newExpr ) -> expressionBAux (( bExpr, op ) :: revOps) newExpr)
        , lazy (\_ -> succeed (finalize revOps bExpr))
        ]


finalize : List ( B_Expr, B_Operator ) -> B_Expr -> B_Expr
finalize revOps finalExpr =
    case revOps of
        [] ->
            finalExpr

        -- And operation have the maximum priorty, so module have a unique case
        ( expr, AndOp ) :: otherRevOps ->
            finalize otherRevOps (And expr finalExpr)

        -- Or have the second maximum priority, so we need to determine how parser's going to do if it searches a module after and if it searches something different
        ( expr, OrOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Or (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, OrOp ) :: otherRevOps ->
            finalize otherRevOps (Or expr finalExpr)


toStringComparator : Comparator -> String
toStringComparator c =
    case c of
        EQ ->
            "="

        NE ->
            "!="

        GT ->
            ">"

        LT ->
            "<"

        GE ->
            ">="

        LE ->
            "<="


toMathStringComparator : Comparator -> String
toMathStringComparator c =
    case c of
        EQ ->
            "= "

        NE ->
            "\\neq "

        GT ->
            "> "

        LT ->
            "< "

        GE ->
            "\\geq "

        LE ->
            "\\leq "


toStringCondition : Condition -> String
toStringCondition c =
    toStringAExpr c.e1 ++ toStringComparator c.comp ++ toStringAExpr c.e2


toMathStringCondition : Condition -> String
toMathStringCondition c =
    toMathStringAExpr c.e1 ++ toMathStringComparator c.comp ++ toMathStringAExpr c.e2


toStringBExpr : B_Expr -> String
toStringBExpr bexpr =
    case bexpr of
        T ->
            "T"

        F ->
            "F"

        And e1 e2 ->
            "(" ++ toStringBExpr e1 ++ "AND" ++ toStringBExpr e2 ++ ")"

        Or e1 e2 ->
            "(" ++ toStringBExpr e1 ++ "OR" ++ toStringBExpr e2 ++ ")"

        Not e ->
            "( NOT" ++ toStringBExpr e ++ ")"

        Cond c ->
            "[" ++ toStringCondition c ++ "]"


toMathStringBExpr : B_Expr -> String
toMathStringBExpr bexpr =
    case bexpr of
        T ->
            "T"

        F ->
            "F"

        And e1 e2 ->
            "(" ++ toMathStringBExpr e1 ++ "\\wedge " ++ toMathStringBExpr e2 ++ ")"

        Or e1 e2 ->
            "(" ++ toMathStringBExpr e1 ++ "\\vee " ++ toMathStringBExpr e2 ++ ")"

        Not e ->
            "( \\neg " ++ toMathStringBExpr e ++ ")"

        Cond c ->
            "[" ++ toMathStringCondition c ++ "]"
