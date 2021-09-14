module LogicUS.AUX.A_Expressions exposing (A_Expr, evaluateAExpr, expressionA, parseAExpr, toMathStringAExpr, toStringAExpr, varsInA_Expr)

import Dict exposing (Dict)
import LogicUS.AUX.AuxiliarFuctions exposing (uniqueConcatList)
import Maybe
import Parser exposing (..)
import Tuple


type A_Expr
    = Number Int
    | Var String
    | Add A_Expr A_Expr
    | Dif A_Expr A_Expr
    | Mul A_Expr A_Expr
    | Div A_Expr A_Expr
    | Mod A_Expr A_Expr


varsInA_Expr : A_Expr -> List String
varsInA_Expr expr =
    case expr of
        Number _ ->
            []

        Var s ->
            [ s ]

        Add e1 e2 ->
            uniqueConcatList (varsInA_Expr e1) (varsInA_Expr e2)

        Dif e1 e2 ->
            uniqueConcatList (varsInA_Expr e1) (varsInA_Expr e2)

        Mul e1 e2 ->
            uniqueConcatList (varsInA_Expr e1) (varsInA_Expr e2)

        Div e1 e2 ->
            uniqueConcatList (varsInA_Expr e1) (varsInA_Expr e2)

        Mod e1 e2 ->
            uniqueConcatList (varsInA_Expr e1) (varsInA_Expr e2)


evaluateAExpr : A_Expr -> Dict String Int -> Maybe Int
evaluateAExpr expr vals =
    case expr of
        Number i ->
            Just i

        Var s ->
            Dict.get s vals

        Add e1 e2 ->
            Maybe.map2 (+) (evaluateAExpr e1 vals) (evaluateAExpr e2 vals)

        Dif e1 e2 ->
            Maybe.map2 (-) (evaluateAExpr e1 vals) (evaluateAExpr e2 vals)

        Mul e1 e2 ->
            Maybe.map2 (*) (evaluateAExpr e1 vals) (evaluateAExpr e2 vals)

        Div e1 e2 ->
            Maybe.map2 (//) (evaluateAExpr e1 vals) (evaluateAExpr e2 vals)

        Mod e1 e2 ->
            Maybe.map2 modBy (evaluateAExpr e2 vals) (evaluateAExpr e1 vals)


parseAExpr : String -> ( Maybe A_Expr, String )
parseAExpr str =
    if str == "" then
        ( Nothing, "Empty expression" )

    else
        case run expressionA str of
            Ok y ->
                ( Just y, "" )

            Err y ->
                ( Nothing, Debug.toString y )


numberParser : Parser Int
numberParser =
    oneOf
        [ succeed negate
            |. symbol "-"
            |= int
        , int
        ]


varAExpr : Parser String
varAExpr =
    Parser.succeed ()
        |. Parser.chompIf Char.isLower
        |. Parser.chompWhile Char.isLower
        |. Parser.chompWhile Char.isDigit
        |> Parser.getChompedString


termAExpr : Parser A_Expr
termAExpr =
    oneOf
        [ succeed Number
            |= numberParser
        , succeed Var
            |= varAExpr
        , succeed identity
            |. symbol "("
            |= lazy (\_ -> expressionA)
            |. symbol ")"
        ]


expressionA : Parser A_Expr
expressionA =
    termAExpr |> andThen (expressionAAux [])


type A_Operator
    = AddOp
    | DifOp
    | MulOp
    | DivOp
    | ModOp


operatorA : Parser A_Operator
operatorA =
    oneOf
        [ Parser.map (\_ -> AddOp) (symbol "+")
        , Parser.map (\_ -> DifOp) (symbol "-")
        , Parser.map (\_ -> MulOp) (symbol "*")
        , Parser.map (\_ -> DivOp) (symbol "/")
        , Parser.map (\_ -> ModOp) (symbol "%")
        ]


expressionAAux : List ( A_Expr, A_Operator ) -> A_Expr -> Parser A_Expr
expressionAAux revOps aExpr =
    oneOf
        [ succeed Tuple.pair
            |= operatorA
            |= termAExpr
            |> andThen (\( op, newExpr ) -> expressionAAux (( aExpr, op ) :: revOps) newExpr)
        , lazy (\_ -> succeed (finalize revOps aExpr))
        ]


finalize : List ( A_Expr, A_Operator ) -> A_Expr -> A_Expr
finalize revOps finalExpr =
    case revOps of
        [] ->
            finalExpr

        -- Module operation have the maximum priorty, so module have a unique case
        ( expr, ModOp ) :: otherRevOps ->
            finalize otherRevOps (Mod expr finalExpr)

        -- Division have the second maximum priority, so we need to determine how parser's going to do if it searches a module after and if it searches something different
        ( expr, DivOp ) :: ( expr2, ModOp ) :: otherRevOps ->
            Div (finalize (( expr2, ModOp ) :: otherRevOps) expr) finalExpr

        ( expr, DivOp ) :: otherRevOps ->
            finalize otherRevOps (Div expr finalExpr)

        -- Multiply cases
        ( expr, MulOp ) :: ( expr2, ModOp ) :: otherRevOps ->
            Mul (finalize (( expr2, ModOp ) :: otherRevOps) expr) finalExpr

        ( expr, MulOp ) :: ( expr2, DivOp ) :: otherRevOps ->
            Mul (finalize (( expr2, DivOp ) :: otherRevOps) expr) finalExpr

        ( expr, MulOp ) :: otherRevOps ->
            finalize otherRevOps (Mul expr finalExpr)

        -- Differece cases
        ( expr, DifOp ) :: ( expr2, ModOp ) :: otherRevOps ->
            Dif (finalize (( expr2, ModOp ) :: otherRevOps) expr) finalExpr

        ( expr, DifOp ) :: ( expr2, DivOp ) :: otherRevOps ->
            Dif (finalize (( expr2, DivOp ) :: otherRevOps) expr) finalExpr

        ( expr, DifOp ) :: ( expr2, MulOp ) :: otherRevOps ->
            Dif (finalize (( expr2, MulOp ) :: otherRevOps) expr) finalExpr

        ( expr, DifOp ) :: otherRevOps ->
            finalize otherRevOps (Dif expr finalExpr)

        -- Add cases
        ( expr, AddOp ) :: ( expr2, ModOp ) :: otherRevOps ->
            Add (finalize (( expr2, ModOp ) :: otherRevOps) expr) finalExpr

        ( expr, AddOp ) :: ( expr2, DivOp ) :: otherRevOps ->
            Add (finalize (( expr2, DivOp ) :: otherRevOps) expr) finalExpr

        ( expr, AddOp ) :: ( expr2, MulOp ) :: otherRevOps ->
            Add (finalize (( expr2, MulOp ) :: otherRevOps) expr) finalExpr

        ( expr, AddOp ) :: ( expr2, DifOp ) :: otherRevOps ->
            Add (finalize (( expr2, DifOp ) :: otherRevOps) expr) finalExpr

        ( expr, AddOp ) :: otherRevOps ->
            finalize otherRevOps (Add expr finalExpr)


toStringAExpr : A_Expr -> String
toStringAExpr aExpr =
    case aExpr of
        Number p ->
            String.fromInt p

        Var p ->
            p

        Add p q ->
            "(" ++ toStringAExpr p ++ "+" ++ toStringAExpr q ++ ")"

        Dif p q ->
            "(" ++ toStringAExpr p ++ "-" ++ toStringAExpr q ++ ")"

        Mul p q ->
            "(" ++ toStringAExpr p ++ "*" ++ toStringAExpr q ++ ")"

        Div p q ->
            "(" ++ toStringAExpr p ++ "//" ++ toStringAExpr q ++ ")"

        Mod p q ->
            "(" ++ toStringAExpr p ++ "%" ++ toStringAExpr q ++ ")"


toMathStringAExpr : A_Expr -> String
toMathStringAExpr aExpr =
    case aExpr of
        Number p ->
            String.fromInt p

        Var p ->
            p

        Add p q ->
            "(" ++ toMathStringAExpr p ++ "+" ++ toMathStringAExpr q ++ ")"

        Dif p q ->
            "(" ++ toMathStringAExpr p ++ "-" ++ toMathStringAExpr q ++ ")"

        Mul p q ->
            "(" ++ toMathStringAExpr p ++ "\\cdot " ++ toMathStringAExpr q ++ ")"

        Div p q ->
            "(" ++ toMathStringAExpr p ++ "//" ++ toMathStringAExpr q ++ ")"

        Mod p q ->
            "(" ++ toMathStringAExpr p ++ "\\% " ++ toMathStringAExpr q ++ ")"
