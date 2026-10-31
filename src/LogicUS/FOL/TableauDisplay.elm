module LogicUS.FOL.TableauDisplay exposing
    ( DTree(..), closedMark, openMark, undecidedMark, unexploredMark
    , numbered, rule, substitution
    , toText, toDOT
    )

{- The way the three semantic tableaux (SemanticTableaux, SemanticTableauxEQ, SemanticTableauxFV) show their trees,
so that they look the same.

  - Each formula node shows its number, which is its depth in the branch (1, 2, ...), and its formula: `5. ¬P(a)`.
    The two components of a β rule have the same number.
  - The edge to a node shows the rule that produced it and the numbers of its premises: `α(4)`, `β(4)`,
    `γ(1){x/a}`, `δ(3){x/c₁}`, `¬¬(2)`; a closed branch ends in `✕`, with the edge `⊥(3,6)`.
  - The other leaves: `◯` open branch, `ⓤ` branch stopped by the limits, `…` branch not explored.

The symbols are chosen so that common fonts have them.

-}

import Dict
import Json.Encode as JSONE
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL, Substitution)


{-| A tree ready to be shown: the label of each node and the label of the edge from its parent.
-}
type DTree
    = DTree { node : String, edge : String } (List DTree)


closedMark : String
closedMark =
    "✕"


openMark : String
openMark =
    "◯"


undecidedMark : String
undecidedMark =
    "ⓤ"


unexploredMark : String
unexploredMark =
    "…"


numbered : Int -> FormulaFOL -> String
numbered k f =
    String.fromInt k ++ ". " ++ FOL_SS.ffolToString f


{-| `rule "γ" [ "1" ] "{x/a}"` is `γ(1){x/a}`.
-}
rule : String -> List String -> String -> String
rule name premises suffix =
    name ++ "(" ++ String.join "," premises ++ ")" ++ suffix


substitution : Substitution -> String
substitution s =
    if Dict.isEmpty s then
        ""

    else
        FOL_SS.substitutionToString s



-- Text: a node per line, with its rule aligned on the right. A branch goes down at the same indentation, and the
-- branches of a β rule are indented one level more than the formula they come from.


toText : List DTree -> String
toText ts =
    let
        lines indent (DTree l ch) =
            ( String.repeat indent "    " ++ l.node, l.edge )
                :: (case ch of
                        [ c ] ->
                            lines indent c

                        _ ->
                            List.concatMap (lines (indent + 1)) ch
                   )

        ls =
            List.concatMap (lines 0) ts

        width =
            Maybe.withDefault 0 (List.maximum (List.map (String.length << Tuple.first) ls))
    in
    String.join "\n"
        (List.map
            (\( left, edge ) ->
                if edge == "" then
                    left

                else
                    String.padRight (width + 4) ' ' left ++ "% " ++ edge
            )
            ls
        )



-- DOT: `header` goes right after `digraph G {` (graph attributes, or extra nodes).


toDOT : String -> List DTree -> String
toDOT header ts =
    let
        q s =
            JSONE.encode 0 (JSONE.string s)

        go parent (DTree l ch) ( acc, n ) =
            let
                me =
                    String.fromInt n

                edge =
                    if parent == "" then
                        []

                    else if l.edge == "" then
                        [ "  " ++ parent ++ " -> " ++ me ++ ";" ]

                    else
                        [ "  " ++ parent ++ " -> " ++ me ++ " [label=" ++ q l.edge ++ "];" ]
            in
            List.foldl (go me) ( List.reverse edge ++ (("  " ++ me ++ " [label=" ++ q l.node ++ "];") :: acc), n + 1 ) ch

        ( body, _ ) =
            List.foldl (go "") ( [], 0 ) ts
    in
    String.join "\n" ([ "digraph G {" ] ++ (if header == "" then [] else [ header ]) ++ List.reverse body ++ [ "}" ])
