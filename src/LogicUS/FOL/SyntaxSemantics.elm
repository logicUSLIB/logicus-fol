module LogicUS.FOL.SyntaxSemantics exposing
    ( Ident, Variable, Term(..), FormulaFOL(..), SetFOL, ffolNegation, termVarSymbols, termsVarSymbols, ffolVarSymbols, termConstSymbols, termsConstSymbols, ffolConstSymbols, termFuncSymbols, termsFuncSymbols, ffolFuncSymbols, ffolPredSymbols, ffolContainsEquality, ffolFormTree, ffolIsWellFormed, ffolHasInstanceOfVar, ffolHasFreeInstanceOfVar, ffolHasLinkedInstanceOfVar, ffolFreeVars, ffolLinkedVars, termIsClosed, termClosedTerms, termsClosedTerms, ffolAllClosedTerms, ffolIsOpen, ffolIsClosed, sfolNegation, sfolConjunction, sfolDisjunction
    , Substitution, substitutionDomain, termApplySubstitution, ffolApplySubstitution, substitutionComposition, ffolRenameVars, ffolUniversalClosure, ffolExistentialClosure
    , L_Structure, lStructureIsValid, termInterpretation, termsInterpretation, ffolValuation, sfolInterpretation
    , ffolReadFromString, ffolReadExtraction, ffolRead, sfolRead, ffolToInputString, substitutionReadFromString, substitutionReadExtraction, substitutionToInputString
    , varToString, varsToString, varToMathString, varsToMathString, identToString, identsToString, identToMathString, identsToMathString, termToString, termsToString, termToMathString, termsToMathString, ffolToString, sfolToString, ffolToMathString, sfolToMathString, sfolToMathString2, formTreeToString, formTreeToDOT, substitutionToString, substitutionToMathString, l_StructureToString
    )

{-| The module provides the elementary tools for working with first order logic. It allows defining both formulas and sets as well as performing some basic operations on them, such as evaluations regarding interpretations, performs substitutions, closures, ...


# FOL Formulas and Sets

@docs Ident, Variable, Term, FormulaFOL, SetFOL, ffolNegation, termVarSymbols, termsVarSymbols, ffolVarSymbols, termConstSymbols, termsConstSymbols, ffolConstSymbols, termFuncSymbols, termsFuncSymbols, ffolFuncSymbols, ffolPredSymbols, ffolContainsEquality, ffolFormTree, ffolIsWellFormed, ffolHasInstanceOfVar, ffolHasFreeInstanceOfVar, ffolHasLinkedInstanceOfVar, ffolFreeVars, ffolLinkedVars, termIsClosed, termClosedTerms, termsClosedTerms, ffolAllClosedTerms, ffolIsOpen, ffolIsClosed, sfolNegation, sfolConjunction, sfolDisjunction


# Substitutions, variable rename and closure

@docs Substitution, substitutionDomain, termApplySubstitution, ffolApplySubstitution, substitutionComposition, ffolRenameVars, ffolUniversalClosure, ffolExistentialClosure


# L-structures and valuations

@docs L_Structure, lStructureIsValid, termInterpretation, termsInterpretation, ffolValuation, sfolInterpretation


# Parsers

@docs ffolReadFromString, ffolReadExtraction, ffolRead, sfolRead, ffolToInputString, substitutionReadFromString, substitutionReadExtraction, substitutionToInputString


# Representation

@docs varToString, varsToString, varToMathString, varsToMathString, identToString, identsToString, identToMathString, identsToMathString, termToString, termsToString, termToMathString, termsToMathString, ffolToString, sfolToString, ffolToMathString, sfolToMathString, sfolToMathString2, formTreeToString, formTreeToDOT, substitutionToString, substitutionToMathString, l_StructureToString

-}

--===========--
--  IMPORTS  --
--===========--

import Dict exposing (Dict)
import Graph exposing (Edge, Graph, Node, NodeId)
import Graph.DOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.FOL.AuxiliarFuctions exposing (replaceBySubscript, replaceBySuperscript, uniqueConcatList)
import Maybe.Extra as ME
import Parser exposing ((|.), (|=), Parser, Trailing(..), succeed)
import Set exposing (Set)
import Tuple exposing (first)
import Tuple exposing (second)



-----------
-- TYPES --
-----------


{-| It represent an ident as a string and a list of subindices as integers
-}
type alias Ident =
    ( String, List Int )


{-| It represent a variable as a string, a list of subindices as integers, and a superindex that must be a positive int.
-}
type alias Variable =
    ( String, List Int, Int )


{-| It is used to represent the terms in First Order Logic , these are variables, constants and functions. Note that constants are a particular case of functions, which are not dependent on any variable.
-}
type Term
    = Var Variable
    | Func Ident (List Term)


{-| It is a recursive definition of a formula in First Order Logic. It could be a predicate, equality, universal quantification, existential quantificacation, negation, conjuction, implication, equivalence and unsatisfiable formula
-}
type FormulaFOL
    = Pred Ident (List Term)
    | Equal Term Term
    | Neg FormulaFOL
    | Conj FormulaFOL FormulaFOL
    | Disj FormulaFOL FormulaFOL
    | Impl FormulaFOL FormulaFOL
    | Equi FormulaFOL FormulaFOL
    | Exists Variable FormulaFOL
    | Forall Variable FormulaFOL
    | Insat
    | Taut


{-| It is used to define sets of formulas in First Order Logic.
-}
type alias SetFOL =
    List FormulaFOL



--===============--
--  FUNCTIONS    --
--===============--
----------------------
-- Regular functions -
----------------------


{-| It gives the negation of a formula applying idempotent rule or the insat/taut negation when corresponds.
-}
ffolNegation : FormulaFOL -> FormulaFOL
ffolNegation f =
    case f of
        Neg g ->
            g

        Taut ->
            Insat

        Insat ->
            Taut

        _ ->
            Neg f


{-| It gets all the variable symbols that acts inside a term

    termVarSymbols (Func "f" [ Var "a", Func "c" [], Func "g" [ Var "b", Var "a" ] ]) =
        [ "a", "b" ]

-}
termVarSymbols : Term -> List Variable
termVarSymbols t =
    case t of
        Var x ->
            [ x ]

        Func _ ts ->
            List.sort <| LE.unique <| List.concat <| List.map termVarSymbols ts


{-| It gets all the variables that acts inside a list of terms

    termsVarSymbols [ Func "f" [ Var "a", Func "c" [] ], Func "g" [ Var "b", Var "c" ] ] =
        [ "a", "b", "c" ]

-}
termsVarSymbols : List Term -> List Variable
termsVarSymbols ts =
    List.sort <| LE.unique <| List.concat <| List.map termVarSymbols ts


{-| It gets all the variables that acts inside a formula

    f1 =
        ffolReadExtraction <| ffolReadFromString "_p(x,y)=_p(y,x)"

    f2 =
        ffolReadExtraction <| ffolReadFromString "!A[x] !A[y] (M(x,y) -> !E[z] F(z, _jhon) & P(x,z) | P(y,z))"

    ffolVarSymbols f1 =
        [ "x", "y" ]
    ffolVarSymbols f2 =
        [ "x", "y", "z" ]

-}
ffolVarSymbols : FormulaFOL -> List Variable
ffolVarSymbols f =
    case f of
        Pred _ ts ->
            termsVarSymbols ts

        Equal t1 t2 ->
            termsVarSymbols [ t1, t2 ]

        Neg p ->
            ffolVarSymbols p

        Conj p q ->
            List.sort <| LE.unique <| ffolVarSymbols p ++ ffolVarSymbols q

        Disj p q ->
            List.sort <| LE.unique <| ffolVarSymbols p ++ ffolVarSymbols q

        Impl p q ->
            List.sort <| LE.unique <| ffolVarSymbols p ++ ffolVarSymbols q

        Equi p q ->
            List.sort <| LE.unique <| ffolVarSymbols p ++ ffolVarSymbols q

        Exists x p ->
            List.sort <| LE.unique <| ffolVarSymbols p ++ [ x ]

        Forall x p ->
            List.sort <| LE.unique <| ffolVarSymbols p ++ [ x ]

        _ ->
            []


{-| It gets all the constant symbols that acts inside a term
-}
termConstSymbols : Term -> List Ident
termConstSymbols t =
    case t of
        Var _ ->
            []

        Func c [] ->
            [ c ]

        Func _ ts ->
            List.sort <| LE.unique <| List.concat <| List.map termConstSymbols ts


{-| It gets all the constants symbols that acts inside a list of terms
-}
termsConstSymbols : List Term -> List Ident
termsConstSymbols ts =
    List.sort <| LE.unique <| List.concat <| List.map termConstSymbols ts


{-| It gets all the constant symbols that acts inside a formula
-}
ffolConstSymbols : FormulaFOL -> List Ident
ffolConstSymbols f =
    case f of
        Pred _ ts ->
            termsConstSymbols ts

        Equal t1 t2 ->
            termsConstSymbols [ t1, t2 ]

        Neg p ->
            ffolConstSymbols p

        Conj p q ->
            List.sort <| LE.unique <| ffolConstSymbols p ++ ffolConstSymbols q

        Disj p q ->
            List.sort <| LE.unique <| ffolConstSymbols p ++ ffolConstSymbols q

        Impl p q ->
            List.sort <| LE.unique <| ffolConstSymbols p ++ ffolConstSymbols q

        Equi p q ->
            List.sort <| LE.unique <| ffolConstSymbols p ++ ffolConstSymbols q

        Exists _ p ->
            List.sort <| LE.unique <| ffolConstSymbols p

        Forall _ p ->
            List.sort <| LE.unique <| ffolConstSymbols p

        _ ->
            []


{-| It gets all the function symbols that acts inside a term
-}
termFuncSymbols : Term -> List Ident
termFuncSymbols t =
    case t of
        Var _ ->
            []

        Func _ [] ->
            []

        Func f_ ts ->
            List.sort <| LE.unique <| f_ :: (List.concat <| List.map termFuncSymbols ts)


{-| It gets all the function symbols that acts inside a list of terms
-}
termsFuncSymbols : List Term -> List Ident
termsFuncSymbols ts =
    List.sort <| LE.unique <| List.concat <| List.map termFuncSymbols ts


{-| It gets all the function symbols that acts inside a formula
-}
ffolFuncSymbols : FormulaFOL -> List Ident
ffolFuncSymbols f =
    case f of
        Pred _ ts ->
            termsFuncSymbols ts

        Equal t1 t2 ->
            termsFuncSymbols [ t1, t2 ]

        Neg p ->
            ffolFuncSymbols p

        Conj p q ->
            List.sort <| LE.unique <| ffolFuncSymbols p ++ ffolFuncSymbols q

        Disj p q ->
            List.sort <| LE.unique <| ffolFuncSymbols p ++ ffolFuncSymbols q

        Impl p q ->
            List.sort <| LE.unique <| ffolFuncSymbols p ++ ffolFuncSymbols q

        Equi p q ->
            List.sort <| LE.unique <| ffolFuncSymbols p ++ ffolFuncSymbols q

        Exists _ p ->
            List.sort <| LE.unique <| ffolFuncSymbols p

        Forall _ p ->
            List.sort <| LE.unique <| ffolFuncSymbols p

        _ ->
            []


{-| It gets all the predicate symbols that acts inside a formula
-}
ffolPredSymbols : FormulaFOL -> List Ident
ffolPredSymbols f =
    case f of
        Pred p _ ->
            [ p ]

        Equal _ _ ->
            [ ( "=", [] ) ]

        Neg p ->
            ffolPredSymbols p

        Conj p q ->
            List.sort <| LE.unique <| ffolPredSymbols p ++ ffolPredSymbols q

        Disj p q ->
            List.sort <| LE.unique <| ffolPredSymbols p ++ ffolPredSymbols q

        Impl p q ->
            List.sort <| LE.unique <| ffolPredSymbols p ++ ffolPredSymbols q

        Equi p q ->
            List.sort <| LE.unique <| ffolPredSymbols p ++ ffolPredSymbols q

        Exists _ p ->
            List.sort <| LE.unique <| ffolPredSymbols p

        Forall _ p ->
            List.sort <| LE.unique <| ffolPredSymbols p

        _ ->
            []


{-| It gets if a formual contains equal predicate or not
-}
ffolContainsEquality : FormulaFOL -> Bool
ffolContainsEquality f =
    case f of
        Pred _ _ ->
            False

        Equal _ _ ->
            True

        Neg p ->
            ffolContainsEquality p

        Conj p q ->
            ffolContainsEquality p || ffolContainsEquality q

        Disj p q ->
            ffolContainsEquality p || ffolContainsEquality q

        Impl p q ->
            ffolContainsEquality p || ffolContainsEquality q

        Equi p q ->
            ffolContainsEquality p || ffolContainsEquality q

        Exists _ p ->
            ffolContainsEquality p

        Forall _ p ->
            ffolContainsEquality p

        _ ->
            False


{-| It gives a graph with the form tree of a formula. If you want visualize it you can use formTreeToDOT and visualize the result witn an online graphviz render. Don't forget change `\\n` by `\n` and `\\"` by `"` in a code editor previously.

    ffolFormTree f2 |> formTreeToDOT =
        "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=plaintext, color=black]\n  edge [dir=none]\n\n  0 -> 1\n  1 -> 2\n  2 -> 3\n  2 -> 9\n  3 -> 4\n  3 -> 5\n  5 -> 6\n  5 -> 8\n  6 -> 7\n\n  0 [label=\"∀x ∀y ( ( M(x, y) → ( ∃z F(z, jhon) ∧ P(x, z) ) ) ∨ P(y, z) )\"]\n  1 [label=\"∀y ( ( M(x, y) → ( ∃z F(z, jhon) ∧ P(x, z) ) ) ∨ P(y, z) )\"]\n  2 [label=\"( ( M(x, y) → ( ∃z F(z, jhon) ∧ P(x, z) ) ) ∨ P(y, z) )\"]\n  3 [label=\"( M(x, y) → ( ∃z F(z, jhon) ∧ P(x, z) ) )\"]\n  4 [label=\"M(x, y)\"]\n  5 [label=\"( ∃z F(z, jhon) ∧ P(x, z) )\"]\n  6 [label=\"∃z F(z, jhon)\"]\n  7 [label=\"F(z, jhon)\"]\n  8 [label=\"P(x, z)\"]\n  9 [label=\"P(y, z)\"]\n}"

-}
ffolFormTree : FormulaFOL -> Graph FormulaFOL ()
ffolFormTree x =
    case x of
        Neg p ->
            let
                ( nodes, edges ) =
                    formTreeAux p 1
            in
            Graph.fromNodesAndEdges (Node 0 x :: nodes) (Edge 0 1 () :: edges)

        Conj p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Node 0 x :: (nodes1 ++ nodes2)) ([ Edge 0 1 (), Edge 0 nextid () ] ++ edges1 ++ edges2)

        Disj p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Node 0 x :: (nodes1 ++ nodes2)) ([ Edge 0 1 (), Edge 0 nextid () ] ++ edges1 ++ edges2)

        Impl p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Node 0 x :: (nodes1 ++ nodes2)) ([ Edge 0 1 (), Edge 0 nextid () ] ++ edges1 ++ edges2)

        Equi p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Node 0 x :: (nodes1 ++ nodes2)) ([ Edge 0 1 (), Edge 0 nextid () ] ++ edges1 ++ edges2)

        Exists _ p ->
            let
                ( nodes, edges ) =
                    formTreeAux p 1
            in
            Graph.fromNodesAndEdges (Node 0 x :: nodes) (Edge 0 1 () :: edges)

        Forall _ p ->
            let
                ( nodes, edges ) =
                    formTreeAux p 1
            in
            Graph.fromNodesAndEdges (Node 0 x :: nodes) (Edge 0 1 () :: edges)

        _ ->
            Graph.fromNodesAndEdges [ Node 0 x ] []


formTreeAux : FormulaFOL -> NodeId -> ( List (Node FormulaFOL), List (Edge ()) )
formTreeAux x nodeid =
    case x of
        Neg p ->
            let
                ( nodes, edges ) =
                    formTreeAux p (nodeid + 1)
            in
            ( Node nodeid x :: nodes, Edge nodeid (nodeid + 1) () :: edges )

        Conj p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            ( Node nodeid x :: (nodes1 ++ nodes2), [ Edge nodeid (nodeid + 1) (), Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Disj p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            ( Node nodeid x :: (nodes1 ++ nodes2), [ Edge nodeid (nodeid + 1) (), Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Impl p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            ( Node nodeid x :: (nodes1 ++ nodes2), [ Edge nodeid (nodeid + 1) (), Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Equi p q ->
            let
                ( nodes1, edges1 ) =
                    formTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    formTreeAux q nextid
            in
            ( Node nodeid x :: (nodes1 ++ nodes2), [ Edge nodeid (nodeid + 1) (), Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Exists _ p ->
            let
                ( nodes, edges ) =
                    formTreeAux p (nodeid + 1)
            in
            ( Node nodeid x :: nodes, Edge nodeid (nodeid + 1) () :: edges )

        Forall _ p ->
            let
                ( nodes, edges ) =
                    formTreeAux p (nodeid + 1)
            in
            ( Node nodeid x :: nodes, Edge nodeid (nodeid + 1) () :: edges )

        _ ->
            ( [ Node nodeid x ], [] )


{-| It indicates if a formula is well formed or not. A formula is well formed if it doesn't contain two nested quantifiers over the same variable

    f3 = ffolReadExtraction <| ffolReadFromString "!A[x] !A[y] (M(x,y) -> !E[x] F(x, _jhon) & P(x,x) | P(y,x))"

    ffolIsWellFormed f1 == True
    ffolIsWellFormed f2 == True
    ffolIsWellFormed f3 == False

-}
ffolIsWellFormed : FormulaFOL -> Bool
ffolIsWellFormed f =
    let
        aux g ls =
            case g of
                Pred _ _ ->
                    True

                Equal _ _ ->
                    True

                Neg p ->
                    aux p ls

                Conj p q ->
                    aux p ls && aux q ls

                Disj p q ->
                    aux p ls && aux q ls

                Impl p q ->
                    aux p ls && aux q ls

                Equi p q ->
                    aux p ls && aux q ls

                Exists x p ->
                    not (List.member x ls) && aux p (ls ++ [ x ])

                Forall x p ->
                    not (List.member x ls) && aux p (ls ++ [ x ])

                Insat ->
                    True

                Taut ->
                    True
    in
    aux f []


{-| It gives if a formula contains an instance of the variable given.
-}
ffolHasInstanceOfVar : FormulaFOL -> Variable -> Bool
ffolHasInstanceOfVar f v =
    case f of
        Pred _ ts ->
            List.member v (termsVarSymbols ts)

        Equal t1 t2 ->
            List.member v (termsVarSymbols [ t1, t2 ])

        Neg g ->
            ffolHasInstanceOfVar g v

        Conj g h ->
            ffolHasInstanceOfVar g v || ffolHasInstanceOfVar h v

        Disj g h ->
            ffolHasInstanceOfVar g v || ffolHasInstanceOfVar h v

        Impl g h ->
            ffolHasInstanceOfVar g v || ffolHasInstanceOfVar h v

        Equi g h ->
            ffolHasInstanceOfVar g v || ffolHasInstanceOfVar h v

        Exists _ g ->
            ffolHasInstanceOfVar g v

        Forall _ g ->
            ffolHasInstanceOfVar g v

        _ ->
            False


{-| It checks if in one formula if it exists any free instance of a given variable
-}
ffolHasFreeInstanceOfVar : FormulaFOL -> Variable -> Bool
ffolHasFreeInstanceOfVar f v =
    case f of
        Pred _ ts ->
            List.member v (termsVarSymbols ts)

        Equal t1 t2 ->
            List.member v (termsVarSymbols [ t1, t2 ])

        Neg g ->
            ffolHasFreeInstanceOfVar g v

        Conj g h ->
            ffolHasFreeInstanceOfVar g v || ffolHasFreeInstanceOfVar h v

        Disj g h ->
            ffolHasFreeInstanceOfVar g v || ffolHasFreeInstanceOfVar h v

        Impl g h ->
            ffolHasFreeInstanceOfVar g v || ffolHasFreeInstanceOfVar h v

        Equi g h ->
            ffolHasFreeInstanceOfVar g v || ffolHasFreeInstanceOfVar h v

        Exists x g ->
            not (x == v) && ffolHasFreeInstanceOfVar g v

        Forall x g ->
            not (x == v) && ffolHasFreeInstanceOfVar g v

        _ ->
            False


{-| It checks if in one formula if it exists any linked instance of a given variable
-}
ffolHasLinkedInstanceOfVar : FormulaFOL -> Variable -> Bool
ffolHasLinkedInstanceOfVar f v =
    case f of
        Pred _ _ ->
            False

        Equal _ _ ->
            False

        Neg g ->
            ffolHasLinkedInstanceOfVar g v

        Conj g h ->
            ffolHasLinkedInstanceOfVar g v || ffolHasLinkedInstanceOfVar h v

        Disj g h ->
            ffolHasLinkedInstanceOfVar g v || ffolHasLinkedInstanceOfVar h v

        Impl g h ->
            ffolHasLinkedInstanceOfVar g v || ffolHasLinkedInstanceOfVar h v

        Equi g h ->
            ffolHasLinkedInstanceOfVar g v || ffolHasLinkedInstanceOfVar h v

        Exists x g ->
            (x == v) && ffolHasInstanceOfVar g v || ffolHasLinkedInstanceOfVar g v

        Forall x g ->
            (x == v) && ffolHasInstanceOfVar g v || ffolHasLinkedInstanceOfVar g v

        _ ->
            False


{-| It gives the variables of the formulas that are free. That is, variables that have a free instance in the formula
-}
ffolFreeVars : FormulaFOL -> List Variable
ffolFreeVars f =
    List.filter (\v -> ffolHasFreeInstanceOfVar f v) <| ffolVarSymbols f


{-| It gives the variables of the formulas that are linked. That is, variables that have a linked instance in the formula
-}
ffolLinkedVars : FormulaFOL -> List Variable
ffolLinkedVars f =
    List.filter (\v -> ffolHasLinkedInstanceOfVar f v) <| ffolVarSymbols f


{-| It determinates if a term is closed this is if it doesn't contains any variable
-}
termIsClosed : Term -> Bool
termIsClosed t =
    (List.isEmpty << termVarSymbols) t


{-| It gives the all the closed terms inside a term (including the entire term if it is closed)
-}
termClosedTerms : Term -> List Term
termClosedTerms t =
    case t of
        Var _ ->
            []

        Func _ [] ->
            [ t ]

        Func _ ts ->
            uniqueConcatList [] <|
                (List.concat <| List.map termClosedTerms ts)
                    ++ (if termIsClosed t then
                            [ t ]

                        else
                            []
                       )


{-| It gives all the closed terms inside a list of terms.
-}
termsClosedTerms : List Term -> List Term
termsClosedTerms ts =
    LE.unique <| List.concat <| List.map termClosedTerms ts


{-| It gives the all the closed terms inside a formula
-}
ffolAllClosedTerms : FormulaFOL -> List Term
ffolAllClosedTerms f =
    case f of
        Pred _ ts ->
            uniqueConcatList [] <| (List.concat <| List.map termClosedTerms ts)

        Equal t1 t2 ->
            uniqueConcatList [] <| (List.concat <| List.map termClosedTerms [ t1, t2 ])

        Neg g ->
            ffolAllClosedTerms g

        Conj g h ->
            uniqueConcatList (ffolAllClosedTerms g) (ffolAllClosedTerms h)

        Disj g h ->
            uniqueConcatList (ffolAllClosedTerms g) (ffolAllClosedTerms h)

        Impl g h ->
            uniqueConcatList (ffolAllClosedTerms g) (ffolAllClosedTerms h)

        Equi g h ->
            uniqueConcatList (ffolAllClosedTerms g) (ffolAllClosedTerms h)

        Exists _ g ->
            ffolAllClosedTerms g

        Forall _ g ->
            ffolAllClosedTerms g

        Taut ->
            []

        Insat ->
            []


{-| It determinates if a formula is opened this is if it doesn't contains any quantifier
-}
ffolIsOpen : FormulaFOL -> Bool
ffolIsOpen f =
    case f of
        Neg g ->
            ffolIsOpen g

        Conj g h ->
            ffolIsOpen g && ffolIsOpen h

        Disj g h ->
            ffolIsOpen g && ffolIsOpen h

        Impl g h ->
            ffolIsOpen g && ffolIsOpen h

        Equi g h ->
            ffolIsOpen g && ffolIsOpen h

        Exists _ _ ->
            False

        Forall _ _ ->
            False

        _ ->
            True


{-| It checks if s formula is closed this is if it hasn't any free variables
-}
ffolIsClosed : FormulaFOL -> Bool
ffolIsClosed f =
    not <| List.any (\x -> ffolHasFreeInstanceOfVar f x) (ffolVarSymbols f)



-------------------
-- SUBSTITUTIONS --
-------------------


{-| It defines a substitution in First Order Logic
-}
type alias Substitution =
    Dict Variable Term


{-| It gets the variable domain of the substitution, that is variables symbols that participates in it.
-}
substitutionDomain : Substitution -> List Variable
substitutionDomain s =
    Dict.keys s


{-| It performes a substitution in a term, replacing the variables according to the substitution.
-}
termApplySubstitution : Substitution -> Term -> Term
termApplySubstitution s t =
    case t of
        Var x ->
            Maybe.withDefault (Var x) <| Dict.get x s

        Func f_ ts ->
            Func f_ <| List.map (termApplySubstitution s) ts


{-| It performes a substitution in a formula, replacing the variables according to the substitution.
-}
ffolApplySubstitution : Substitution -> FormulaFOL -> FormulaFOL
ffolApplySubstitution s f =
    case f of
        Pred p_ ts ->
            Pred p_ <| List.map (termApplySubstitution s) ts

        Equal t1 t2 ->
            Equal (termApplySubstitution s t1) (termApplySubstitution s t2)

        Neg g ->
            Neg (ffolApplySubstitution s g)

        Conj g h ->
            Conj (ffolApplySubstitution s g) (ffolApplySubstitution s h)

        Disj g h ->
            Disj (ffolApplySubstitution s g) (ffolApplySubstitution s h)

        Impl g h ->
            Impl (ffolApplySubstitution s g) (ffolApplySubstitution s h)

        Equi g h ->
            Equi (ffolApplySubstitution s g) (ffolApplySubstitution s h)

        Exists x g ->
            Exists x <| ffolApplySubstitution (Dict.filter (\k v -> k /= x && (not <| List.member x <| termVarSymbols v)) s) g

        Forall x g ->
            Forall x <| ffolApplySubstitution (Dict.filter (\k v -> k /= x && (not <| List.member x <| termVarSymbols v)) s) g

        Taut ->
            Taut

        Insat ->
            Insat


{-| It gives the composition of two substitutions (s1 ∘ s2)
-}
substitutionComposition : Substitution -> Substitution -> Substitution
substitutionComposition s1 s2 =
    Dict.fromList <|
        List.filter (\( x, t ) -> Var x /= t) <|
            List.map (\( x2, t2 ) -> ( x2, termApplySubstitution s1 t2 )) (Dict.toList s2)
                ++ List.filter (\( x1, _ ) -> not (Dict.member x1 s2)) (Dict.toList s1)


{-| It renames variables in a formula if it is necessary. If a instance is linked to several quantifiers (non well formed formula) it takes the nearest one as reference.
-}
ffolRenameVars : FormulaFOL -> FormulaFOL
ffolRenameVars f =
    let
        aux g cur hist =
            case g of
                Pred n ts ->
                    let
                        s =
                            Dict.map (\( vname, vindices, _ ) v -> Var ( vname, vindices, v )) cur
                    in
                    ( Pred n <| List.map (\t -> termApplySubstitution s t) ts, hist )

                Equal t1 t2 ->
                    let
                        s =
                            Dict.map (\( vname, vindices, _ ) v -> Var ( vname, vindices, v )) cur
                    in
                    ( Equal (termApplySubstitution s t1) (termApplySubstitution s t2), hist )

                Neg h ->
                    let
                        ( nh, nhist ) =
                            aux h cur hist
                    in
                    ( Neg nh, nhist )

                Conj h i ->
                    let
                        ( nh, nhist1 ) =
                            aux h cur hist
                    in
                    let
                        ( ni, nhist2 ) =
                            aux i cur nhist1
                    in
                    ( Conj nh ni, nhist2 )

                Disj h i ->
                    let
                        ( nh, nhist1 ) =
                            aux h cur hist
                    in
                    let
                        ( ni, nhist2 ) =
                            aux i cur nhist1
                    in
                    ( Disj nh ni, nhist2 )

                Impl h i ->
                    let
                        ( nh, nhist1 ) =
                            aux h cur hist
                    in
                    let
                        ( ni, nhist2 ) =
                            aux i cur nhist1
                    in
                    ( Impl nh ni, nhist2 )

                Equi h i ->
                    let
                        ( nh, nhist1 ) =
                            aux h cur hist
                    in
                    let
                        ( ni, nhist2 ) =
                            aux i cur nhist1
                    in
                    ( Equi nh ni, nhist2 )

                Forall ( xn, xsbi, xspi ) h ->
                    let
                        xind =
                            (Maybe.withDefault 0 <| Dict.get ( xn, xsbi ) hist) + 1
                    in
                    let
                        ncur =
                            Dict.insert ( xn, xsbi, xspi ) xind cur

                        nhist1 =
                            Dict.insert ( xn, xsbi ) xind hist
                    in
                    let
                        ( nh, nhist2 ) =
                            aux h ncur nhist1
                    in
                    ( Forall ( xn, xsbi, xind ) nh, nhist2 )

                Exists ( xn, xsbi, xspi ) h ->
                    let
                        xind =
                            (Maybe.withDefault 0 <| Dict.get ( xn, xsbi ) hist) + 1
                    in
                    let
                        ncur =
                            Dict.insert ( xn, xsbi, xspi ) xind cur

                        nhist1 =
                            Dict.insert ( xn, xsbi ) xind hist
                    in
                    let
                        ( nh, nhist2 ) =
                            aux h ncur nhist1
                    in
                    ( Exists ( xn, xsbi, xind ) nh, nhist2 )

                Taut ->
                    ( Taut, hist )

                Insat ->
                    ( Insat, hist )
    in
    let
        renamed =
            Tuple.first <| aux f Dict.empty Dict.empty
    in
    let
        renamedVars =
            ffolVarSymbols renamed
    in
    let
        uniqueVars =
            Dict.fromList <| List.map (\( x, i, z ) -> ( ( x, i, z ), Var ( x, i, 0 ) )) <| List.filter (\( x, i, s ) -> List.all (\( y, i2, s2 ) -> (y /= x) || (i /= i2) || (s == s2)) renamedVars) <| renamedVars
    in
    ffolSubstitutionQuantifiedVars uniqueVars renamed


ffolSubstitutionQuantifiedVars : Substitution -> FormulaFOL -> FormulaFOL
ffolSubstitutionQuantifiedVars subs g =
    case g of
        Pred _ _ ->
            ffolApplySubstitution subs g

        Equal _ _ ->
            ffolApplySubstitution subs g

        Neg h ->
            Neg (ffolSubstitutionQuantifiedVars subs h)

        Conj h i ->
            Conj
                (ffolSubstitutionQuantifiedVars subs h)
                (ffolSubstitutionQuantifiedVars subs i)

        Disj h i ->
            Disj
                (ffolSubstitutionQuantifiedVars subs h)
                (ffolSubstitutionQuantifiedVars subs i)

        Impl h i ->
            Impl
                (ffolSubstitutionQuantifiedVars subs h)
                (ffolSubstitutionQuantifiedVars subs i)

        Equi h i ->
            Equi
                (ffolSubstitutionQuantifiedVars subs h)
                (ffolSubstitutionQuantifiedVars subs i)

        Forall ( xn, xsbi, xspi ) h ->
            case Dict.get ( xn, xsbi, xspi ) subs of
                Just (Var v) ->
                    Forall v (ffolSubstitutionQuantifiedVars subs h)

                _ ->
                    Forall ( xn, xsbi, xspi ) (ffolSubstitutionQuantifiedVars subs h)

        Exists ( xn, xsbi, xspi ) h ->
            case Dict.get ( xn, xsbi, xspi ) subs of
                Just (Var v) ->
                    Exists v (ffolSubstitutionQuantifiedVars subs h)

                _ ->
                    Exists ( xn, xsbi, xspi ) (ffolSubstitutionQuantifiedVars subs h)

        Taut ->
            Taut

        Insat ->
            Insat


{-| It gives the universal closure of a formula
-}
ffolUniversalClosure : FormulaFOL -> FormulaFOL
ffolUniversalClosure f =
    let
        openVars =
            List.filter (\v -> ffolHasFreeInstanceOfVar f v) <| ffolVarSymbols f
    in
    ffolRenameVars <| List.foldl (\x ac -> Forall x ac) f openVars


{-| It gives the existential closure of a formula
-}
ffolExistentialClosure : FormulaFOL -> FormulaFOL
ffolExistentialClosure f =
    let
        openVars =
            List.filter (\v -> ffolHasFreeInstanceOfVar f v) <| ffolVarSymbols f
    in
    ffolRenameVars <| List.foldl (\x ac -> Exists x ac) f openVars



---------------------
-- INTERPRETATIONS --
---------------------


{-| It defines an interpretation in First Order Logic, this is a pair of a set of elements (universe) and a record with the following keys and values:

  - key:`const`, value: A dictionary that asigns to each constant symbol a element of the universe.

  - key:`func`, value: A dictionary that asigns to each function symbol, $f$, a tuple whose first argument regards to the arity, $n$, and second one a dictionary (who emulates a total function) that assigns to each posible k-tuple (as a list) of elements of the universe an element of this universe.

  - key:`pred`, value: A dictionary that asigns to each predicate symbol, $P$, a tuple whose first argument regards to the arity, $n$, and second one the set of k-tuples (as lists) of elements of the universe that verifies the predicate.

-}
type alias L_Structure comparable =
    ( Set comparable
    , { const : Dict Ident comparable
      , func : Dict Ident ( Int, Dict (List comparable) comparable )
      , pred : Dict Ident ( Int, Set (List comparable) )
      }
    )


{-| It checks that a L\_Structure is valid, that is:

  - If all the values asigned to the constants are in the universe

  - For each function symbol, of arity k, all the possible k-tuples (as lists) of elements for the universe must be in the associated dictionary, and all the elements of its range must be in the universe.

  - For each predicate symbol, all the elements of the associated set must be lists whose length matches with the regarding arity and whose elements belongs to the universe

-}
lStructureIsValid : L_Structure comparable -> Bool
lStructureIsValid ( u, i ) =
    (List.all (\v -> Set.member v u) <| Dict.values i.const)
        && (List.all
                (\( ar, f_M ) ->
                    (List.all (\v -> Set.member v u) <| Dict.values f_M)
                        && (List.length (Dict.keys f_M) == Set.size u ^ ar)
                        && List.all (\t -> List.member t (Dict.keys f_M)) (LE.cartesianProduct <| List.repeat ar (Set.toList u))
                )
            <|
                Dict.values i.func
           )
        && (List.all
                (\( ar, p_M ) ->
                    List.all (\e -> List.length e == ar && List.all (\v -> Set.member v u) e) <| Set.toList p_M
                )
            <|
                Dict.values i.pred
           )


{-| It calculates the interpretation of a closed term regarding to a L\_structure. If it is not interpretable by the L\_struncture then it returns Nothing.
-}
termInterpretation : Term -> L_Structure comparable -> Maybe comparable
termInterpretation t ls =
    if lStructureIsValid ls then
        termInterpretationAux t Dict.empty ls

    else
        Nothing



-- It calculates the interpretation of a closed term regarding to a L\_structure and an assignation of values for the variables.


termInterpretationAux : Term -> Dict Variable comparable -> L_Structure comparable -> Maybe comparable
termInterpretationAux t vars_val ( u, i ) =
    case t of
        Var x ->
            Maybe.andThen
                (\v ->
                    if Set.member v u then
                        Just v

                    else
                        Nothing
                )
                (Dict.get x vars_val)

        Func f_ [] ->
            Dict.get f_ i.const

        Func f_ ts ->
            Maybe.andThen
                (\( ar, f_M ) ->
                    if List.length ts == ar then
                        Maybe.andThen
                            (\args -> Dict.get args f_M)
                            (termsInterpretationAux ts vars_val ( u, i ))

                    else
                        Nothing
                )
                (Dict.get f_ i.func)


{-| It calculates the interpretations of a list of closed terms, if any of them is not interpretable then it returns Nothing.
-}
termsInterpretation : List Term -> L_Structure comparable -> Maybe (List comparable)
termsInterpretation ts ls =
    if lStructureIsValid ls then
        ME.combine <| List.map (\t -> termInterpretationAux t Dict.empty ls) ts

    else
        Nothing



-- It calculates the interpretations of a list of closed terms and an asignation for the variables, if any of them is not interpretable then it returns Nothing.


termsInterpretationAux : List Term -> Dict Variable comparable -> L_Structure comparable -> Maybe (List comparable)
termsInterpretationAux ts vars_val ls =
    ME.combine <| List.map (\t -> termInterpretationAux t vars_val ls) ts


{-| It calculates the valuation of a formula regarding to an interpretation. If the formula is not closed or any element is not interpretable it returns Nothing.
-}
ffolValuation : FormulaFOL -> L_Structure comparable -> Maybe Bool
ffolValuation f ls =
    if (not << ffolIsClosed) f then
        Nothing

    else if lStructureIsValid ls then
        ffolValuationAux f Dict.empty ls

    else
        Nothing


ffolValuationAux : FormulaFOL -> Dict Variable comparable -> L_Structure comparable -> Maybe Bool
ffolValuationAux f vars_val ( u, i ) =
    case f of
        Pred p_ ts ->
            Maybe.andThen
                (\( ar, p_M ) ->
                    if List.length ts == ar then
                        Maybe.map
                            (\args -> Set.member args p_M)
                            (termsInterpretationAux ts vars_val ( u, i ))

                    else
                        Nothing
                )
                (Dict.get p_ i.pred)

        Equal t1 t2 ->
            Maybe.map2 (==) (termInterpretationAux t1 vars_val ( u, i )) (termInterpretationAux t2 vars_val ( u, i ))

        Neg g ->
            Maybe.map not (ffolValuationAux g vars_val ( u, i ))

        Conj g h ->
            Maybe.map2 (&&) (ffolValuationAux g vars_val ( u, i )) (ffolValuationAux h vars_val ( u, i ))

        Disj g h ->
            Maybe.map2 (||) (ffolValuationAux g vars_val ( u, i )) (ffolValuationAux h vars_val ( u, i ))

        Impl g h ->
            Maybe.map2 (\x y -> not x || y) (ffolValuationAux g vars_val ( u, i )) (ffolValuationAux h vars_val ( u, i ))

        Equi g h ->
            Maybe.map2 (==) (ffolValuationAux g vars_val ( u, i )) (ffolValuationAux h vars_val ( u, i ))

        Exists x g ->
            Maybe.map (List.any identity) <|
                ME.combine <|
                    List.map
                        (\o -> ffolValuationAux g (Dict.insert x o vars_val) ( u, i ))
                        (Set.toList u)

        Forall x g ->
            Maybe.map (List.all identity) <|
                ME.combine <|
                    List.map
                        (\o -> ffolValuationAux g (Dict.insert x o vars_val) ( u, i ))
                        (Set.toList u)

        Insat ->
            Just False

        Taut ->
            Just True


{-| It calculates the valuation of a set of closed formulas regarding to an interpretation. If any formula is interpretable it returns Nothing.
-}
sfolInterpretation : SetFOL -> L_Structure comparable -> Maybe Bool
sfolInterpretation fs ls =
    if List.any (not << ffolIsClosed) fs then
        Nothing

    else if lStructureIsValid ls then
        Maybe.map (List.all identity) <|
            ME.combine <|
                List.map (\f -> ffolValuation f ls) fs

    else
        Nothing



------------
-- PARSER --
------------
-- It removes the spaces of a string


cleanSpaces : String -> String
cleanSpaces x =
    String.replace " " "" <| String.replace "\n" "" x


{-| It reads the formula from a string. It returns a tuple with may be a formula (if it can be read it), the input considerated to parse and a message of error it it is not able to performs the parsing. The rules of the notation are:

  - The variables correspond to alphanumeric strings, starting with an uppercase character, and optionally indexed by sequences of natural numbers, which have been written between the symbols `_{` and `}` and separated by commas. For example: `X`,`Y_{1}`, `   Xa_{1,1}`.
  - The functions are described analogously to the variables but starting with a lowercase character. In addition, the arguments, if any, are specified between parentheses and separated by commas. Examples of constants `a`, `b_{1}`,`john`, and functions (not constants): `f(x)`, `g_{1}(X, a)`,`*father(john)`, ...
  - Predicates are described in a similar way to functions, as strings of characters, the first in uppercase, and followed, if applicable, by a list of terms, specified in parentheses and separated by commas, in the same way as presented for functions. Examples of predicates `P`,`Q_{1}(X)`,`Uncle(*john, *paul)`, ...
  - The use of connectives is equivalent proposed for propositional logic, using `&` for conjunction, `|` for disjunction, `->` for implication, `<->` for equivalence and `¬` or `-` for negation with classical priority(negation, conjunction, disjunction, implication, equivalence) and the use of parentheses to indicate another association priority.
  - Quantifiers are described as `!E` for the existential`!A` for the universal, followed by the variable indicated in brackets, `[` and `]`, and by the quantized formula. As an example, the inductive property on a function (f) can be expressed as: `!A[X_{1}] !A[X_{2}](f(X_{1}) = f(X_{2}) -> X_{1} = f(X_{2}))`, or the membership of a value (a) to the range of a function (g) like `!E[x](g(X) = a))`.
  - As in propositional logic, the valid formula is defined by `!T` and the unsatisfiable formula for`!F`.
  - The external parentheses of the formulas should not be put, since the Parser will put them automatically, so their use or not is irrelevant.
    Error messages are not perfect but we're working to improve it.

-}
ffolReadFromString : String -> ( Maybe FormulaFOL, String, String )
ffolReadFromString x =
    case cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run ffolParser ("(" ++ s ++ ")") of
                Ok y ->
                    ( Maybe.Just y, ffolToInputString y, "" )

                Err y ->
                    ( Maybe.Nothing, "(" ++ s ++ ")", "Error: " ++ String.replace "\"" "'" (Debug.toString y) )


{-| It extract the formula readed. If it is Nothing it returns Insat
-}
ffolReadExtraction : ( Maybe FormulaFOL, String, String ) -> FormulaFOL
ffolReadExtraction ( f, _, _ ) =
    Maybe.withDefault Insat f


{-| It reads the formula from a string. It returns the Formula if the string si correct, otherwise it returns Insat.
-}
ffolRead : String -> FormulaFOL
ffolRead =
    ffolReadExtraction << ffolReadFromString


{-| It reads a set of formulas from a string. Each string that corresponds to each of the formulas of the set must be ended by a point `.`
(the last formula can, optionally, not be ended by a point).
-}
sfolRead : String -> SetFOL
sfolRead fs =
    let
        fsRead =
            List.map ffolReadFromString <| List.filter (not << String.isEmpty << cleanSpaces) <| String.split "." fs
    in
    if List.any (\( mf, _, _ ) -> mf == Nothing) fsRead then
        []

    else
        List.map ffolReadExtraction fsRead


termToInputString : Term -> String
termToInputString x =
    case x of
        Var ( vname, sb, sp ) ->
            (String.toUpper << String.left 1) vname
                ++ String.dropLeft 1 vname
                ++ (if List.isEmpty sb then
                        ""

                    else
                        "_{" ++ (String.join "," <| List.map String.fromInt sb) ++ "}"
                   )
                ++ (if sp <= 0 then
                        ""

                    else
                        "^{" ++ String.fromInt sp ++ "}"
                   )

        Func ( fname, [] ) ts ->
            (String.toLower << String.left 1) fname ++ String.dropLeft 1 fname ++ termsToString ts

        Func ( fname, findices ) ts ->
            (String.toLower << String.left 1) fname ++ String.dropLeft 1 fname ++ "_{" ++ (String.join "," <| List.map String.fromInt findices) ++ "}" ++ termsToString ts


termsToInputString : List Term -> String
termsToInputString ts =
    if List.isEmpty ts then
        ""

    else
        "(" ++ (String.join ", " <| List.map termToInputString ts) ++ ")"


{-| It gives the corresponding input syntax of a formula
-}
ffolToInputString : FormulaFOL -> String
ffolToInputString f =
    case f of
        Exists x g ->
            "!E[" ++ termToInputString (Var x) ++ "]" ++ ffolToInputString g

        Forall x g ->
            "!A[" ++ termToInputString (Var x) ++ "]" ++ ffolToInputString g

        Pred ( pname, [] ) ts ->
            (String.toUpper << String.left 1) pname ++ String.dropLeft 1 pname ++ termsToInputString ts

        Pred ( pname, pindices ) ts ->
            (String.toUpper << String.left 1) pname ++ String.dropLeft 1 pname ++ "_{" ++ (String.join "," <| List.map String.fromInt pindices) ++ "}" ++ termsToInputString ts

        Equal t1 t2 ->
            termToInputString t1 ++ "=" ++ termToInputString t2

        Neg g ->
            "¬" ++ ffolToInputString g

        Conj g h ->
            "(" ++ ffolToInputString g ++ "&" ++ ffolToInputString h ++ ")"

        Disj g h ->
            "(" ++ ffolToInputString g ++ "|" ++ ffolToInputString h ++ ")"

        Impl g h ->
            "(" ++ ffolToInputString g ++ "->" ++ ffolToInputString h ++ ")"

        Equi g h ->
            "(" ++ ffolToInputString g ++ "<->" ++ ffolToInputString h ++ ")"

        Taut ->
            "!T"

        _ ->
            "!F"



-- PARSER BUIDER FUCTIONS
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
            |= folVarNameParser
        ]


folVarNameParser : Parser String
folVarNameParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isUpper
        |. Parser.chompWhile Char.isAlpha
        |> Parser.getChompedString


folVarSubindexedParser : Parser Variable
folVarSubindexedParser =
    Parser.succeed (\x y -> ( x, y, 0 ))
        |= folVarNameParser
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
        |= folVarNameParser
        |. Parser.symbol "^{"
        |= Parser.int
        |. Parser.symbol "}"


folVarSubSuperIndexedParser : Parser Variable
folVarSubSuperIndexedParser =
    Parser.succeed (\x y z -> ( x, y, z ))
        |= folVarNameParser
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


folTermIdentifierParser : Parser Ident
folTermIdentifierParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable folTermIdentifierSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= folTermNameParser
        , Parser.succeed (\x -> ( x, [] ))
            |= Parser.map String.fromInt Parser.int
        ]


folTermIdentifierSubindexedParser : Parser Ident
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


folPredIdentifierParser : Parser Ident
folPredIdentifierParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable folPredIdentifierSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= folPredNameParser
        ]


folPredIdentifierSubindexedParser : Parser Ident
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
        [ succeed Func
            |= folTermIdentifierParser
            |= folListTermParser
        , succeed Var
            |= folVariableParser
        ]


folListTermParser : Parser (List Term)
folListTermParser =
    Parser.oneOf
        [ succeed identity
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> folEnumerationTermParser)
            |. Parser.symbol ")"
        , succeed []
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



-- It defines the syntax of formulas and its processing enusuring that it corresponds to the parser of all of the string given.


ffolParser : Parser FormulaFOL
ffolParser =
    Parser.succeed identity
        |= ffolParserAux
        |. Parser.end


ffolParserAux : Parser FormulaFOL
ffolParserAux =
    Parser.oneOf
        [ Parser.succeed Exists
            |. Parser.oneOf
                [ Parser.symbol "!E"
                , Parser.symbol "∃"
                ]
            |. Parser.symbol "["
            |= folVariableParser
            |. Parser.symbol "]"
            |= Parser.lazy (\_ -> ffolParserAux)
        , Parser.succeed Forall
            |. Parser.oneOf
                [ Parser.symbol "!A"
                , Parser.symbol "∀"
                ]
            |. Parser.symbol "["
            |= folVariableParser
            |. Parser.symbol "]"
            |= Parser.lazy (\_ -> ffolParserAux)
        , Parser.succeed Insat
            |. Parser.oneOf
                [ Parser.symbol "!F"
                , Parser.symbol "⊥"
                ]
        , Parser.succeed Taut
            |. Parser.oneOf
                [ Parser.symbol "!T"
                , Parser.symbol "⊤"
                ]
        , Parser.backtrackable <|
            Parser.succeed Equal
                |= folTermParser
                |. Parser.symbol "="
                |= folTermParser
        , Parser.succeed Pred
            |= folPredIdentifierParser
            |= folListTermParser
        , Parser.succeed Neg
            |. Parser.oneOf
                [ Parser.symbol "¬"
                , Parser.symbol "-"
                ]
            |= Parser.lazy (\_ -> ffolParserAux)
        , succeed identity
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> expression)
            |. Parser.symbol ")"
        ]



-- It defines the propositional infixed operators (and, or, implication and equivalence)


type Operator
    = AndOp
    | OrOp
    | ImplOp
    | EquivOp


operator : Parser Operator
operator =
    Parser.oneOf
        [ Parser.succeed AndOp
            |. Parser.symbol "&"
        , Parser.succeed AndOp
            |. Parser.symbol "∧"
        , Parser.succeed OrOp
            |. Parser.symbol "|"
        , Parser.succeed OrOp
            |. Parser.symbol "∨"
        , Parser.succeed ImplOp
            |. Parser.symbol "->"
        , Parser.succeed ImplOp
            |. Parser.symbol "→"
        , Parser.succeed EquivOp
            |. Parser.symbol "<->"
        , Parser.succeed EquivOp
            |. Parser.symbol "↔"
        ]


expression : Parser FormulaFOL
expression =
    ffolParserAux |> Parser.andThen (expressionAux [])



-- -- It defines the propositional infixed operators (and, or, implication and equivalence)


expressionAux : List ( FormulaFOL, Operator ) -> FormulaFOL -> Parser FormulaFOL
expressionAux revOps expr =
    Parser.oneOf
        [ Parser.succeed Tuple.pair
            |= operator
            |= ffolParserAux
            |> Parser.andThen (\( op, newExpr ) -> expressionAux (( expr, op ) :: revOps) newExpr)
        , Parser.lazy (\_ -> Parser.succeed (finalize revOps expr))
        ]



-- It defines the priority and the processing of the operators and formulas.


finalize : List ( FormulaFOL, Operator ) -> FormulaFOL -> FormulaFOL
finalize revOps finalExpr =
    case revOps of
        [] ->
            finalExpr

        -- AND EXPRESSIONS CASES
        -- And operation have the maximum priorty, so module have a unique case
        ( expr, AndOp ) :: otherRevOps ->
            finalize otherRevOps (Conj expr finalExpr)

        -- OR EXPRESSIONS CASES
        -- Or have the second maximum priority, so we need to determine how parser's going to do if it searches an and after, and if it searches something different.
        ( expr, OrOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Disj (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, OrOp ) :: otherRevOps ->
            finalize otherRevOps (Disj expr finalExpr)

        -- IMPLICATION EXPRESSIONS CASES
        ( expr, ImplOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Impl (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, ImplOp ) :: ( expr2, OrOp ) :: otherRevOps ->
            Impl (finalize (( expr2, OrOp ) :: otherRevOps) expr) finalExpr

        ( expr, ImplOp ) :: otherRevOps ->
            finalize otherRevOps (Impl expr finalExpr)

        -- EQUIVALATION EXPRESSIONS CASES
        ( expr, EquivOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Equi (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, EquivOp ) :: ( expr2, OrOp ) :: otherRevOps ->
            Equi (finalize (( expr2, OrOp ) :: otherRevOps) expr) finalExpr

        ( expr, EquivOp ) :: ( expr2, ImplOp ) :: otherRevOps ->
            Equi (finalize (( expr2, ImplOp ) :: otherRevOps) expr) finalExpr

        ( expr, EquivOp ) :: otherRevOps ->
            finalize otherRevOps (Equi expr finalExpr)


{-| It returns a tuple with may be a substitution (if it can be read it), the input considerated to parse and a message of error if it is not able to performs the parsing.
-- Messages are not perfect but we're working to improve it.
-}
substitutionReadFromString : String -> ( Maybe Substitution, String, String )
substitutionReadFromString x =
    case cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run substitutionParser s of
                Ok y ->
                    ( Maybe.Just y, substitutionToInputString y, "" )

                Err y ->
                    ( Maybe.Nothing, s, "Error: " ++ String.replace "\"" "'" (Debug.toString y) )


{-| It generates the corresponding string input of a substitution
-}
substitutionToInputString : Substitution -> String
substitutionToInputString s =
    "{" ++ (String.join ", " <| List.map (\( x, t ) -> x ++ "/" ++ termToInputString t) <| List.map (\( x, y ) -> ( termToInputString (Var x), y )) <| Dict.toList s) ++ "}"


{-| It extract the formula readed. If it is Nothing it returns Insat
-}
substitutionReadExtraction : ( Maybe Substitution, String, String ) -> Substitution
substitutionReadExtraction ( s, _, _ ) =
    Maybe.withDefault Dict.empty s



-- It gives the definition of the parser to read substitutions


substitutionParser : Parser Substitution
substitutionParser =
    succeed Dict.fromList
        |= Parser.sequence
            { start = "{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = substitutionItemParser
            , trailing = Forbidden -- demand a trailing semi-colon
            }



-- It gives the definition to parsing an item of the subtitution


substitutionItemParser : Parser ( Variable, Term )
substitutionItemParser =
    succeed Tuple.pair
        |= folVariableParser
        |. Parser.symbol "/"
        |= folTermParser



--================--
-- REPRESENTATION --
--================--


{-| It generates the string of an identifier
-}
identToString : Ident -> String
identToString i =
    case i of
        ( iname, [] ) ->
            iname

        ( iname, iindices ) ->
            iname ++ (replaceBySubscript <| (String.join "," <| List.map String.fromInt iindices))



{-| It generates the string of a variable
-}
varToString : Variable -> String
varToString ( vname, sb, sp ) =
    (String.toLower << String.left 1) vname
        ++ String.dropLeft 1 vname
        ++ (if List.isEmpty sb then
                ""

            else
                replaceBySubscript <| (String.join "," <| List.map String.fromInt sb)
           )
        ++ (if sp <= 0 then
                ""

            else
                replaceBySuperscript <| String.fromInt sp
           )


{-| It generates the string of a list of identifier
-}
identsToString : List Ident -> String
identsToString is =
    "[" ++ (String.join ", " <| List.map identToString is) ++ "]"


{-| It generates the string of a list of variables
-}
varsToString : List Variable -> String
varsToString vs =
    "[" ++ (String.join ", " <| List.map varToString vs) ++ "]"


{-| It generates the string of a term
-}
termToString : Term -> String
termToString t =
    case t of
        Var v ->
            varToString v

        Func ( fname, [] ) ts ->
            fname ++ termsToString ts

        Func ( fname, findices ) ts ->
            fname ++ (replaceBySubscript <| (String.join "," <| List.map String.fromInt findices)) ++ termsToString ts


{-| It generates the string of a list of terms (parameters)
-}
termsToString : List Term -> String
termsToString ts =
    if List.isEmpty ts then
        ""

    else
        "(" ++ (String.join "," <| List.map termToString ts) ++ ")"


{-| It generates the string of a First Order Logic Formula,
-}
ffolToString : FormulaFOL -> String
ffolToString f =
    case f of
        Pred ( pname, [] ) ts ->
            pname ++ termsToString ts

        Pred ( pname, pindices ) ts ->
            pname ++ (replaceBySubscript <| (String.join "," <| List.map String.fromInt pindices)) ++ termsToString ts

        Equal t1 t2 ->
            "(" ++ termToString t1 ++ " = " ++ termToString t2 ++ ")"

        Neg (Equal t1 t2) ->
            "(" ++ termToString t1 ++ " != " ++ termToString t2 ++ ")"

        Neg p ->
            "¬" ++ ffolToString p

        Conj p q ->
            "(" ++ ffolToString p ++ " ∧ " ++ ffolToString q ++ ")"

        Disj p q ->
            "(" ++ ffolToString p ++ " ∨ " ++ ffolToString q ++ ")"

        Impl p q ->
            "(" ++ ffolToString p ++ " → " ++ ffolToString q ++ ")"

        Equi p q ->
            "(" ++ ffolToString p ++ " ↔ " ++ ffolToString q ++ ")"

        Exists v p ->
            "∃" ++ (termToString <| Var v) ++ ffolToString p

        Forall v p ->
            "∀" ++ (termToString <| Var v) ++ ffolToString p

        Taut ->
            "⊤"

        Insat ->
            "⊥"

{-| It generates the string of a First Order Logic Set of formulas,
-}
sfolToString : SetFOL -> String
sfolToString fs =
    "{" ++ (String.join ", " <| List.map ffolToString fs) ++ "}"


{-| It generates the string of an identifier using Latex notation
-}
identToMathString : Ident -> String
identToMathString v =
    case v of
        ( vname, [] ) ->
            vname

        ( vname, vindices ) ->
            vname ++ "_{" ++ (String.join "," <| List.map String.fromInt vindices) ++ "}"


{-| It generates the string of a variable using Latex Notation
-}
varToMathString : Variable -> String
varToMathString ( vname, sb, sp ) =
    (String.toLower << String.left 1) vname
        ++ String.dropLeft 1 vname
        ++ (if List.isEmpty sb then
                ""

            else
                "_{" ++ (String.join "," <| List.map String.fromInt sb) ++ "}"
           )
        ++ (if sp <= 0 then
                ""

            else
                replaceBySuperscript <| String.fromInt sp
           )


{-| It generates the string of a list of identifier
-}
identsToMathString : List Ident -> String
identsToMathString is =
    "[" ++ (String.join ", " <| List.map identToMathString is) ++ "]"


{-| It generates the string of a list of identifier
-}
varsToMathString : List Variable -> String
varsToMathString vs =
    "[" ++ (String.join ", " <| List.map varToMathString vs) ++ "]"


{-| It generates the string of a term using latex notation
-}
termToMathString : Term -> String
termToMathString t =
    case t of
        Var v ->
            varToMathString v

        Func ( fname, [] ) ts ->
            fname ++ termsToMathString ts

        Func ( fname, findices ) ts ->
            fname ++ "_{" ++ (String.join "," <| List.map String.fromInt findices) ++ "}" ++ termsToMathString ts


{-| It generates the string of a list of terms (parameters) using latex notation
-}
termsToMathString : List Term -> String
termsToMathString ts =
    if List.isEmpty ts then
        ""

    else
        "( " ++ (String.join ", " <| List.map termToMathString ts) ++ " )"


{-| It generates the string of a First Order Logic Formula using latex notation
-}
ffolToMathString : FormulaFOL -> String
ffolToMathString f =
    case f of
        Pred ( pname, [] ) ts ->
            pname ++ termsToString ts

        Pred ( pname, pindices ) ts ->
            pname ++ "_{ " ++ (String.join "," <| List.map String.fromInt pindices) ++ " }" ++ termsToMathString ts

        Equal t1 t2 ->
            " \\left( " ++ termToMathString t1 ++ " = " ++ termToMathString t2 ++ " \\right) "

        Neg p ->
            " \\neg " ++ ffolToMathString p

        Conj p q ->
            " \\left( " ++ ffolToMathString p ++ " \\wedge " ++ ffolToMathString q ++ " \\right) "

        Disj p q ->
            " \\left( " ++ ffolToMathString p ++ " \\vee " ++ ffolToMathString q ++ " \\right) "

        Impl p q ->
            " \\left( " ++ ffolToMathString p ++ " \\rightarrow " ++ ffolToMathString q ++ " \\right) "

        Equi p q ->
            " \\left( " ++ ffolToMathString p ++ " \\leftrightarrow " ++ ffolToMathString q ++ " \\right) "

        Exists v p ->
            " \\exists " ++ (termToMathString <| Var v) ++ " \\," ++ ffolToMathString p

        Forall v p ->
            " \\forall " ++ (termToMathString <| Var v) ++ " \\," ++ ffolToMathString p

        Taut ->
            " \\top "

        Insat ->
            " \\perp "


{-| It generates the string of a First Order Logic Set of formulas using latex notation as an array
-}
sfolToMathString : SetFOL -> String
sfolToMathString fs =
    "\\lbrace " ++ (String.join ", " <| List.map ffolToMathString fs) ++ " \\rbrace"


{-| It generates the string of a First Order Logic Set of formulas using latex notation as an array
-}
sfolToMathString2 : SetFOL -> String
sfolToMathString2 fs =
    "\\begin{array}{l} " ++ (String.join " \\\\ " <| List.map ffolToMathString fs) ++ " \\end{array}"


{-| It gives a string representation of a form tree
-}
formTreeToString : Graph FormulaFOL () -> String
formTreeToString t =
    Graph.toString (\x -> Just <| ffolToString x) (\_ -> Nothing) t


{-| It gives a string representation of a form tree using DOT format
-}
formTreeToDOT : Graph FormulaFOL () -> String
formTreeToDOT t =
    let
        myStyles =
            { defaultStyles | node = "shape=plaintext, color=black", edge = "dir=none, color=blue" }
    in
    String.replace "\n" "" <| String.replace "\"" ">" <| String.replace "=\"" "=<" <| Graph.DOT.outputWithStyles myStyles (\x -> Just <| ffolToString x) (\_ -> Nothing) t


{-| It gives a string representation of a substitution using latex notation
-}
substitutionToString : Substitution -> String
substitutionToString s =
    "{" ++ (String.join ", " <| List.map (\( x, t ) -> x ++ "/" ++ termToString t) <| List.map (\( x, y ) -> ( termToString (Var x), y )) <| Dict.toList s) ++ "}"


{-| It gives a string representation of a substitution using latex notation
-}
substitutionToMathString : Substitution -> String
substitutionToMathString s =
    " \\lbrace " ++ (String.join ", " <| List.map (\( x, t ) -> x ++ "/" ++ termToMathString t) <| List.map (\( x, y ) -> ( termToMathString (Var x), y )) <| Dict.toList s) ++ " \\rbrace "


{-| It gives a L-structure as string. It needs a funtion that gives the string representation of the elements of the L-Structure
-}
l_StructureToString : L_Structure comparable -> (comparable -> String) -> String
l_StructureToString ( u, i ) ra =
    let
        universeString =
            "U: {" ++ (String.join ", " <| List.map ra <| Set.toList u) ++ "}"

        constString =
            "c={" ++ (String.join ", " <| List.map ra <| Dict.values i.const) ++ "}"

        funcString =
            let
                fInternalString _ ar f_M =
                    String.join ";" <|
                        List.map
                            (\e -> "(" ++ (String.join "," <| List.map ra e) ++ "):" ++ (Maybe.withDefault "" <| Maybe.map ra <| Dict.get e f_M))
                            (LE.cartesianProduct <| List.repeat ar <| Set.toList u)
            in
            let
                fString ( f, ( ar, f_M ) ) =
                    f ++ ": {" ++ fInternalString f ar f_M ++ "}"
            in
            String.join "\n" <| List.map fString <| List.map (\( x, y ) -> ( termToString (Func x []), y )) <| Dict.toList i.func

        predString =
            let
                pInternalString ar p_M =
                    String.join ";" <|
                        List.foldr
                            (\e ac ->
                                if Set.member e p_M then
                                    ("(" ++ (String.join "," <| List.map ra e) ++ ")") :: ac

                                else
                                    ac
                            )
                            []
                            (LE.cartesianProduct <| List.repeat ar <| Set.toList u)
            in
            let
                pString ( p, ( ar, p_M ) ) =
                    p ++ ": {\n" ++ pInternalString ar p_M ++ "\n}"
            in
            String.join "\n" <| List.map pString <| List.map (\( x, y ) -> ( ffolToString (Pred x []), y )) <| Dict.toList i.pred
    in
    String.join "\n\n" [ universeString, constString, funcString, predString ]


{-| It transforms a SetFOL into a new SetFOL by negating each formula of the set.
-}
sfolNegation : SetFOL -> SetFOL
sfolNegation =
    List.map ffolNegation


{-| It transforms a SetFOL into a FormulaFOL using conjuction between formulas. If Set is empty Taut is given
-}
sfolConjunction : SetFOL -> FormulaFOL
sfolConjunction fs =
    case fs of
        [] ->
            Taut

        x :: xs ->
            List.foldl (\f ac -> Conj ac f) x xs


{-| It transforms a SetPL into a FormulaFOL using disjunction between formulas. If Set is empty Insat is given
-}
sfolDisjunction : SetFOL -> FormulaFOL
sfolDisjunction fs =
    case fs of
        [] ->
            Insat

        x :: xs ->
            List.foldl (\f ac -> Disj ac f) x xs
