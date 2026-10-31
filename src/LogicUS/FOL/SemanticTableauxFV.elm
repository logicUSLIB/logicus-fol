module LogicUS.FOL.SemanticTableauxFV exposing
    ( FVTableau, FVNode, FVRule(..), FVResult(..), FVLimits
    , defaultLimits, semanticTableauFV, semanticTableauFVWith, semanticTableauFVIsClosed
    , semanticTableauFVSummary, semanticTableauFVToString, semanticTableauFVToDOT
    )

{-| Semantic tableaux with free variables.

In the tableau of the module `SemanticTableaux` a universal formula (γ) is instantiated with closed terms, which have
to be guessed in advance. Here a γ formula is instantiated with a new **free variable**, and the variables get their
values when they are needed to close a branch: two literals close a branch when their atoms **unify**, and the unifier
is applied to the whole tableau (the variables are _rigid_: a variable has the same value in every branch). An
existential formula (δ) is instantiated with a Skolem term on the free variables of the formula (the δ⁺ rule): a new
constant if it has none.

In each branch the rules are applied in this order: double negations, α and δ formulas, then β formulas (first one
with a component that closes a branch at once), then γ formulas (the least used one). A formula already in the branch
is not added again, and a β formula with a component in the branch is not expanded.

The search for a closed tableau proves the branches from left to right. When a literal can close the branch in
several ways, or can also be kept open (because the unifier would bind variables that another branch may need), each
way is an alternative, and the search backtracks to the next one when a later branch cannot be closed. A closure that
binds no variable, or only variables that no other open branch has, is never undone. The number of times that each γ
formula can be used in a branch grows from 1 to a limit (iterative deepening), so that the simplest closed tableaux
are found first.

The answer is one of three:

  - `Closed`: every branch is closed, so the set of formulas is unsatisfiable.
  - `Open`: a branch is fully expanded and open, and has no γ formulas, so the set is satisfiable (its literals
    define a Herbrand model).
  - `Unknown`: no closed tableau was found within the limits. First-order satisfiability is undecidable, and a
    branch with a γ formula (other than a vacuous one, like `∀x P(a)`) is never fully expanded.

Equality is only used to close branches with `¬(t = t)` (after unification), and with complementary equalities: a
fully expanded open branch with an equality `s = t` between different terms gives `Unknown`. The module
`SemanticTableauxEQ` has rules for equality.

Free variables of the input formulas are treated as constants (they are not bound by the unifiers).


# Types

@docs FVTableau, FVNode, FVRule, FVResult, FVLimits


# Algorithm

@docs defaultLimits, semanticTableauFV, semanticTableauFVWith, semanticTableauFVIsClosed


# Representation

@docs semanticTableauFVSummary, semanticTableauFVToString, semanticTableauFVToDOT

-}

import Dict exposing (Dict)
import Graph.Tree as GTree exposing (Tree)
import Json.Encode as JSONE
import List.Extra as LE
import LogicUS.FOL.SyntaxSemantics as FOL_SS exposing (FormulaFOL(..), Ident, SetFOL, Substitution, Term(..), Variable)
import LogicUS.FOL.TableauDisplay as TD exposing (DTree(..))
import Set exposing (Set)



--===========--
--   TYPES   --
--===========--


{-| A free-variable tableau: the tree, the answer, the substitution of the free variables, the limit on the uses of
the γ formulas with which the answer was obtained, and the number of steps of the search.
-}
type alias FVTableau =
    { tree : Tree FVNode
    , result : FVResult
    , substitution : Substitution
    , gammaUses : Int
    , depth : Int
    , steps : Int
    }


{-| A node of the tree: its number `i` (its depth in the branch; 0 for the leaves), its formula (with the free variables it was given), the
rule that produced it, the numbers of the nodes it comes from, and a substitution: the instantiation of the bound
variable for γ and δ, and the bindings of the free variables made to close the branch for a closure.
-}
type alias FVNode =
    { i : Int
    , f : FormulaFOL
    , rule : FVRule
    , from : List Int
    , subs : Substitution
    }


{-| The rule that produced a node. `Alpha` and `Beta` carry the component (1 or 2). The leaves are `Closure` (closed
branch), `OpenLeaf` (fully expanded open branch), `LimitLeaf` (a branch stopped by the limits) and `Unexplored` (a
branch that the search did not reach).
-}
type FVRule
    = Premise
    | DoubleNeg
    | Alpha Int
    | Beta Int
    | Gamma
    | Delta
    | Closure
    | OpenLeaf
    | LimitLeaf
    | Unexplored


{-| The answer of the search. `Unknown` says which limits were reached, or that an open branch has equalities.
-}
type FVResult
    = Closed
    | Open
    | Unknown { gammaUses : Bool, depth : Bool, steps : Bool, equality : Bool }


{-| The limits of the search: the maximum number of uses of each γ formula in a branch (the iterative deepening goes
from 1 to it), the maximum number of rule applications in a branch (at most 250, so that the tree can be drawn without
overflowing the call stack of a browser), and the maximum number of steps of the search.
-}
type alias FVLimits =
    { gammaUses : Int
    , depth : Int
    , steps : Int
    }


{-| Limits suitable for the problems of a logic course: `{ gammaUses = 3, depth = 40, steps = 20000 }`.
-}
defaultLimits : FVLimits
defaultLimits =
    { gammaUses = 3, depth = 40, steps = 20000 }



--====================--
--   CLASSIFICATION   --
--====================--


type Kind
    = KClose
    | KTrue
    | KLit Bool FormulaFOL
    | KDN FormulaFOL
    | KAlpha FormulaFOL FormulaFOL
    | KBeta FormulaFOL FormulaFOL
    | KGamma Variable FormulaFOL
    | KDelta Variable FormulaFOL


classify : FormulaFOL -> Kind
classify f =
    let
        neg =
            FOL_SS.ffolNegation
    in
    case f of
        Pred _ _ ->
            KLit True f

        Equal _ _ ->
            KLit True f

        Neg ((Pred _ _) as a) ->
            KLit False a

        Neg ((Equal _ _) as a) ->
            KLit False a

        Neg (Neg g) ->
            KDN g

        Conj g h ->
            KAlpha g h

        Neg (Disj g h) ->
            KAlpha (neg g) (neg h)

        Neg (Impl g h) ->
            KAlpha g (neg h)

        Equi g h ->
            KAlpha (Impl g h) (Impl h g)

        Disj g h ->
            KBeta g h

        Neg (Conj g h) ->
            KBeta (neg g) (neg h)

        Impl g h ->
            KBeta (neg g) h

        Neg (Equi g h) ->
            KBeta (neg (Impl g h)) (neg (Impl h g))

        Forall x g ->
            KGamma x g

        Neg (Exists x g) ->
            KGamma x (neg g)

        Exists x g ->
            KDelta x g

        Neg (Forall x g) ->
            KDelta x (neg g)

        Taut ->
            KTrue

        Neg Insat ->
            KTrue

        Insat ->
            KClose

        Neg Taut ->
            KClose



--====================--
--   SEARCH STATE     --
--====================--


type alias NodeRec =
    { parent : Int
    , f : FormulaFOL
    , rule : FVRule
    , from : List Int
    , subs : Substitution
    }


type alias Lit =
    { id : Int, pos : Bool, atom : FormulaFOL }


type alias Gam =
    { id : Int, f : FormulaFOL, uses : Int }



-- An open branch still to be closed: its last node, the number of rules applied in it, the nodes whose formulas
-- have not been looked at yet, the formulas waiting to be expanded (α, double negations and δ first, then β, then
-- γ), its literals, all its formulas (to avoid adding the same formula twice), the free variables introduced in it
-- and the version of the substitution under which its literals were last compared.


type alias Branch =
    { last : Int
    , depth : Int
    , incoming : List ( Int, FormulaFOL )
    , easy : List ( Int, FormulaFOL )
    , betas : List ( Int, FormulaFOL )
    , gammas : List Gam
    , lits : List Lit
    , forms : List FormulaFOL
    , vset : Set Variable
    , checked : Int
    }


type alias State =
    { goals : List Branch
    , sigma : Substitution
    , vars : Set Variable
    , nodes : Dict Int NodeRec
    , next : Int
    , names : Dict String Int
    , sk : Int
    , cs : Int
    , version : Int
    , closed : Int
    }


type alias Ctx =
    { k : Int
    , depth : Int
    , maxSteps : Int
    , usedVars : Set Variable
    , usedIdents : Set Ident
    }


type alias Search =
    { st : State
    , choices : List State
    , steps : Int
    , gammaHit : Bool
    , depthHit : Bool
    , best : Maybe ( ( Int, Int ), State )
    }


type Step
    = Continue Search
    | Done Outcome


type Outcome
    = Refuted Search
    | FoundOpen Search
    | Exhausted Search
    | OutOfSteps Search


type Expansion
    = Expanded State
    | Finished
    | BlockedByGamma
    | BlockedByDepth



--====================--
--   UNIFICATION      --
--====================--


applyT : Substitution -> Term -> Term
applyT s t =
    if Dict.isEmpty s then
        t

    else
        FOL_SS.termApplySubstitution s t


applyF : Substitution -> FormulaFOL -> FormulaFOL
applyF s f =
    if Dict.isEmpty s then
        f

    else
        FOL_SS.ffolApplySubstitution s f


termVars : Term -> Set Variable -> Set Variable
termVars t acc =
    case t of
        Var x ->
            Set.insert x acc

        Func _ ts ->
            List.foldl termVars acc ts


occurs : Variable -> Term -> Bool
occurs x t =
    case t of
        Var y ->
            x == y

        Func _ ts ->
            List.any (occurs x) ts


bind : Variable -> Term -> Substitution -> Substitution
bind x t th =
    let
        s1 =
            Dict.singleton x t
    in
    Dict.insert x t (Dict.map (\_ u -> FOL_SS.termApplySubstitution s1 u) th)



-- Most general unifier (idempotent) of a list of pairs of terms, binding only the variables of the tableau.


unify : Set Variable -> List ( Term, Term ) -> Substitution -> Maybe Substitution
unify vars pairs th =
    case pairs of
        [] ->
            Just th

        ( a, b ) :: rest ->
            let
                a1 =
                    applyT th a

                b1 =
                    applyT th b
            in
            if a1 == b1 then
                unify vars rest th

            else
                case ( a1, b1 ) of
                    ( Var x, _ ) ->
                        if Set.member x vars then
                            if occurs x b1 then
                                Nothing

                            else
                                unify vars rest (bind x b1 th)

                        else
                            case b1 of
                                Var y ->
                                    if Set.member y vars then
                                        unify vars rest (bind y a1 th)

                                    else
                                        Nothing

                                _ ->
                                    Nothing

                    ( _, Var y ) ->
                        if Set.member y vars then
                            if occurs y a1 then
                                Nothing

                            else
                                unify vars rest (bind y a1 th)

                        else
                            Nothing

                    ( Func f fs, Func g gs ) ->
                        if f == g && List.length fs == List.length gs then
                            unify vars (List.map2 Tuple.pair fs gs ++ rest) th

                        else
                            Nothing



-- The unifiers that make two atoms complementary (equalities in both orientations).


atomUnifiers : Set Variable -> FormulaFOL -> FormulaFOL -> List Substitution
atomUnifiers vars a b =
    case ( a, b ) of
        ( Pred p ts, Pred q us ) ->
            if p == q && List.length ts == List.length us then
                List.filterMap identity [ unify vars (List.map2 Tuple.pair ts us) Dict.empty ]

            else
                []

        ( Equal s t, Equal u v ) ->
            LE.unique <| List.filterMap identity [ unify vars [ ( s, u ), ( t, v ) ] Dict.empty, unify vars [ ( s, v ), ( t, u ) ] Dict.empty ]

        _ ->
            []


compose : Substitution -> Substitution -> Substitution
compose th sigma =
    Dict.union th (Dict.map (\_ t -> applyT th t) sigma)



--====================--
--   THE SEARCH       --
--====================--


addNode : State -> Int -> FormulaFOL -> FVRule -> List Int -> Substitution -> ( State, Int )
addNode st parent f rule from subs =
    ( { st | nodes = Dict.insert st.next { parent = parent, f = f, rule = rule, from = from, subs = subs } st.nodes, next = st.next + 1 }
    , st.next
    )



-- Adds a chain of nodes at the end of a branch (one rule application).


extend : State -> Branch -> Int -> List ( FormulaFOL, FVRule, Substitution ) -> ( State, Branch )
extend st b from items =
    List.foldl
        (\( f, rule, subs ) ( st1, b1 ) ->
            let
                ( st2, id ) =
                    addNode st1 b1.last f rule [ from ] subs
            in
            ( st2, { b1 | last = id, incoming = b1.incoming ++ [ ( id, f ) ], forms = f :: b1.forms } )
        )
        ( st, { b | depth = b.depth + 1 } )
        items


closeBranch : State -> Branch -> List Branch -> List Int -> Substitution -> State
closeBranch st b rest from th =
    let
        ( st1, _ ) =
            addNode st b.last Insat Closure from th
    in
    if Dict.isEmpty th then
        { st1 | goals = rest, closed = st.closed + 1 }

    else
        { st1 | goals = rest, closed = st.closed + 1, sigma = compose th st.sigma, version = st.version + 1 }



-- The ways in which a new literal closes the branch: with ¬(s = t) if s and t unify, and with a complementary
-- literal of the branch.


closureOptions : State -> Branch -> Int -> Bool -> FormulaFOL -> List ( List Int, Substitution )
closureOptions st b id pos atom =
    let
        sa =
            applyF st.sigma atom

        refl =
            case ( pos, sa ) of
                ( False, Equal s t ) ->
                    case unify st.vars [ ( s, t ) ] Dict.empty of
                        Just th ->
                            [ ( [ id ], th ) ]

                        Nothing ->
                            []

                _ ->
                    []

        comps =
            List.concatMap
                (\m ->
                    if m.pos /= pos then
                        List.map (\th -> ( [ m.id, id ], th )) <| atomUnifiers st.vars sa (applyF st.sigma m.atom)

                    else
                        []
                )
                b.lits
    in
    refl ++ comps



-- A pair of literals of the branch that are complementary under the current substitution (without binding
-- anything), or a literal ¬(t = t).


quickClosure : State -> Branch -> Maybe (List Int)
quickClosure st b =
    let
        ls =
            List.map (\m -> ( m, applyF st.sigma m.atom )) b.lits

        complementary ( m1, a1 ) ( m2, a2 ) =
            m1.pos
                /= m2.pos
                && (a1
                        == a2
                        || (case ( a1, a2 ) of
                                ( Equal s t, Equal u v ) ->
                                    s == v && t == u

                                _ ->
                                    False
                           )
                   )

        search xs =
            case xs of
                [] ->
                    Nothing

                (( m, a ) as x) :: more ->
                    case ( m.pos, a ) of
                        ( False, Equal s t ) ->
                            if s == t then
                                Just [ m.id ]

                            else
                                case LE.find (complementary x) more of
                                    Just ( m2, _ ) ->
                                        Just (List.sort [ m.id, m2.id ])

                                    Nothing ->
                                        search more

                        _ ->
                            case LE.find (complementary x) more of
                                Just ( m2, _ ) ->
                                    Just (List.sort [ m.id, m2.id ])

                                Nothing ->
                                    search more
    in
    search ls



-- Looks at a new formula of the branch: closes it, or keeps it to be expanded. The result is the list of
-- alternatives, in the order in which they are tried.


processIncoming : State -> Branch -> List Branch -> Int -> FormulaFOL -> List State
processIncoming st b rest id f =
    case classify f of
        KClose ->
            [ closeBranch st b rest [ id ] Dict.empty ]

        KTrue ->
            [ { st | goals = b :: rest } ]

        KLit pos atom ->
            let
                options =
                    closureOptions st b id pos atom

                keep =
                    { st | goals = { b | lits = { id = id, pos = pos, atom = atom } :: b.lits } :: rest }
            in
            case LE.find (\( _, th ) -> Dict.isEmpty th) options of
                Just ( from, th ) ->
                    [ closeBranch st b rest (List.sort from) th ]

                Nothing ->
                    if List.isEmpty options then
                        [ keep ]

                    else
                        let
                            -- the variables that the other open branches have (under the substitution)
                            shared =
                                List.foldl (\g acc -> Set.foldl (\x acc2 -> termVars (applyT st.sigma (Var x)) acc2) acc g.vset) Set.empty rest
                        in
                        -- a closure that only binds variables of this branch does not affect the others: it is the
                        -- best choice, and there is no need to try other ones
                        case LE.find (\( _, th ) -> List.all (\x -> not (Set.member x shared)) (Dict.keys th)) options of
                            Just ( from, th ) ->
                                [ closeBranch st b rest (List.sort from) th ]

                            Nothing ->
                                List.map (\( from, th ) -> closeBranch st b rest (List.sort from) th) options ++ [ keep ]

        KBeta _ _ ->
            [ { st | goals = { b | betas = b.betas ++ [ ( id, f ) ] } :: rest } ]

        KGamma _ _ ->
            [ { st | goals = { b | gammas = b.gammas ++ [ { id = id, f = f, uses = 0 } ] } :: rest } ]

        _ ->
            [ { st | goals = { b | easy = b.easy ++ [ ( id, f ) ] } :: rest } ]


freshVar : Ctx -> State -> Variable -> ( Variable, State )
freshVar ctx st ( name, _, _ ) =
    let
        go n =
            if Set.member ( name, [ n ], 0 ) ctx.usedVars then
                go (n + 1)

            else
                n

        n1 =
            go (1 + Maybe.withDefault 0 (Dict.get name st.names))
    in
    ( ( name, [ n1 ], 0 ), { st | names = Dict.insert name n1 st.names, vars = Set.insert ( name, [ n1 ], 0 ) st.vars } )


skolemTerm : Ctx -> State -> List Variable -> ( Term, State )
skolemTerm ctx st args =
    let
        go name n =
            if Set.member ( name, [ n ] ) ctx.usedIdents then
                go name (n + 1)

            else
                n
    in
    if List.isEmpty args then
        let
            n =
                go "c" (st.cs + 1)
        in
        ( Func ( "c", [ n ] ) [], { st | cs = n } )

    else
        let
            n =
                go "ş" (st.sk + 1)
        in
        ( Func ( "ş", [ n ] ) (List.map Var args), { st | sk = n } )


expand : Ctx -> State -> Branch -> List Branch -> Expansion
expand ctx st b rest =
    let
        fits =
            b.depth < ctx.depth

        new items =
            List.filter (\( g, _, _ ) -> not (List.member g b.forms)) items
    in
    case b.easy of
        ( id, f ) :: more ->
            let
                b1 =
                    { b | easy = more }

                items =
                    case classify f of
                        KDN g ->
                            ( new [ ( g, DoubleNeg, Dict.empty ) ], st )

                        KAlpha g h ->
                            ( new [ ( g, Alpha 1, Dict.empty ), ( h, Alpha 2, Dict.empty ) ], st )

                        KDelta x g ->
                            let
                                args =
                                    List.filter (\v -> Set.member v st.vars) (FOL_SS.ffolFreeVars f)

                                ( t, st1 ) =
                                    skolemTerm ctx st args
                            in
                            ( [ ( FOL_SS.ffolApplySubstitution (Dict.singleton x t) g, Delta, Dict.singleton x t ) ], st1 )

                        _ ->
                            ( [], st )
            in
            case items of
                ( [], _ ) ->
                    Expanded { st | goals = b1 :: rest }

                ( xs, st1 ) ->
                    if fits then
                        let
                            ( st2, b2 ) =
                                extend st1 b1 id xs
                        in
                        Expanded { st2 | goals = b2 :: rest }

                    else
                        BlockedByDepth

        [] ->
            case pickBeta st b of
                Just ( ( id, f ), more ) ->
                    case classify f of
                        KBeta g h ->
                            if List.member g b.forms || List.member h b.forms then
                                -- the branch already satisfies the β formula
                                Expanded { st | goals = { b | betas = more } :: rest }

                            else if fits then
                                let
                                    ( st1, n1 ) =
                                        addNode st b.last g (Beta 1) [ id ] Dict.empty

                                    ( st2, n2 ) =
                                        addNode st1 b.last h (Beta 2) [ id ] Dict.empty

                                    child n g1 =
                                        { b | betas = more, last = n, depth = b.depth + 1, incoming = [ ( n, g1 ) ], forms = g1 :: b.forms, checked = st.version }
                                in
                                Expanded { st2 | goals = child n1 g :: child n2 h :: rest }

                            else
                                BlockedByDepth

                        _ ->
                            Expanded { st | goals = { b | betas = more } :: rest }

                Nothing ->
                    case LE.minimumBy .uses (List.filter (\g -> g.uses < ctx.k) b.gammas) of
                        Nothing ->
                            if List.isEmpty b.gammas then
                                Finished

                            else
                                BlockedByGamma

                        Just gam ->
                            if fits then
                                case classify gam.f of
                                    KGamma x g ->
                                        if not (FOL_SS.ffolHasFreeInstanceOfVar g x) then
                                            -- a vacuous quantifier: g is its only instance
                                            let
                                                b0 =
                                                    { b | gammas = List.filter (\g1 -> g1.id /= gam.id) b.gammas }
                                            in
                                            if List.member g b.forms then
                                                Expanded { st | goals = b0 :: rest }

                                            else
                                                let
                                                    ( st2, b2 ) =
                                                        extend st b0 gam.id [ ( g, Gamma, Dict.empty ) ]
                                                in
                                                Expanded { st2 | goals = b2 :: rest }

                                        else
                                            let
                                                ( v, st1 ) =
                                                    freshVar ctx st x

                                                s =
                                                    Dict.singleton x (Var v)

                                                b1 =
                                                    { b
                                                        | vset = Set.insert v b.vset
                                                        , gammas =
                                                            List.map
                                                                (\g1 ->
                                                                    if g1.id == gam.id then
                                                                        { g1 | uses = g1.uses + 1 }

                                                                    else
                                                                        g1
                                                                )
                                                                b.gammas
                                                    }

                                                ( st2, b2 ) =
                                                    extend st1 b1 gam.id [ ( FOL_SS.ffolApplySubstitution s g, Gamma, s ) ]
                                            in
                                            Expanded { st2 | goals = b2 :: rest }

                                    _ ->
                                        Expanded { st | goals = { b | gammas = List.filter (\g1 -> g1.id /= gam.id) b.gammas } :: rest }

                            else
                                BlockedByDepth


-- The next β formula: the first one with a component that closes its branch at once, if any (so that the
-- tableau branches less), or else the oldest one.


pickBeta : State -> Branch -> Maybe ( ( Int, FormulaFOL ), List ( Int, FormulaFOL ) )
pickBeta st b =
    let
        lits =
            List.map (\m -> ( m.pos, applyF st.sigma m.atom )) b.lits

        closesAtOnce g =
            case classify g of
                KClose ->
                    True

                KLit pos atom ->
                    let
                        sa =
                            applyF st.sigma atom
                    in
                    List.any
                        (\( p, a ) ->
                            p
                                /= pos
                                && (a
                                        == sa
                                        || (case ( a, sa ) of
                                                ( Equal t1 t2, Equal u1 u2 ) ->
                                                    t1 == u2 && t2 == u1

                                                _ ->
                                                    False
                                           )
                                   )
                        )
                        lits
                        || (case ( pos, sa ) of
                                ( False, Equal t1 t2 ) ->
                                    t1 == t2

                                _ ->
                                    False
                           )

                _ ->
                    False

        good ( _, f ) =
            case classify f of
                KBeta g h ->
                    closesAtOnce g || closesAtOnce h

                _ ->
                    False
    in
    case LE.findIndex good b.betas of
        Just i ->
            Maybe.map (\x -> ( x, LE.removeAt i b.betas )) (LE.getAt i b.betas)

        Nothing ->
            case b.betas of
                x :: more ->
                    Just ( x, more )

                [] ->
                    Nothing


fail : Search -> Bool -> Search
fail s byGamma =
    let
        score =
            ( s.st.closed, Dict.size s.st.nodes )

        better =
            case s.best of
                Nothing ->
                    True

                Just ( sc, _ ) ->
                    score > sc
    in
    { s
        | gammaHit = s.gammaHit || byGamma
        , depthHit = s.depthHit || not byGamma
        , best =
            if better then
                Just ( score, s.st )

            else
                s.best
    }


backtrack : Search -> Step
backtrack s =
    case s.choices of
        c :: cs ->
            Continue { s | st = c, choices = cs, steps = s.steps + 1 }

        [] ->
            Done (Exhausted s)


step : Ctx -> Search -> Step
step ctx s =
    if s.steps >= ctx.maxSteps then
        Done (OutOfSteps s)

    else
        let
            st =
                s.st
        in
        case st.goals of
            [] ->
                Done (Refuted s)

            b :: rest ->
                if b.checked < st.version then
                    case quickClosure st b of
                        Just from ->
                            Continue { s | st = closeBranch st b rest from Dict.empty, steps = s.steps + 1 }

                        Nothing ->
                            Continue { s | st = { st | goals = { b | checked = st.version } :: rest } }

                else
                    case b.incoming of
                        ( id, f ) :: more ->
                            case processIncoming st { b | incoming = more } rest id f of
                                first :: others ->
                                    Continue { s | st = first, choices = others ++ s.choices, steps = s.steps + 1 }

                                [] ->
                                    backtrack s

                        [] ->
                            case expand ctx st b rest of
                                Expanded st2 ->
                                    Continue { s | st = st2, steps = s.steps + 1 }

                                Finished ->
                                    Done (FoundOpen s)

                                BlockedByGamma ->
                                    backtrack (fail s True)

                                BlockedByDepth ->
                                    backtrack (fail s False)


loop : Ctx -> Search -> Outcome
loop ctx s =
    case step ctx s of
        Continue s2 ->
            loop ctx s2

        Done o ->
            o



--====================--
--   ENTRY POINTS     --
--====================--


initState : SetFOL -> State
initState fs =
    let
        nodes =
            Dict.fromList <| List.indexedMap (\i f -> ( i, { parent = i - 1, f = f, rule = Premise, from = [], subs = Dict.empty } )) fs

        n =
            List.length fs
    in
    { goals =
        [ { last = n - 1
          , depth = 0
          , incoming = List.indexedMap Tuple.pair fs
          , easy = []
          , betas = []
          , gammas = []
          , lits = []
          , forms = fs
          , vset = Set.empty
          , checked = 0
          }
        ]
    , sigma = Dict.empty
    , vars = Set.empty
    , nodes = nodes
    , next = n
    , names = Dict.empty
    , sk = 0
    , cs = 0
    , version = 0
    , closed = 0
    }


{-| It builds a free-variable tableau of a set of formulas, with `defaultLimits` except for the maximum number of
uses of each γ formula in a branch and the maximum number of rule applications in a branch, which are given:
`semanticTableauFV fs maxGammaUses maxDepth`.
-}
semanticTableauFV : SetFOL -> Int -> Int -> FVTableau
semanticTableauFV fs uMax dMax =
    semanticTableauFVWith { defaultLimits | gammaUses = uMax, depth = dMax } fs


{-| It builds a free-variable tableau of a set of formulas with the given limits.
-}
semanticTableauFVWith : FVLimits -> SetFOL -> FVTableau
semanticTableauFVWith limits fs =
    let
        depthLimit =
            clamp 0 250 limits.depth

        ctx0 =
            { k = 1
            , depth = depthLimit
            , maxSteps = limits.steps
            , usedVars = Set.fromList <| List.concatMap FOL_SS.ffolVarSymbols fs
            , usedIdents = Set.fromList <| List.concatMap (\f -> FOL_SS.ffolConstSymbols f ++ FOL_SS.ffolFuncSymbols f) fs
            }

        st0 =
            initState fs

        maxK =
            max 1 limits.gammaUses

        unknown s byGamma byDepth bySteps =
            let
                -- the state of the search that closed most branches
                st =
                    case s.best of
                        Just ( sc, b ) ->
                            if bySteps && ( s.st.closed, Dict.size s.st.nodes ) > sc then
                                s.st

                            else
                                b

                        Nothing ->
                            s.st
            in
            ( st, LimitLeaf, Unknown { gammaUses = byGamma, depth = byDepth, steps = bySteps, equality = False } )

        run k steps0 =
            let
                ctx =
                    { ctx0 | k = k }
            in
            case loop ctx { st = st0, choices = [], steps = steps0, gammaHit = False, depthHit = False, best = Nothing } of
                Refuted s ->
                    ( ( s.st, OpenLeaf, Closed ), k, s.steps )

                FoundOpen s ->
                    let
                        withEquality =
                            case s.st.goals of
                                b :: _ ->
                                    List.any
                                        (\m ->
                                            case ( m.pos, m.atom ) of
                                                ( True, Equal t1 t2 ) ->
                                                    t1 /= t2

                                                _ ->
                                                    False
                                        )
                                        b.lits

                                [] ->
                                    False
                    in
                    if withEquality then
                        ( ( s.st, OpenLeaf, Unknown { gammaUses = False, depth = False, steps = False, equality = True } ), k, s.steps )

                    else
                        ( ( s.st, OpenLeaf, Open ), k, s.steps )

                Exhausted s ->
                    if s.gammaHit && k < maxK then
                        run (k + 1) s.steps

                    else
                        ( unknown s s.gammaHit s.depthHit False, k, s.steps )

                OutOfSteps s ->
                    ( unknown s False False True, k, s.steps )

        ( ( stF, firstLeaf, result ), kF, stepsF ) =
            run 1 0
    in
    { tree = buildTree stF firstLeaf
    , result = result
    , substitution = stF.sigma
    , gammaUses = kF
    , depth = depthLimit
    , steps = stepsF
    }


{-| It says if the tableau is closed, that is, if it proves that the set of formulas is unsatisfiable.
-}
semanticTableauFVIsClosed : FVTableau -> Bool
semanticTableauFVIsClosed t =
    t.result == Closed



--====================--
--   THE TREE         --
--====================--


isFormulaRule : FVRule -> Bool
isFormulaRule r =
    case r of
        Closure ->
            False

        OpenLeaf ->
            False

        LimitLeaf ->
            False

        Unexplored ->
            False

        _ ->
            True


buildTree : State -> FVRule -> Tree FVNode
buildTree st firstLeaf =
    let
        -- leaves for the branches that are not closed: the first one is open or was stopped by the limits
        ( nodes, _ ) =
            List.foldl
                (\( j, b ) ( d, n ) ->
                    ( Dict.insert n
                        { parent = b.last
                        , f = Insat
                        , rule =
                            if j == 0 then
                                firstLeaf

                            else
                                Unexplored
                        , from = []
                        , subs = Dict.empty
                        }
                        d
                    , n + 1
                    )
                )
                ( st.nodes, st.next )
                (List.indexedMap Tuple.pair st.goals)

        children =
            Dict.foldr (\id r d -> Dict.update r.parent (\l -> Just (id :: Maybe.withDefault [] l)) d) Dict.empty nodes

        kids id =
            Maybe.withDefault [] (Dict.get id children)

        -- the number of a formula node is its depth in the branch
        number depth id d =
            case Dict.get id nodes of
                Just r ->
                    if isFormulaRule r.rule then
                        List.foldl (number (depth + 1)) (Dict.insert id (depth + 1) d) (kids id)

                    else
                        List.foldl (number depth) d (kids id)

                Nothing ->
                    d

        nums =
            List.foldl (number 0) Dict.empty (kids -1)

        num id =
            Maybe.withDefault 0 (Dict.get id nums)

        build id =
            case Dict.get id nodes of
                Just r ->
                    GTree.inner { i = num id, f = r.f, rule = r.rule, from = List.map num r.from, subs = r.subs } (List.map build (kids id))

                Nothing ->
                    GTree.empty
    in
    case kids -1 of
        root :: _ ->
            build root

        [] ->
            GTree.leaf { i = 0, f = Taut, rule = OpenLeaf, from = [], subs = Dict.empty }



--====================--
--   REPRESENTATION   --
--====================--


nodeLabel : FVNode -> String
nodeLabel n =
    case n.rule of
        Closure ->
            TD.closedMark

        OpenLeaf ->
            TD.openMark

        LimitLeaf ->
            TD.undecidedMark

        Unexplored ->
            TD.unexploredMark

        _ ->
            TD.numbered n.i n.f


ruleLabel : FVNode -> String
ruleLabel n =
    let
        froms =
            List.map String.fromInt n.from
    in
    case n.rule of
        DoubleNeg ->
            TD.rule "¬¬" froms ""

        Alpha _ ->
            TD.rule "α" froms ""

        Beta _ ->
            TD.rule "β" froms ""

        Gamma ->
            TD.rule "γ" froms (TD.substitution n.subs)

        Delta ->
            TD.rule "δ" froms (TD.substitution n.subs)

        Closure ->
            TD.rule "⊥" froms (TD.substitution n.subs)

        _ ->
            ""


toDTrees : Tree FVNode -> List DTree
toDTrees tree =
    case GTree.root tree of
        Just ( n, ch ) ->
            [ DTree { node = nodeLabel n, edge = ruleLabel n } (List.concatMap toDTrees ch) ]

        Nothing ->
            []


times : Int -> String
times n =
    if n == 1 then
        "once"

    else
        String.fromInt n ++ " times"


{-| A sentence that explains the answer.
-}
semanticTableauFVSummary : FVTableau -> String
semanticTableauFVSummary t =
    case t.result of
        Closed ->
            "Closed tableau (each γ formula used at most "
                ++ times t.gammaUses
                ++ " in a branch): the set is unsatisfiable"
                ++ (if Dict.isEmpty t.substitution then
                        "."

                    else
                        ". σ = " ++ FOL_SS.substitutionToString t.substitution
                   )

        Open ->
            "Open branch, fully expanded and without γ formulas: the set is satisfiable."

        Unknown u ->
            if u.equality then
                "Open branch with equalities: this tableau does not use the equality axioms, so it does not decide."

            else if u.steps then
                "No closed tableau found within the limit of steps of the search."

            else
                "No closed tableau found with "
                    ++ String.join " and "
                        ((if u.gammaUses then
                            [ "each γ formula used at most " ++ times t.gammaUses ++ " in a branch" ]

                          else
                            []
                         )
                            ++ (if u.depth then
                                    [ "at most " ++ String.fromInt t.depth ++ " rules in a branch" ]

                                else
                                    []
                               )
                        )
                    ++ "."


{-| It represents the tableau as a string: a node per line, indented by its depth, with the rule that produced it,
and the answer at the end. Each formula is numbered by its depth in the branch: `5. ¬P(x₁)   % β(4)`.
-}
semanticTableauFVToString : FVTableau -> String
semanticTableauFVToString t =
    TD.toText (toDTrees t.tree) ++ "\n" ++ semanticTableauFVSummary t


{-| It represents the tableau as a DOT graph (GraphViz). The first node is the summary of the answer. Each formula
is numbered by its depth in the branch, and the edges show the rules: `α(4)`, `β(4)`, `γ(1){x/x₁}`,
`δ(3){y/ş₁(x₁)}`, `¬¬(2)`; a closed branch ends in `✕`, and the edge `⊥(3,6){x₁/a}` names the two formulas that
close it and the bindings of the free variables that the closure makes. An open branch ends in `◯`, one stopped by
the limits in `ⓤ` and one not explored in `…`.
-}
semanticTableauFVToDOT : FVTableau -> String
semanticTableauFVToDOT t =
    TD.toDOT ("  summary [label=" ++ JSONE.encode 0 (JSONE.string (semanticTableauFVSummary t)) ++ "];") (toDTrees t.tree)
