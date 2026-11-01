module LogicUS.FOL.DeductionSystems exposing
    ( Preset, presets, presetSystem
    , naturalDeduction, quantifierRules, equalityRules, derivedRules, axiomatic
    )

{-| Deduction systems for first-order logic ready to use with `LogicUS.FOL.Deduction`, as text that can be edited:
rules can be removed, renamed or added before reading it with `readSystem`. The rules of the connectives are those of
`LogicUS.PL.DeductionSystems` (package logicus-pl).


# Presets

@docs Preset, presets, presetSystem


# Rules

@docs naturalDeduction, quantifierRules, equalityRules, derivedRules, axiomatic

-}

import LogicUS.FOL.Deduction as D exposing (System)
import LogicUS.PL.DeductionSystems as PLDS


{-| A system with a name and a short description.
-}
type alias Preset =
    { name : String
    , description : String
    , rules : String
    }


{-| The rules of the quantifiers. In ∀I and ∃E the term `a` must be new (a variable or a constant that does not
occur in the open assumptions nor in the conclusion).
-}
quantifierRules : String
quantifierRules =
    String.join "\n"
        [ "rule ∀I : A[x/a] ⊢ ∀x A   if a fresh"
        , "rule ∀E : ∀x A ⊢ A[x/t]"
        , "rule ∃I : A[x/t] ⊢ ∃x A"
        , "rule ∃E : ∃x A, [A[x/a]] B ⊢ B   if a fresh"
        ]


{-| Reflexivity and Leibniz law (substitution of equals).
-}
equalityRules : String
equalityRules =
    String.join "\n"
        [ "axiom =I : t = t"
        , "rule =E : t = s, A[x/t] ⊢ A[x/s]"
        ]


{-| Classical natural deduction for first-order logic with equality: the rules of the connectives (intuitionistic
and classical), and those of the quantifiers and of equality.
-}
naturalDeduction : String
naturalDeduction =
    String.join "\n\n" [ PLDS.naturalDeduction, quantifierRules, equalityRules ]


{-| Rules that can be derived from the others, for exercises that allow them: those of `LogicUS.PL.DeductionSystems`
(MT, DS, HS, ¬¬I, LEM, De Morgan laws) and the negation of the quantifiers.
-}
derivedRules : String
derivedRules =
    String.join "\n"
        [ PLDS.derivedRules
        , "rule ¬∀ : ¬∀x A ⊢ ∃x ¬A"
        , "rule ¬∃ : ¬∃x A ⊢ ∀x ¬A"
        ]


{-| The axiomatic system of `LogicUS.PL.DeductionSystems` extended to first-order logic: two axiom schemes of the
universal quantifier and the generalization rule.
-}
axiomatic : String
axiomatic =
    String.join "\n"
        [ PLDS.axiomatic
        , "axiom A4 : ∀x A → A[x/t]"
        , "axiom A5 : ∀x (A → B) → (A → ∀x B)   if x not free in A"
        , "rule Gen : A ⊢ ∀x A"
        ]


{-| The systems of this module. They have the same names as their propositional versions in
`LogicUS.PL.DeductionSystems`.
-}
presets : List Preset
presets =
    [ { name = "Natural deduction (classical)", description = "Introduction and elimination rules of the connectives, quantifiers and equality, ¬¬E and RAA", rules = naturalDeduction }
    , { name = "Natural deduction (intuitionistic)", description = "Without ¬¬E and RAA", rules = String.join "\n\n" [ PLDS.intuitionisticRules, quantifierRules, equalityRules ] }
    , { name = "Natural deduction with derived rules", description = "Classical natural deduction plus MT, DS, HS, ¬¬I, LEM, De Morgan laws and the negation of the quantifiers", rules = String.join "\n\n" [ naturalDeduction, derivedRules ] }
    , { name = "Axiomatic system", description = "A1-A5, modus ponens and generalization", rules = axiomatic }
    ]


{-| The system of a preset, by name.
-}
presetSystem : String -> Maybe System
presetSystem name =
    presets
        |> List.filter (\p -> p.name == name)
        |> List.head
        |> Maybe.andThen (\p -> Result.toMaybe (D.readSystem p.rules))
