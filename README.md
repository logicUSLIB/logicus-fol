# LogicUS.FOL

## Design Goals

This package has been created to work with computer logic, specifically with First Order Logic. For a series of types and functions have been created that allow the definition and interpretation of formulas as well as the application of the main algorithms to reduce the consistency of formulas and sets.

## Overview

The _LogicUS.FOL_ packages allow working with formulas and sets in First Order Logic. It includes aspects like L-Structures valuation, substitution performing, normal forms, clauses and other algorithms like Semantic Tableaux, Herbrand Works or Resolution. Next, we make a synopsis of each of the modules exposed:

- **_LogicUS.FOL.SintaxSemantics_**:
  It constitutes the basis of first logic, so that it exposes the syntax for the definition of the formulas and substituions (including all the operations with it, like clausre, variable renaming, ...) as well as the semantics for the L-Structure and its evaluation.

- **_LogicUS.FOL.SemanticTableaux_**: It develops all the necessary tools for working with semantic boards in FOL, distinguishing the different types of formulas and rules and also allowing the visualization of the complete board.

- **_LogicUS.FOL.NormalForms_**: It contains the functions necessary for the transformation of formulas into normal forms: Prenex, Skolem, NNF, CNF, DNF.

- **_LogicUS.FOL.Clauses_**: It provides some functions that allow work with first order clauses, definition, operations, transformation of formulas and sets into clausal sets, ...

- **_LogicUS.FOL.Herbrand_**: It defines the functions necessary for the application of the Herbrand Works (Universe, interpretations, models, ...)

- **_LogicUS.FOL.Unification_**: It provides the functions for working with the unification algorithms: terms and atoms MGU.

- **_LogicUS.FOL.Resolution_**: It gives the functions for working with the resolution algorithm in FOL and its representation, with several strategies (shortest clause first, linear, positive, negative).

- **_LogicUS.FOL.SemanticTableauxEQ_**: Semantic tableaux for first order logic with equality.

- **_LogicUS.FOL.SemanticTableauxFV_**: Semantic tableaux with free variables: the universal formulas are instantiated with new variables, which get their values by unification when a branch is closed, and the search backtracks over the ways of closing the branches. It finds closed tableaux that the ground tableaux of _SemanticTableaux_ only find with the right terms, and the tree shows each variable and the substitution that closes each branch.

- **_LogicUS.FOL.Deduction_** and **_LogicUS.FOL.DeductionSystems_**: Deduction systems for first-order logic given by their rules, written as schemas (`rule ∀I : A[x/a] ⊢ ∀x A  if a fresh`, `rule =E : t = s, A[x/t] ⊢ A[x/s]`, `axiom A4 : ∀x A → A[x/t]`), so that each exercise says which rules can be used. They extend `LogicUS.PL.Deduction` (logicus-pl), whose rules of the connectives they use, with quantifiers, substitutions without capture, side conditions and equality. Proofs in the style of Fitch are checked line by line, with an explanation of each error, and the module gives the rules that can be used at the end of a proof: forward from the lines, closing the current subproof, or backward from the goal. The presets are natural deduction (classical, intuitionistic, with derived rules) and an axiomatic system.

- **_LogicUS.FOL.Prover9Mace4_** and **_LogicUS.FOL.TPTP_**: For problems too big for the didactic algorithms, they translate a problem to the input of external provers ([Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/), and any prover that reads [TPTP](https://www.tptp.org), such as [E](https://eprover.org)) and read their answers back. Mace4 models are returned as L-structures, so they can be checked and shown with the rest of the library. Running the provers is up to the application.

## Tests

`tests/` contains semantic tests that compare the algorithms with a reference implementation on small finite structures. Run them with `npx elm-test`.

You can access to the installation guide, theoretical and practical contents, and more at [LogicUS](https://ramgonvictor.wixsite.com/logicus).
