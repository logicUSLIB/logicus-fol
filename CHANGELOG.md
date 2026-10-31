# Changelog

## 3.2.2

### Changed

- The free variables of the input formulas are universally quantified in the three semantic tableaux:
  `SemanticTableaux` and `SemanticTableauxFV` treated them as constants, while `SemanticTableauxEQ` (and resolution)
  closed them universally. `{P(x), ¬P(a)}` is now refuted by the three. The tableaux start from the universal
  closures, and closed formulas are shown as they were given (`SemanticTableauxEQ` no longer renames their bound
  variables apart, which showed `x¹`, `y²`...).
- `ffolToString` writes `¬(s = t)` as `(s ≠ t)` instead of `(s != t)`, and `ffolToMathString` as `s \neq t`.

## 3.2.1

### Changed

- The three semantic tableaux (`SemanticTableaux`, `SemanticTableauxEQ`, `SemanticTableauxFV`) show their trees in
  the same way, as text, DOT and (`SemanticTableauxEQ`) JSON:
  - each formula is numbered by its depth in the branch, and the number is shown in the node: `5. ¬P(a)` (the two
    components of a β rule have the same number);
  - the edges show the rule and the numbers of its premises: `α(4)`, `β(4)`, `γ(1){x/a}`, `δ(3){x/c₁}`, `¬¬(2)`,
    and in the equality tableau the equalities used by Leibniz law: `α(9).𝓛𝓛8`, `𝓛𝓛8(5)`;
  - a closed branch ends in `✕`, with the edge `⊥(3,6)` (the contradictory formulas); an open branch in `◯`, a
    branch stopped by the limits in `ⓤ` and a branch not explored in `…`. These symbols are in common fonts (`🗴`
    and `⭘` were shown as empty boxes in some browsers).
  - the text form has a node per line, with its rule aligned on the right; the branches of a β rule are indented.
- The equality tableau names its new constants `c₁`, `c₂`, ... (the first ones not used by the input) instead of
  `κ₀`, `κ₁`, ..., like the other two tableaux.

### Fixed

- `SemanticTableaux`: the label of a δ rule gave an internal key instead of the number of its formula.

## 3.2.0

### Added

- `LogicUS.FOL.SemanticTableauxFV`: semantic tableaux with free variables. A γ formula is instantiated with a new
  variable, a δ formula with a Skolem term on the free variables of the formula (the δ⁺ rule), and two literals
  close a branch when their atoms unify; the unifier applies to every branch, and the search backtracks over the
  ways of closing them. The number of uses of each γ formula in a branch grows up to a limit (iterative deepening).
  The answer is `Closed` (unsatisfiable), `Open` (a fully expanded open branch without γ formulas: satisfiable) or
  `Unknown`, and the tree (as text or DOT) shows the variables and the bindings made by each closure. It closes 26
  of the Pelletier problems 18–46 (all but 34, 38 and 43) in a few milliseconds each; the ground tableau of
  `SemanticTableaux` closes 16 of them with its usual limits.

### Changed

- `SemanticTableaux.semanticTableau` is up to twice as fast on large tableaux: each step only compares the new nodes
  with the branch, instead of every pair of nodes. The tableaux are the same as before.

## 3.1.1

### Fixed

- `ffolToSkolem` (and so `ffolToNNF`, `ffolToCNF`, `ffolToClauses`) did not rename variables apart in prenex formulas:
  in `∃x∀x P(x)` the Skolem constant of the outer `x` replaced the inner one.
- `SemanticTableauxEQ` could overflow the call stack (in browsers and in `elm-test`) on long branches; branches longer
  than 150 nodes are now left undecided (never counted as closed).

## 3.1.0

Correctness fixes found by a new suite of semantic tests (`tests/`), which compares the algorithms with a reference
implementation evaluated on small finite structures, and new support for external provers.

### Fixed

- `SemanticTableaux.semanticTableauIsInsat` reported a tableau as closed when a branch had only been cut by the depth
  limits: `∀x P(x)` was "refuted".
- `SemanticTableauxEQ`: when the universe was empty, the γ rule took the constant `κ₀` without registering it, and the
  δ rule then reused it as a "new" constant: `{∀x ¬P(x), ∀y ∃x x ≠ y}` (satisfiable) was refuted.
- First order resolution (all strategies) did not terminate on many satisfiable sets, even without function symbols:
  `cfolSubsumes` was plain inclusion, so renamed variants of a clause were never discarded. It is now θ-subsumption.
- First order resolution had no factoring, so some unsatisfiable sets could not be refuted
  (e.g. `{P(x), P(y)}, {¬P(u), ¬P(v)}`). Binary factoring is now an inference of every strategy.
- Shortest-clause-first resolution did not resolve a clause with itself.
- `csfolSCFLinearResolution` only tried the first clause as top clause, and explored every branch even after finding a
  refutation.
- An input containing the empty clause was reported satisfiable by the resolution functions.
- ⊤ inside a clause produced the empty clause in `csfolFromCNF`, `ffolToClauses` and `sfolToClauses`
  (`⊤ ∨ ⊤` became `□`).
- `sfolToSkolem` did not apply the preprocessing of `ffolToSkolem` and left quantifiers under `↔` and `¬`.
- `ffolToInputString` wrote variables inside function arguments in display syntax (`P(f(x))`), which reads back as a
  constant.
- Parser error messages no longer show internal Elm values.

### Changed

- Resolution is a semi-decision procedure: on a satisfiable set it may never stop, even without function symbols. The
  strategies are now bounded (300 processed clauses, 100 steps for linear resolution, resolvents of at most 8
  literals), so they always return; `False` means "not refuted within the bounds".
- Requires `logicUSLIB/logicus-pl` 4.1.0 or later (3.0.0 still required 1.x, so it could not be combined with
  recent versions of logicus-pl).

### Added

- `LogicUS.FOL.Prover9Mace4`: input files for Prover9/Mace4 with readable names, `prover9Result`, and `mace4Models`
  (Mace4 models as `L_Structure Int`).
- `LogicUS.FOL.TPTP`: TPTP (FOF) problems for E, Vampire and other provers, and `szsStatus`.
- `LogicUS.FOL.ToStringP9M4` is now exposed (deprecated in favour of `Prover9Mace4`).
