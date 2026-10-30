# Changelog

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
