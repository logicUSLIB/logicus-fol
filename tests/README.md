# Tests

Semantic tests: the algorithms are compared with a reference implementation written independently of the library
(`FOLOracle.elm`), on random formulas and random finite structures of 1 to 3 elements. Transformations that add
Skolem functions are checked in both directions (a model of the result is a model of the input; a model of the input
expands to a model of the result). `FOLRegressionTests.elm` keeps one test per bug found. `FOLTableauxFVTests.elm`
checks the free-variable tableaux: a closed tableau has no model, every open branch defines a model (built from its
literals), propositional sets are decided exactly, and the Pelletier problems 18–46 (but 34, 38 and 43) are closed.

Run them with [elm-test](https://github.com/rtfeldman/node-test-runner) (the resolution tests take a few minutes):

    npx elm-test
