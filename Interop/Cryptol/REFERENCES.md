# References

### CRYPTOL360 — Cryptol syntax and reference semantics

Galois, Inc. *Cryptol 3.6.0*.
[Release](https://github.com/GaloisInc/cryptol/releases/tag/3.6.0),
[syntax PDF](https://github.com/GaloisInc/cryptol/blob/3.6.0/docs/Syntax.pdf),
[semantics PDF](https://github.com/GaloisInc/cryptol/blob/3.6.0/docs/Semantics.pdf),
[reference evaluator source](https://github.com/GaloisInc/cryptol/blob/3.6.0/src/Cryptol/Eval/Reference.lhs),
[resolved typed AST](https://github.com/GaloisInc/cryptol/blob/3.6.0/src/Cryptol/TypeCheck/AST.hs).

The semantics document describes lifted value CPOs, suspended product and
sequence components, continuous functions, and recursive declaration groups.
The optional model implements and proves adequacy for a selected resolved
fragment. Its external tests distinguish the reference evaluator from the
normal evaluator, including their negative-integer division discrepancy.

Used in: `Model/`, [model guide](docs/model.md).

The partial numeric functions and their differential cases follow
[`TypeCheck/Solver/InfNat.hs`](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/src/Cryptol/TypeCheck/Solver/InfNat.hs).
Closed structural and literal constraints follow
[`TypeCheck/Solver/Class.hs`](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/src/Cryptol/TypeCheck/Solver/Class.hs).
The broader source graph includes the actual polynomial and fold/scan bodies in
[`lib/Cryptol/Reference.cry`](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/lib/Cryptol/Reference.cry).
The [exporter guide](exporter/README.md) distinguishes these provenance and
executable checks from semantic correspondence proofs.
