# Recursive inner-product protocol and replay

`Examples/InnerProduct/Protocol.lean` specifies the binary specialization of
the recursive protocol in Bootle–Cerulli–Chaidos–Groth–Petit, EUROCRYPT 2016,
§4.2. It uses additive group notation and nonzero field challenges. At depth
`r` its recursively indexed vectors have `2^(r+1)` coordinates; terminal
witnesses have two coordinates.

The six fields of `FoldMessage` are the coefficients with indices −1 and +1
for each of the source paper's `A`, `B`, and `z` expressions. The index-zero
coefficients are the current statement. `accepts` folds the statement along
the transcript and checks the final openings and inner product.

## Execution and observation

`Replay.lean` represents the causal prover, after fixing its private seed, as
an actual `OracleComp` program whose remaining requests are public challenges.
It proves source-path reconstruction, transcript output, and exact public-query
counts for arbitrary depth. `replay33` records nine prescribed paths through
one two-round prover. It does not search for accepting paths or enforce
distinct challenges.

`Interaction.lean` gives the same protocol a role-decorated `TypeTree`, a
prover strategy, and a public-coin verifier. `publicVerifier_replay` proves
that replaying the verifier on a recorded transcript computes `accepts`
without sampling challenges again. A theorem identifying the entire paired
two-party runner with the source oracle execution is not included.

The independent model in `VCVioTest/InnerProduct/PlainReplay.lean` has no
imports. `PlainProtocol.lean` shares only the mathematical protocol definitions.
`Comparison.run_eq` proves equality under arbitrary monadic challenge handlers.
Its corollaries cover native measures, joint state observations, and a private
seed sampled once before an adaptive consumer. They use one common consumer;
they do not assume that consumer has an extraction or termination guarantee.

## Security boundary

These modules do not establish completeness for the whole family, accepting-tree
generation, special soundness, the generalized extractor's success or expected
work, a DLog reduction, or Fiat–Shamir security. Public-query counts exclude the
prover's private computation and group arithmetic. The concrete checks exercise
folding arithmetic, depths zero through three, and costs retained after failed
attempts. They do not replace general security proofs.

The source theorem's extraction endpoint is a valid witness **or** a nontrivial
discrete-log relation. An unconditional witness-only assertion would require
additional computational reasoning and an explicit key-generation experiment.

Source: [EUROCRYPT 2016 paper, §4](https://www.iacr.org/archive/eurocrypt2016/96650200/96650200.pdf).
