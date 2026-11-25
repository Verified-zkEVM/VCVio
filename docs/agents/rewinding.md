# Rewinding

The rewinding framework in
[`VCVio/CryptoFoundations/Rewinding/`](../../VCVio/CryptoFoundations/Rewinding/) runs a black-box
algorithm against complete reruns of a prover whose private randomness and oracle answers stay
frozen across the reruns. It has three layers:

1. A **reset policy** says what stays frozen between reruns.
2. A **finder** searches for accepting challenges and sees only the verdicts of complete runs.
3. The **bridge and recovery** theorems carry the finder's success and cost guarantees to frozen
   reruns, and hand the transcripts of the runs it saw to a witness extractor.

[forking.md](forking.md) covers the forking lemmas and compares the two finders in the library.

## Map

| Layer | Main names | File |
|---|---|---|
| Reset policy | `Rewinding.ResetPolicy`, `Rewinding.ResetPolicy.attempt` | [`Basic.lean`](../../VCVio/CryptoFoundations/Rewinding/Basic.lean), [`Laws.lean`](../../VCVio/CryptoFoundations/Rewinding/Laws.lean) |
| Policies | `Rewinding.fixedTape`, `Rewinding.ResetPolicy.ofRandomOracle`, `Rewinding.ResetPolicy.product` | [`FixedTape.lean`](../../VCVio/CryptoFoundations/Rewinding/FixedTape.lean), [`Instances.lean`](../../VCVio/CryptoFoundations/Rewinding/Instances.lean) |
| Eager table | `Rewinding.ResetPolicy.eagerTable`, `Rewinding.ResetPolicy.attempt_eagerTable` | [`Eager.lean`](../../VCVio/CryptoFoundations/Rewinding/Eager.lean) |
| Finder contract | `Rewinding.IsFinder`, `Rewinding.IsTreeFinder` | [`Finder.lean`](../../VCVio/CryptoFoundations/Rewinding/Finder.lean) |
| Finders | `Rewinding.isTreeFinder_thresholdFinder`, `OracleComp.isFinder_coordFinder`, `OracleComp.isFinder_blockFinder` | [`ThresholdFinder.lean`](../../VCVio/CryptoFoundations/Rewinding/ThresholdFinder.lean), [`CoordinateFork/Finder.lean`](../../VCVio/CryptoFoundations/CoordinateFork/Finder.lean), [`CoordinateFork/BlockFinder.lean`](../../VCVio/CryptoFoundations/CoordinateFork/BlockFinder.lean) |
| Rounds | `Rewinding.thresholdChildren`, `Rewinding.blockChildren`, `Rewinding.thresholdChildren_eq_blockChildren` | [`ThresholdRound.lean`](../../VCVio/CryptoFoundations/Rewinding/ThresholdRound.lean), [`BlockRound.lean`](../../VCVio/CryptoFoundations/Rewinding/BlockRound.lean) |
| Bounds against reruns | `Rewinding.ResetPolicy.finder_bounds_honest` | [`FinderBridge.lean`](../../VCVio/CryptoFoundations/Rewinding/FinderBridge.lean) |
| Transcript recovery | `Rewinding.recover`, `Rewinding.ResetPolicy.recover_bounds_honest` | [`Extraction.lean`](../../VCVio/CryptoFoundations/Rewinding/Extraction.lean) |
| Query cost | `Rewinding.ResetPolicy.chargedAttempt`, `Rewinding.ResetPolicy.recover_bounds_honest_charged` | [`Cost.lean`](../../VCVio/CryptoFoundations/Rewinding/Cost.lean), [`Extraction.lean`](../../VCVio/CryptoFoundations/Rewinding/Extraction.lean) |

## Reset policies

A `Rewinding.ResetPolicy init impl` reimplements an oracle handler `impl`, whose state starts from
`init`, with two pieces of state. The **world** holds what every rerun must see the same way, such
as private coins or a random-oracle table. It grows as runs discover new entries and is never
reset within an attempt. The **cursor** holds a run's position, such as how many coins it has
drawn, and restarts on every rerun. Four laws make reruns faithful:

- `Rewinding.ResetPolicy.faithful_coins`: one run, interleaved with independent coins, has the
  honest distribution.
- `grows`: a query only extends the world.
- `frozen`: an answer observed in a world is replayed in every extension of it.
- `commute`: two runs discover the same world in either order.

`Rewinding.ResetPolicy.attempt` runs a black-box algorithm
`alg : OracleComp (unifSpec + rerunSpec Q α) β` against these reruns. A query `q` on the second
summand executes `run q` from its beginning against the current world and returns its output. The
attempt returns the algorithm's output and the number of complete runs. The algorithm's own coins
come from the first summand and are not frozen.

The library provides these policies:

- `Rewinding.fixedTape` freezes a prover's private coins: a rerun replays every coin draw that an
  earlier run made.
- `Rewinding.ResetPolicy.ofRandomOracle` freezes a lazily sampled random-oracle table.
- `Rewinding.ResetPolicy.stateless` and `Rewinding.ResetPolicy.ofEmptySpec` cover deterministic
  oracles and the empty spec.
- `Rewinding.ResetPolicy.product` runs two policies side by side over `spec₁ + spec₂`, for example
  a prover's coins beside a random oracle.

## Finders

A finder is a computation `find : OracleComp (unifSpec + accSpec C) (Option Out)`. It sees a
Boolean acceptance oracle on complete challenge vectors `(r : R) → C r` and its own coins, and
nothing else. `Rewinding.IsFinder` states its contract against every fixed acceptance function
`f`:

- `sound`: every returned output satisfies `good f`.
- `success`: the acceptance rate `ε` of `f` and the success probability `p` satisfy
  `ε ≤ κ + (1 − κ) p`.
- `cost`: the expected number of acceptance-oracle calls is at most `T`, counted over complete
  runs whether or not they succeed.

`Rewinding.IsTreeFinder` specializes the contract to finders that return a `Rewinding.VecTree`
whose sibling challenges satisfy a node predicate and whose leaves all accept. The threshold finder
of Attema–Cramer–Kohl is a tree finder (`Rewinding.isTreeFinder_thresholdFinder`). Figure 11 of
Fenzi–Moghaddas–Nguyen is a finder that returns a star of challenges
(`OracleComp.isFinder_coordFinder`). Its generalization to an alphabet and a threshold per coordinate
(`OracleComp.isFinder_blockFinder`) runs one round of `Rewinding.blockChildren`, which collects,
from a pool per coordinate, `k j - 1` accepted children of an accepted centre. At one coordinate
that round is the threshold round of Attema–Cramer–Kohl
(`Rewinding.thresholdChildren_eq_blockChildren`).

## Bounds against frozen reruns

On a finite set of challenge vectors, a frozen prover determines one random table of complete
outputs. `Rewinding.ResetPolicy.eagerTable` draws all of them at once, and
`Rewinding.ResetPolicy.attempt_eagerTable` shows that every black-box algorithm sees the same joint
output and complete-run count from frozen reruns as from this table. A finder's guarantees hold
for every fixed acceptance function, so they hold on average over the table:

- `Rewinding.ResetPolicy.finder_bounds` reads the acceptance rate as the average acceptance rate of
  the table.
- `Rewinding.ResetPolicy.finder_bounds_honest` reads it as the honest acceptance probability,
  averaged over challenge vectors. This is the form to use against a concrete prover:

```text
(∑ c, Pr[run c accepts]) / |challenge vectors| ≤ κ + (1 − κ) · Pr[the finder succeeds]
E[number of complete runs] ≤ T
```

## Recovering transcripts

A finder returns challenges. A witness extractor needs the prover's transcripts at those
challenges, taken from the runs whose verdicts the finder saw. `Rewinding.recover` does this in
three steps:

1. It runs the finder. Each acceptance query `q` executes a complete run of `run q`, caches its
   output `a`, and answers `accept q a`.
2. On success with output `o`, it looks up the transcript at each point `points o i` in the cache,
   and reruns only on a miss. The index type of the points needs `FinEnum`, which fixes the lookup
   order and keeps `Rewinding.recover` computable.
3. It hands the transcripts to the extractor `ext o`.

Against frozen reruns, recovery is the finder against the verdicts of an eager table, followed by
extraction from the same table (`Rewinding.ResetPolicy.attempt_recover`). When every good output
accepts at its points (the hypothesis `hpts`), the finder queried all of them
(`Rewinding.IsFinder.mem_log_of_mem_support`). So there are no misses, and on every outcome
recovery makes exactly the finder's complete runs
(`Rewinding.IsFinder.snd_eq_of_mem_support_recoverFrom`). The main results are:

- `Rewinding.ResetPolicy.recover_bounds_honest`: if the extractor returns a valid witness from the
  transcripts of every good output, in every table of the eager table's support (the hypothesis
  `hext`), then a valid witness comes back with the finder's success bound, after at most `T`
  complete runs in expectation. `Rewinding.ResetPolicy.recover_bounds_honest_sub` states the
  success bound with subtraction.
- `Rewinding.ResetPolicy.recover_tree_bounds_honest`: the case of a tree finder, with the leaves
  as the points. It needs no `hpts`, because every leaf of a returned tree accepts.
- `Rewinding.ResetPolicy.valid_of_mem_support_attempt_recover`: every returned witness is valid.
  This uses only the finder's soundness.

The hypothesis `hext` ranges over tables in the eager table's support. In each such table every
complete run is a pure lookup in one world (`Rewinding.ResetPolicy.eagerTable_settled`), so runs
that begin with a common phase publish the same value from it. For a multi-round prover,
`Rewinding.ResetPolicy.eagerTable_proj_eq_of_key_eq` gives the messages that sibling transcripts
share. For a Σ-protocol prover, `Rewinding.ResetPolicy.eagerTable_fst_eq` gives the shared
commitment.

[`VCVioTest/RewindingExtraction.lean`](../../VCVioTest/RewindingExtraction.lean) puts the pieces
together for a specially sound Σ-protocol: the threshold finder with two branches, recovery of both
transcripts, and the protocol's extractor. It runs under `Rewinding.fixedTape` and under the product
of `Rewinding.fixedTape` with a random oracle.

## Query cost and the accounting boundary

The cost field of `Rewinding.IsFinder` counts complete runs. To count the oracle queries inside
them, `Rewinding.ResetPolicy.chargedAttempt` instruments every rerun with a cost model and adds up
the charges beside the run count. Forgetting the charges gives the plain attempt back
(`Rewinding.ResetPolicy.map_chargedAttempt_eq_attempt`). If every complete run has worst-case query
cost at most `c` (`WorstCaseCostBound`), the expected accumulated query cost is at most `c * T`:

- `Rewinding.ResetPolicy.finder_bounds_charged_of_worstCaseCostBound` for a finder;
- `Rewinding.ResetPolicy.recover_bounds_honest_charged` for recovery.

The accounting boundary is `run q`. Instrumentation charges exactly the oracle queries inside
`run q`, and nothing checks that `run q` is complete. So:

- `run q` must include the verifier and everything the extractor reads. A run that stops at the
  prover's last message leaves the verifier's queries uncharged.
- The charge excludes the reset policy's work to answer queries, local computation, and the
  finder's own coins and work.
- Under `Rewinding.fixedTape` the prover's queries are its coin draws, so a rerun that replays a
  draw from the frozen tape is charged for it again.

The module documentation of
[`Cost.lean`](../../VCVio/CryptoFoundations/Rewinding/Cost.lean) gives the form of these bounds
that uses the expected largest rerun cost, and explains why an average cost per input does not
suffice: a finder may pick its inputs after it sees the frozen world.
