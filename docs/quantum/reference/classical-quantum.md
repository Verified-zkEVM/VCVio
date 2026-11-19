# Classical and quantum side by side

This dictionary pairs classical VCVio interfaces with their quantum counterparts; see the
[program guide](../guide/4-programs-and-runtimes.md) for execution and the
[QROM guide](../guide/5-qrom.md) for the classical embedding.

| Classical VCVio | Quantum VCVio |
|---|---|
| `OracleSpec`: query and answer types | `QuantumOracleSpec`: ports with input and output registers and a result type |
| `OracleComp spec α` | `QuantumComp L spec X A`, `QuantumComp₂`, `QComp` |
| a query handler, `QueryImpl` with `simulateQ` | a runtime, `QuantumRuntime`, with `QuantumRuntime.run` |
| a stateful handler | a runtime's private register |
| subprobability distributions; failure as missing mass | subinstruments; failure as missing trace |
| `evalDist`, `SemanticsVia` | `outcomeMeasure`, `evalDist`, `SubInstrument.semanticsVia` |
| `randomOracle`, lazily sampled | `qromEvalDist`: $H$ sampled once, queried through $U_H$ |
| `IsTotalQueryBound` | `IsQueryBound` |
| `OracleComp (X →ₒ Y) α` | embedded by `OracleComp.toQuantum`, with the same distribution |
| `OracleComp (unifSpec + (X →ₒ Y)) α` | `OracleComp.toQuantumRandomized`: ordinary basis queries, free local private coins, and the same lazy random-oracle law |
| `OracleComp (unifSpec + (X →ₒ Y).batch) α` | `OracleComp.toQuantumBatch`: one quantum call per list round, local private coins, the same lazy random-oracle law |
| classical `IsOnlineQueryBound oa (r, q)` | round bound `r` and point bound `q` for `oa.toQuantumBatch` |
| classical list-order unbatching | quantum sequentialization of `oa.toQuantumBatch`, with the same observed law |
| pathwise natural-number charges on oracle ports | `IsQueryChargeBound`: under per-call charge bounds, total weight is at most budget times input trace |
| weighted incidence of hidden disagreement sets | `sum_mul_re_trace_conj_parallelInputProjector_frame_le`: expected union mass for a challenge-independent input state |
| finding one uniformly hidden marked input | `markedSearchAdvantage_le_of_isPointBound`: success at most `min 1 ((1 + 2 * sqrt (q * Q))^2 / N)` with round cap `q` and total-point cap `Q` |

The marked-search experiment uses one additive `ZMod 2` oracle marking a single hidden input.
Its interpretation, program, initial state and guessing rule are independent of that input;
failure contributes missing mass. `preimageSearchAdvantage_le_of_isPointBound` separately bounds
inversion of a fixed target under one uniform random function, with the same round and point
budgets and with response-space cardinality in the denominator.
