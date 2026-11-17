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
