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
