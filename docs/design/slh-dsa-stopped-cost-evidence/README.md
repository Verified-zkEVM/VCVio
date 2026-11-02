# Stopped-prefix query-cost transport

This is a checked generic research artifact, outside the production import graph.
It is not an SLH-DSA instantiation or a recovery of the positive-127 bound.

`QueryImpl.stoppedAtBad` freezes base state after a bad state is reached.
The cost observer charges the triggering query and freezes its counter thereafter.
`prEvent_stopped_cost_gt_le_full_cost_gt` bounds the upper tail of that prefix
cost by the complete cost under a handler related by `DominatedUntilBad`.

The theorem assumes invariant preservation and a common input-only Nat weight.
It retains arbitrary initial counters and requires no preservation-of-bad premise,
structural query bound, crypto assumption, or auxiliary security hypothesis.

The implementation has one handler, two private support lemmas and one theorem.
Polishing changes only headers, module visibility, documentation and diagnostics.
All declaration types, premises and implementation/proof tokens match the reviewed
prototype after removing comments, whitespace and terminal diagnostic commands.

Validation used Lean v4.35.0, default proof limits and `-j2`, against immutable
olean libraries from VCVio commit `b63fede77cfcf9e23fda94c28e951e4520fdeb91`.
The packaged module and an independent importing audit both compiled without warnings.
The audit printed the exact theorem type and only `propext`, `Classical.choice`
and `Quot.sound` as axiom dependencies. There is no `sorryAx` dependency.

To repeat the audit, compile `CostTail.lean` to an external output directory,
put that directory before the pinned dependency libraries in `LEAN_PATH`, and
compile a module containing:

```lean
import CostTail
#check @QueryImpl.prEvent_stopped_cost_gt_le_full_cost_gt
#print axioms QueryImpl.prEvent_stopped_cost_gt_le_full_cost_gt
```

`manifest.json` pins source, dependency metadata and external validation receipts.
Raw compiler logs and intermediate attempts remain outside the repository.
Remaining work includes phase-aware observer transport, exact source-budget
correspondence, stopped cache-potential compatibility and same-measure coverage.
