# Bounded refactor probes

These three frozen research sources validate small interfaces, not a completed shared security
game or graph/probability port. [The plan](../slh-dsa-reuse-refactor-plan.md) records the unproved
implementation gates. [evidence.json](evidence.json) binds source/log hashes, exact environment,
results and limitations; [strength-manifest.json](strength-manifest.json) inventories 77 original
source declarations in 25 groups. A source-header inventory does not replace kernel statement,
observer or all-budget proof recovery during implementation.

| Source | Validated scope |
|---|---|
| [VariableContextWire.lean](VariableContextWire.lean) | Per-query valid-context framing injectivity; canonical Wire/full #766 bound and weak term; sharper hedged bound; 128s/192f consumers; invalid 256-byte-context collision |
| [WeightedBudgetProbe.lean](WeightedBudgetProbe.lean) | Weighted structural/pathwise bridge; adaptive joint cap 2 vs separate 2+2; nonunit policy cap/witness 6; erasure, AE and probability-one event |
| [ReplyLogProbe.lean](ReplyLogProbe.lean) | Generic readback/raw-log freshness; actual total `signingLogContains` and optional-success formula; rejection retained in raw log, replay and distinct-signature examples |

P1 does not implement a rejected-request signing experiment. P2 is a free-program cost consumer,
not complete SUF/source/cache specialization or phase/input-dependent actual game execution.
P3 is a pure log proof, not execution/charging of a signer or a game/security equivalence.
None proves the effectful FORS gate, a full original-127 transport, or parameterized graph security.
The final logs [p1](p1.log.txt), [p2](p2.log.txt), [p3](p3.log.txt) have no warnings/errors or `sorryAx`;
printed proofs use subsets of `propext`, `Classical.choice`, `Quot.sound`.

The plan source is main `9b4e1a0307414994c5fe7b136d4c52cdd39333fa`, tree `e10d9c55…`.
The actual probes ran in an isolated private clone at local `92eaa1af…`, tree `74b8149d…`, with
source and all eleven dependencies clean/unchanged before and after. They import only unchanged
framework/#766 modules; P1 checks all 295 local source-closure Git blobs against both revisions.
P1's static closure is not the complete external-package closure or a build-size measurement.
The reviewed tree equals the earlier integration source `f2bd85c9…`; the local withdrawal is
not the refactor implementation base. No production source or baseline was changed by these probes.

To reproduce, use a checkout containing this plan/evidence with the pinned canonical lock and
prepare the named existing modules in an owned build environment. Do not share writable caches
or mutate another validation lane. Lean is `v4.35.0`; PolyFun is `ecac686f…`, Mathlib `56a00585…`;
all full revisions and the manifest hash are in evidence.json. From that checkout's root:

```bash
lake exe cache get
lake build HashSig.SLHDSA.Security.Wire VCVio.CryptoFoundations.SignatureAlg \
  VCVio.OracleComp.QueryTracking.CostModel VCVio.OracleComp.QueryTracking.QueryBound
probe_dir="$PWD/docs/design/slh-dsa-reuse-evidence"
LEAN_NUM_THREADS=4 timeout 90s lake env lean --root="$probe_dir" \
  -DautoImplicit=false "$probe_dir/VariableContextWire.lean"
LEAN_NUM_THREADS=4 timeout 60s lake env lean --root="$probe_dir" \
  -DautoImplicit=false "$probe_dir/WeightedBudgetProbe.lean"
LEAN_NUM_THREADS=4 timeout 60s lake env lean --root="$probe_dir" \
  -DautoImplicit=false "$probe_dir/ReplyLogProbe.lean"
```

The recorded P1 command additionally wrote an external `.olean` under its isolated prototype
root. No heartbeats/recursion limits or linters were relaxed; P2/P3 produced no object/code files.
P1's final run took 27.63s, P2 4.98s; no separate elapsed timer was recorded for final P3.
These times describe those probes only. Failed intermediate attempts are not acceptance evidence.
No complete repository build was run by the prototypes, and their scoped PASS is not a claim
that the future shared architecture, all original strength-preserving ports or CI have passed.
