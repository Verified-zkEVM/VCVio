# Parallel-QROM review response and reproducible checks

The reviewed stack consists of #1188 and #1190–#1196. Its model and headline security
statements passed two independent reviews. The follow-up narrows documentation claims,
strengthens two quantitative bounds, and makes concrete inversion certificates available
as Lean declarations. The theorem scope remains finite-dimensional quantum programs,
finite input windows for the exact byte construction, and query-bounded preprocessing
with unrestricted retained memory.

## Mathematical and scope corrections

| Topic | Response |
|---|---|
| Masked-chain collision allowance | Only the `q + 1` programmed input vertices need to be distinct. The allowance is `choose(q+1,2)/N`; the endpoint remains in the joint observation but is not part of that bad event. Without preprocessing, the zero-round bound is exactly `1/N`. |
| Online point budget | `qromDelaySecure_quantumWindowScheme_min_width_points` uses `min onlineWidth onlinePoints` for the same admissible adversaries. This is a width refinement; a round-times-total-online-points hybrid is separate. |
| Whole-bit inversion claims | `parallelQROMBits_plantedPreimage_127` and `parallelQROMBits_plantedPreimage_128` state the advertised large-cardinality certificates for the actual planted-preimage game and its syntactic budgets. |
| Exact-encoding prerequisites | The delay proof uses the raw window runtime, honest execution laws and injective honest-input encoding. Table splitting is a separate exact encoding result, retained as a reusable API. |
| Preprocessing in the coupling | Both phases of the programmed game query the completed programmed oracle. The later preprocessing hybrid pays explicitly to replace only preprocessing by the base-oracle run. |
| Deadline | Every online branch must stop before `keyRound`. Early successes of a program that continues longer on other branches need a separate truncation theorem. The checked honest solver validates the commitment one round after key derivation. `quantumWindowDerive` has a proved `keyRound` budget and fixed-oracle honest-generation correctness. |
| Literature comparison | Afshar et al. Lemma 5.5 already bounds the endpoint event. The root-accumulation bookkeeping gives order `kq³/N`; the detailed published theorem states order `sqrt(kq³/N)`. No endpoint novelty or best-known-bound claim is made. |
| Concrete link widths | The guide evaluates the 24-byte reference schedules with an explicit per-round width cap and preprocessing premise. The illustrative quantum estimates are about `2^-82.33` and `2^-42.33`, compared with the paper's classical `2^-117` and `2^-97`. These are oracle-resource calculations, not a gate-cost or hardware reduction. |
| Search calibration | One Grover iteration has success `(3 - 4/N)^2/N`, approaching the hybrid bound `9/N` as `N` grows. Exact finite-`N` equality with `9/N` is not claimed. |

The [time-lock guide](../quantum/guide/7-time-lock-puzzles.md) gives the final experiment
and its assumptions. The [design account](quantum-layer.md#20-concrete-finite-window-query-estimates)
gives exact numerical schedules. The
[literature page](../quantum/reference/literature.md#search-calibrated-security-bits)
states the security-bit normalization and planted coupling without requiring a private PDF.

## Generic interfaces and separate follow-ups

A batch round queries one base port. Several additive oracles can be encoded as one port
on a sum domain when a round must query them together. Sequentialization supplies a full-run
law and point-budget certificate; sequential bounds apply through them when their local
signature includes arbitrary instruments. Gate-set or local-cost restrictions need their
own transport.

The quantum puzzle interface embeds classical honest generators. The adapter from arbitrary
classical two-phase adversaries, with advantage equality and phase-budget transport, is a
separate bridge. Generic quantum correctness and solver-budget predicates are also separate;
the applications state their honest laws and resource bounds directly. A key-recovery bound
alone does not assert that an arbitrary puzzle is solvable.

The root bound is the recommended masked-chain API. The older event-error family remains
available. Generalizing its online cutoff from the chain-length parameter to a smaller actual
adversary round count, and factoring every event-error theorem through root comparisons,
are proof/API refinements rather than missing hypotheses of the current bound. The existing
import direction is `RootBounds → Homogeneous → Bounds`; deriving the older family from
root theorems first requires separating shared definitions and lemmas to keep that graph
acyclic. It is not a local replacement of every proof by one root-theorem invocation.

The claim that empty-round removal has no production use does not hold for the whole stack:
`Quantum/Oracle/MaskedChain/Preprocessing/DropEmpty.lean` uses it for the effective
preprocessing round budget `min rpre Qpre`. It is infrastructure at the earlier experiment
PR's head. Likewise, sections 14 and 15 of `quantum-layer.md` are present in the integrated
stack and belong to the masked-chain application; an earlier slice omits those application
sections. The full design page has consecutive sections 1–20.

QuantumFoundations and VCVio have a pre-existing `Quantum.QComp` name collision. The stack
imports the completely positive subinstrument modules and does not import
`QuantumFoundations.Instrument` or its dependent umbrella. Upstream API/name coordination is
separate from this stack. Generic foundations and uniform-table APIs remain upstream candidates;
a declaration can be useful independently of the application that first motivated it.

Auxiliary-input security after unbounded preprocessing, serialized puzzle interfaces,
unrestricted-length quantum queries, and CFHL compressed-oracle collision/chain bounds remain
separate development tracks.

## Recomputing the 24-byte estimates

The following standard-library calculation evaluates the uncapped expression in the guide
at its declared per-round cap and preprocessing product. It prints the base-two logarithms;
negative values are meaningful before the probability cap.

```python
from decimal import Decimal as D, localcontext

with localcontext() as context:
    context.prec = 100
    S, A, L = D(2)**256, D(2)**128, D(2)**192
    width, preprocessing_product = D(3_500_000_000_000), D(2)**100
    for chains, steps in [(16, 2**29), (33, 273038961038961)]:
        rounds = D(chains * (steps + 2))
        path_points = D(chains * (steps + 3) + 1)
        incidence = 1/L + path_points/S
        preprocessing_incidence = incidence/A
        root = (1/S.sqrt() + 2*rounds*(width*incidence).sqrt()
                + 2*(preprocessing_product*preprocessing_incidence).sqrt())
        bound = path_points**2/S + root**2
        print(bound.ln()/D(2).ln())
```

The outputs round to `-82.3295` and `-42.3278`. This arithmetic check is separate from the
Lean theorem and from the assumptions relating oracle resources to elapsed seconds.

## Reproducing the historical 1,290-contract comparison

The 1,290-declaration result describes compatibility of the Lean 4.36 audited port
`ed4e0a4fc73738de9e03cf50abde672fdd413a40` with the polished integration
`67ca1cdff44a38757999d34152412e78a52c1d5e`. It does not assert that later strengthening
of a bound has the same statement. The immutable historical JSON records retain their original
commits and hashes. Their machine-local snapshot paths are not required for this reproduction.

The two commits, capture tools, module inventory and dependency pins are available in the
[public repository](https://github.com/Verified-zkEVM/VCVio). With Git, `uv` and the pinned
Lean toolchain available, start in a fresh directory:

```bash
git clone https://github.com/Verified-zkEVM/VCVio.git qrom-contract-review
cd qrom-contract-review
git checkout --detach 67ca1cdff44a38757999d34152412e78a52c1d5e
git worktree add --detach ../qrom-contract-baseline ed4e0a4fc73738de9e03cf50abde672fdd413a40
QROM_REVIEW_DIR="$(pwd)"
QROM_BASELINE_DIR="$(cd ../qrom-contract-baseline && pwd)"
mkdir contract-review
```

Extract the exact 64-module production scope from the committed quality record:

```bash
uv run --no-project --python 3.12 python - <<'PY'
import json
from pathlib import Path
record = json.loads(Path("docs/design/parallel-qrom-polish-validation.json").read_text())
modules = sorted({m for cut in record["cuts"] for m in cut["contract_modules"]})
assert len(modules) == 64
Path("contract-review/modules.txt").write_text("\n".join(modules) + "\n")
PY
```

Build the production umbrella in both isolated trees. Use the same committed inspector to
capture each compiled environment:

```bash
lake exe cache get
lake build VCVio
(cd "$QROM_BASELINE_DIR" && lake exe cache get && lake build VCVio)
uv run --no-project --python 3.12 python scripts/check-quantum-port-contracts.py capture \
  "$QROM_BASELINE_DIR" "$QROM_REVIEW_DIR/contract-review/baseline.json" \
  --root VCVio --modules-file "$QROM_REVIEW_DIR/contract-review/modules.txt"
uv run --no-project --python 3.12 python scripts/check-quantum-port-contracts.py capture \
  "$QROM_REVIEW_DIR" "$QROM_REVIEW_DIR/contract-review/polished.json" \
  --root VCVio --modules-file "$QROM_REVIEW_DIR/contract-review/modules.txt"
uv run --no-project --python 3.12 python scripts/check-quantum-port-contracts.py compare \
  contract-review/baseline.json contract-review/polished.json \
  --modules contract-review/modules.txt --out contract-review/comparison.json
```

The expected historical comparison has 1,290 shared declarations and no raw type,
captured definition-body or reducibility changes. Captures also record source/tool hashes,
the actual working-tree status and dependency manifests. The output files themselves are
created only for this reproduction, so their provenance metadata need not match the older
machine-local snapshot bytes.

The comparison is not a proof-axiom check. Run the current repository checks independently:

```bash
lake exe axiomsweep --check
lake exe initsweep --check
lake lint
lake test
lake exe initsweep --check --root VCVioTest --root LatticeCryptoTest
bash scripts/check-imports.sh
```

The default axiom sweep covers configured production roots. The explicit test initializer
roots above are `VCVioTest` and `LatticeCryptoTest`; they do not imply a complete fresh
axiom sweep of every test declaration or a `HashSigTest` umbrella. The default `lake test`
builds all three test libraries and runs its executable and CSV checks. Native FFI tests use
the separate `--ffi` mode. Each PR must still pass on its own base and head.

When sibling PRs land, merge both documentation contributions and regenerate the umbrellas
with `scripts/update-lib.sh`; choosing one side of `ToMathlib.lean` or `VCVioTest.lean` can
drop exports or regression imports. Compare the union of application sources against the
integration reference and rerun generated-import checks on the actual landing tree.
