# SLH-DSA security-delta recovery pilot

The Lean 4.35 pilot below records the 3929-call verifier allowance at its cited revisions.
The current development proves `slhDsa_sufCma_le` for the FIPS 205 joint-work game and uses
a 3824-call allowance in `wireStrongAdvantage_le_jointWorkBound` for fixed contexts.
[Current security guide](slh-dsa-shake128s-suf-cma.md) ·
[FIPS theorem](../../HashSig/SLHDSA/SHAKE128s/Statement/Theorems/StrongUnforgeability.lean) ·
[Wire theorem](../../HashSig/SLHDSA/SHAKE128s/Statement/Theorems/WireStrongUnforgeability.lean)

This bounded research record compares validated `b63fede77cfcf9e23fda94c28e951e4520fdeb91`
with main `cc6ae6cc39c1cca024d292262f90880b551fb2b3`. It does not change production code or
establish that either probability proof is indispensable. The original target remains

```lean
Game.HasSecurityBits FIPS205.scheme Game.adversaryWork 127
```

This quantifies over every per-request message/context adversary, every `q >= 1`, an almost-sure
signing-attempt lifetime of `2^64`, and an almost-sure joint sum of signing attempts, direct hashes
and final-verifier hashes at most `q`. The scheme is deterministic pure-mode SHAKE-128s with
independent uniform seeds and one initially empty, full-30-byte oracle. Keygen/signer hashes execute
but are excluded from that sum. A proof from the #766 route is **not recovered here**.

## Checked results

The three [Lean probes](slh-dsa-security-delta-evidence/) establish:

- `StructuralRecovery.structural_bound`: the #766 fixed-valid-context wire theorem at its unchanged
  structural caps, including the full weak-seed term.
- `byte_zero` and `envelope_zero`: at `qh=qs=0`, its complete expression is
  `7859 / 2^128 + A / 2^256`, where `A = honestAdrsCount vp`.
- `EligibleComparison`: every constant candidate gives a query-free wire client; its transformed
  external game satisfies the original lifetime, the actual joint cap `q=3929`, and exact advantage
  equality. This establishes common eligibility, not an attack or a success lower bound.
- `zero_caps_obstruction`: `3929 / 2^127` is strictly smaller than that complete structural
  expression. Their gap is `1/2^128 + A/2^256`. This obstructs domination by that displayed formula;
  it does not show that a sharper consequence of lower-level #766 lemmas is unavailable.
- `OperationalRecovery.advantage_eq_zero` and `advantage_eq_zero_fips`: an actual joint cap below
  569 gives zero success, at both the paper and native byte interfaces, with variable contexts and
  **no lifetime premise**. These use the existing accepted-verifier lower bound, the common counted
  observation and a representation bridge. They import neither the positive 127 theorem nor its
  probability route. This isolates an existing operational guarantee; it is not a new security bound.

All three probes compile with Lean 4.35.0, `j4`, default proof limits and ordinary imports.
Ten selected axiom reports use only `propext`, `Classical.choice`, `Quot.sound`. The final check has
no errors, warnings or admissions. Compiler outputs are external; accepted b63 library artifacts
are read without rebuilding or modifying that checkout. This is a bounded prototype, not another
full-library or runtime validation.

## The difference is not confined to the tiny zero-cap example

On the **same fixed-context wire advantage**, let `h=qh`, `s=qs`, `V=3929`, and let `C(h,s)` be
the existing weighted target-coverage expression. The deterministic formulas are

```text
G = (h+1) C(h,s) + (2(h+V)+s+1)/2^128 + A/2^256
W = (h+s+V)/2^127
G-W = (h+1) C(h,s) + (1-s)/2^128 + A/2^256.
```

The existing exact evaluators justify the expressions; [compare_bounds.py](slh-dsa-security-delta-evidence/compare_bounds.py)
replays the following comparisons with Python `Fraction`, Stirling numbers and factorials.
These are arithmetic comparisons of existing bounds, **not new formal security theorems**.
All displayed bounds are below one and satisfy `s <= 2^64`.

| `qh` | `qs` | General `G` | Specialized `W` | Smaller expression |
|---|---|---:|---:|---|
| `2^64` | `2^64` | `1.63652517243e-19` | `2.16840434497e-19` | General |
| `2^80` | `2^64` | `7.17247190134e-15` | `7.10553577782e-15` | Specialized |
| `2^120` | `2^64` | `0.00788828641787` | `0.00781250000000` | Specialized |
| `2^126` | `2^64` | `0.525100843537` | `0.500000000000` | Specialized |

Thus neither published expression uniformly dominates the other. The minimum already on main
retains both on their common scope. #766 also already covers one full-byte SHAKE oracle, all six
SHAKE parameter sets, deterministic/hedged families and refined weak-seed bounds. #912's narrower
actual-joint theorem is not the first single-oracle or full-30-byte result. No claim about an optimal
finite-budget envelope, matching formal SLH attack, or independent modeling assumptions follows.

## Exact residual work for a #766-based recovery

The promising existing owner is
[`JointBound.prEvent_idealDraw_runTargetCollision_or_runHiddenHit_or_le_of_charged`](../../HashSig/SLHDSA/Security/JointBound.lean),
whose `hbud` retains the deferred-state quantity

```text
2 * keyEntries.encard / |Y| + χ.U(cache) + seedCharge(cache) + χ.c(cache) <= B.
```

It accepts the existing `DeferredCharge`; another oracle/counter framework is unnecessary.
The structural verifier maximum enters the specializations, notably
`PrfKeyBound.two_mul_encard_keyEntries_div_add_seedCharge_add_hmsgCharge_le_of_mem_support`
(lines 157–198), using `a+b <= qh+V` and `a+b+h <= qh+qs+V` from `LabBudget`.
That produces `2(qh+V)+qs+1`, losing the actual per-run charge information.

A finite next recovery attempt must discharge four obligations:

1. Flatten successful variable-context requests to arbitrary **internal bytes**, preserving fresh
   returned pairs. Invalid signing requests return `none` locally but retain their attempt charge.
   A fixed-empty-context wire wrapper is not this reduction. A failed final parse may give an internal
   fallback extra losing work, so preserve the winning event or keep the rejecting wrapper explicitly.
2. Relate the real almost-sure joint cap to an appropriate capped/prefix/deferred run. It does not
   imply an all-free-path structural cap: two queries to the same cached input cannot disagree in the
   real ROM, but a free-program disagreement branch can contain arbitrarily many queries.
3. Retain actual role counts in the existing charged-potential bound and account jointly for coverage,
   byte clashes and weak seeds within `2q/2^128`. Substituting `qh=qs=q` does not do this. Winning-only
   normalization using the operational 569 lower bound can help but still leaves universal-verifier
   slack if `Vmax` is retained. The displayed bound's `+1` may itself be removable in special cases;
   the search of existing lemmas here is not exhaustive.
4. Prove the exact original all-`q`, variable-context endpoint, preserving every stronger applicable
   #766 regime before retiring the specialized probability route.

At the pilot revision the parsed verifier had a 569–3824 hash-call interval. A framing or
signature-decoding failure returns before any hash query. A well-formed signature that fails the
final root comparison still incurs verification work. The pilot used the universal 3929-call
allowance. The current fixed-context wire theorem uses the proved 3824-call upper bound across
all these branches. [Current wire theorem](../../HashSig/SLHDSA/SHAKE128s/Statement/Theorems/WireStrongUnforgeability.lean)

## Cost and salvage interpretation

Against duplicate-heavy main, #1009 shares real implementations and proof mechanisms, but adds
8,871 production physical Lean lines. That does not establish it is preferable to a #766-based
selective integration. Some extracted mechanisms have only #912 production consumers. The separate
salvage inventory identifies a small native provider-observation convenience, while graph clients,
moments and exact-count packages need independent justification if the paper development is removed.
Extraction alone does not justify keeping all 73 new production files. Removing #912 without
replacements loses established guarantees. A narrower replacement could preserve the displayed wire
corollaries without recovering the full
variable-context joint theorem; these are separate preservation choices.

## Evidence and replay

[manifest.json](slh-dsa-security-delta-evidence/manifest.json) records exact sources, outputs and log
hashes; [checks.log](slh-dsa-security-delta-evidence/checks.log) contains the concise axiom reports.
Preparatory failed elaborations are retained externally as nonacceptance; no source change is hidden
by their later successful replays. No production change, runtime test or publication is part of this pilot.

```sh
python3 docs/design/slh-dsa-security-delta-evidence/replay.py \
  --artifacts /tmp/vcvio-slhdsa-integration --output /tmp/slhdsa-security-delta-replay-new
python3 docs/design/slh-dsa-security-delta-evidence/compare_bounds.py
```

After review and a research commit, add `--recorded-head FULL_COMMIT_SHA` to require a clean source
checkout at that exact commit before and after the same checks. The artifact checkout and its twelve
dependency checkouts must remain clean and locked. No cache download or production build is run.
