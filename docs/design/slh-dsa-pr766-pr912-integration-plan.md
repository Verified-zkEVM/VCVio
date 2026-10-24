# SLH-DSA integration plan for PRs 766 and 912

Status: execution specification, 2026-10-24. The implementation and merge gates below remain
open unless the validation record explicitly marks a probe complete.

Preserve #766's general classical-ROM security results and reusable framework APIs. Land #912
as an additional deterministic SHAKE-128s result, connect it to the existing wire-game API, and
retain the stronger applicable bound on their common scope. Keep the larger construction,
deployment, and security developments as separately specified follow-ups.

## Starting revisions

| Input | Pinned revision | Role |
|---|---|---|
| `main` | `f3df0ac18aa5ae72b3e920ad5460492aa039b4f7` | Canonical integration base |
| #766 | `aaf16f331e2d8cdc3e93f5bdb4029804c286689a` | General ROM proofs, wire transport, evaluators, certificates, profiles |
| #912 | `1e1a0b0e9d6ed78351e98409719d754f2acd7e64` | SHAKE-128s transcription, proof, bridge, and FORS order correction |
| #886 | `97b8b31afde12e3af4e674d8fd5990f3de9716a2` | Independent generic API and provider-family follow-up |
| Existing integration merge | `21880ea684198fb8b5fa502edd11e5d02d81fca5` | Merge of the pinned #766 and `main`; a reference tree for reconstruction |

#912 is stacked on #766. Its 531-file comparison also includes a merge from `main`; the
changes after the integration merge are 394 files. Reconstruct the intended additions rather
than treating every file in the displayed comparison as new SLH-DSA work.

Use Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and the dependency lock
of the canonical integration base. In particular, its PolyFun revision is
`5670109ccaaaf945c6003519244b76e0777ecc45`. Recheck these pins before execution; changed heads
require a new unique diff and validation record.

## Results that must survive

1. #766's `securityTarget_two_one` and its general-depth, per-public-seed and averaged forms.
2. Single-SHAKE SUF-CMA bounds at all six SHAKE parameter sets, including deterministic and
   hedged signing, and the `n = 32` weak-seed treatment. Preserve the corresponding EUF forms.
3. Pure-mode wire transport, strict codecs, named reductions, exact evaluators, the 18-entry
   certified table, existing structured-ROM range certificates, and security profiles.
4. The generic random-oracle, coupling, simulation, wire, and work-transport APIs used by these
   results, with their tests.
5. #912's `SLHDSA.SHAKE128s.slhDsa_sufCma_127`, including its variable-context pure-mode
   request interface and its program/distribution bridge to the library's scheme.

The common interface added below is deliberately narrower than item 5: deterministic
SHAKE-128s, a fixed valid context, independent uniform key seeds, and the fixed 30-byte
random oracle. It does not restrict or replace #912's original theorem.

## A Stabilize and land PR 766

Create a dedicated implementation worktree. Preserve the reviewed heads before changing
published branches. Integrate the pinned `main` into #766; before the FORS changes, the source
tree should match the existing integration merge, apart from explicitly reviewed documentation.

**First implementation checkpoint A0:** build the preserved #766 development on this canonical
dependency lock before developing the adapter or redesigning proofs. Prepare and commit generated
imports first, then use the recorded-head gate below with `lake build HashSig VCVioTest HashSigTest`.
Check actual dependency checkout revisions against `lake-manifest.json`; old probe oleans or a
different PolyFun checkout do not discharge A0. Resolve compatibility failures before proceeding,
and keep the effort estimate provisional until the canonical-lock checkpoints pass.

Apply the selected-secret-first order of [FIPS 205 Algorithm 16](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.205.pdf#page=41) to `forsSignWithSecret`, and
align the lab program and proofs. The known repair surface is nine files:

| File under `HashSig/SLHDSA/` | Required change |
|---|---|
| `SecretProvider.lean` | Read the selected secret before the sibling path; update naturality |
| `Security/CacheSecret.lean` | Reorder the settled-signature witnesses and their consumer |
| `AddressDiscipline.lean` | Sequence the secret predicate before the path predicate |
| `Security/SecretTraces.lean` | Preserve the ledger predicate in the new order |
| `Security/LabScheme.lean` | Reorder `labForsSign` and its predicate proof |
| `Security/LabReadSet.lean` | Reorder the proof that lab signing reads no hidden cell |
| `Security/LabEquiv/Tree.lean` | Read the secret first, then frame its cell fact through path computation |
| `Security/RomDescentSecret.lean` | Destructure the new secret/path witness order |
| `Security/HonestTransfer.lean` | Transport the reordered witnesses |

A [nine-file prototype patch](slh-dsa-pr766-pr912-evidence/fors-order-repair.patch) exists
against the pinned #766 tree as a zero-context unified diff. Apply it from the worktree root
with `git apply --unidiff-zero docs/design/slh-dsa-pr766-pr912-evidence/fors-order-repair.patch`.
Its reconstruction matches the original prototype byte-for-byte in all nine files at both the
pinned #766 and canonical integration baselines. It is a starting patch, not a substitute for
applying the change to the canonical base and rerunning its checks. Preserve headline theorem statements and
numerical bounds. The cache-reader helper's existential witness order changes as itemized
above; update its consumers together and include that API change in the review packet.

Add a small provider-parametric trace regression that distinguishes secret-first from path-first
execution, with distinguishable selected and sibling leaves. Retain the honest-provider equality
and current ACVP regressions. Do not add a duplicate SHAKE implementation for this test.

Put this regression in `HashSigTest/SLHDSA/ForsSecretOrder.lean`, registered as
`slhdsa_fors_secret_order_tests` in `lakefile.lean` and `lake test`. Use small FORS trees and
callbacks that record the operation and address. Check that the selected secret is read first,
the path uses sibling leaves, and two trees are processed in increasing tree order.

Reconcile the PR body and design records: wire transport and canonical parsing, certified
evaluation, and the additional vectors are present; XOF game transport, full honest-work
certificates, and the second construction remain open. Preserve the general-ROM design record
and CSV, rather than replacing them with the SHAKE-128s design note.

**Acceptance:** the preserved headline theorem types and numerical bounds are unchanged; all
affected modules and regressions pass; the regenerated table is byte-identical; full validation
passes on the exact new #766 head. Merge #766 before merging #912.

## B Reconstruct PR 912 as an addition

Use a separate worktree and the stabilized #766 as the base, rebased to canonical `main` after
#766 merges. Bring over the 238 modules under `HashSig/SLHDSA/SHAKE128s/`, preserving attribution,
and the proposed `docs/design/slh-dsa-shake128s-suf-cma.md`. Include the original program bridge
and theorem.
The shared FORS repair belongs to A and should not be introduced a second time.

Do not replay the deletion commit `e897ebb5570f7eaf60c4b8a0142c85e00dc05bf1`. Preserve the
inherited framework modules, security results, test executables, certificate checker, and
security-bound table. Reconcile the README, agent guide, roadmap, and documentation names so
both developments are discoverable. Regenerate library umbrellas using `./scripts/update-lib.sh`.

Keep implementation changes confined to this addition, its shared prerequisites, the adapter
in C, tests, and documentation. Compare the final tree to the stabilized base: unexplained
deletions and unrelated changes fail this gate. Apply the current module/exposure policy;
do not reintroduce broad exposure or eager enumeration already removed from #912.

All 238 new modules are in the headline theorem's import closure. This does not establish that
every declaration or import is needed, but it rules out a simple deletion of an isolated unused
directory. Do not make a large proof rewrite or parameter generalization part of this merge.

**Acceptance:** both sets of headline theorems coexist, their axiom sets remain standard, and
the addition passes full validation without raising warning, lint, axiom, or initialization
baselines. Run the existing wire, table, and ACVP checks as well as the new tests.

**Checkpoint B0 before C:** after the minimal additive reconstruction and the shared repair, commit
the source and generated imports, then build both original theorem families and their tests through
the recorded-head gate on the canonical lock. All 238 imported modules and the final #912 headline
must build here. Do not begin substantial adapter work on the strength of the old-cache probes.

## C Connect the two public security interfaces

Add the proposed `HashSig/SLHDSA/SHAKE128s/Bridge/Wire.lean` for the fixed-context adapter and
the proposed `HashSig/SLHDSA/SHAKE128s/Statement/Theorems/WireStrongUnforgeability.lean`
for the public bound.
The former may import `SLHDSA/Security/Wire.lean`; the existing generic security and VCVio
modules must not import the specialized SHAKE-128s proof. Keep this dependency direction.

Place the transformation, advantage equality and budget transport in
`SLHDSA.SHAKE128s.Bridge`. Place the two public bound theorems in `SLHDSA.SHAKE128s`, beside
the existing headline. Keep the proof-local game implementation intact in this integration.

Let `vp` be SHAKE-128s, `ctx : SLHDSA.Security.PureContext`, and

```text
alg = wireShakeScheme vp ctx deterministicRand (uniform public seed)
adv : SignatureAlg.StrongUnforgeableAdversary alg
V = GeneralScheme.verifyInternalQueryBound vp.params = 3929
B766(qh, qs) = byteBound vp qh qs
             + honestAdrsCount vp / 2^256 * weakSeedFactor vp (everySeedBound vp qh qs)
```

Use the existing conservative verifier cap `V = 3929` for the first public adapter. #912's
sharper cap 3824 is optional subsequent work and is not a premise of this integration.

The concrete adapter `fixedContextAdversary ctx adv` must:

1. Encode the challenger-generated typed public key for the existing wire adversary.
2. Forward ambient queries unchanged, including repeated hash queries and private sampling.
3. Attach `ctx.bytes` to every signing request, map its `some signature` answer to the wire
   signature, and attach the same context to the final forgery.
4. Prove that signing at this valid fixed context cannot return `none`; a total adapter's
   fallback must be unreachable in this experiment.

Prove challenger key consistency before comparing signers: the generated public seed/root
equal the corresponding fields stored in the secret key. Do not claim equality of signers
for arbitrary unrelated public and secret keys. Relate the exact signing logs and returned-pair
freshness, and identify the two empty-cache random-oracle runtimes.

Required public results, with implementation names fixed here:

| Declaration | Required statement |
|---|---|
| `strongUnforgeableAdvantage_eq_fixedContext` | The wire advantage equals the adapted `Game.securityGame FIPS205.scheme` advantage |
| `withinSigningLimit_fixedContext` | `adv.RomQueryBound qh qs` and `qs ≤ 2^64` imply the adapted game's signing limit |
| `hasQueryBound_fixedContext` | The same pathwise budget implies the adapted game's almost-sure work bound `qh + qs + V` |
| `wireStrongAdvantage_le_workBound` | The wire advantage is at most `(qh + qs + V) / 2^127` under those hypotheses |
| `wireStrongAdvantage_le_min_bound` | The same advantage is at most `min (B766 qh qs) ((qh + qs + V) / 2^127)` |

The [adapter contract](slh-dsa-pr766-pr912-evidence/adapter-contract.lean.txt) contains a
type-checked implementation of the adversary transformation, a proved fixed-context signing
equation, and type-checked propositions for the remaining interfaces. Those propositions are
specifications, not proofs of the required advantage or budget statements.

Test the observable boundary using small executable schemes and adversaries where possible:
exact replay loses; a different valid signature on the same signed message wins; repeated hash
calls are all charged; each signing request is charged once; private samples are free; malformed
signatures reject with no verification hashes; context length 255 is admitted and 256 rejects
before hashing. Exercise the fixed-context adapter with a nonempty context. Check that keygen
and signer hash calls remain excluded from `adversaryWork`, while verification is included.
Retain FIPS codec and ACVP tests for the actual scheme. Tests that merely restate the final
theorem do not replace these controls.

Put the counted-game controls in the proposed `HashSigTest/SLHDSA/SHAKE128s/Game.lean`, registered as
`slhdsa_shake128s_game_tests` in `lakefile.lean` and `lake test`. Supply a computable runner
proved equal to the counted experiment, following the existing wire test's
`executableExperiment_eq`; execute it against a small deterministic caching/trace handler.
One fixture must produce exactly these counts: one keygen hash, two signer hashes, two direct
adversary hash calls at the same input, one signing request, and one verifier hash. Two private
samples add no work. The expected `adversaryWork` total is four, while the full hash count is
six. Changing either cache-hit accounting or source attribution must fail the fixture.

Put fixed-context translation and theorem-interface controls in
the proposed `HashSigTest/SLHDSA/SHAKE128s/WireBridge.lean`. Check actual query translation
using a nonempty context and a recognizable signing reply, without executing an expensive full FIPS keygen.
The replay and same-message/different-signature controls must inspect the computed win bit and
log, not rely on application of the final security inequality.

Give this module a `check : IO Unit` entry point and a root `main` that calls it. Register
`lean_exe slhdsa_shake128s_wire_bridge_tests` with root
`HashSigTest.SLHDSA.SHAKE128s.WireBridge` in `lakefile.lean`, and add
`#["exe", "slhdsa_shake128s_wire_bridge_tests"]` to the explicit `lake test` step list.
The targeted invocation is `lake exe slhdsa_shake128s_wire_bridge_tests`. The validation log must
show this executable running its context-translation and freshness assertions; compilation by
the test-library glob alone does not satisfy this gate. Failed assertions must exit nonzero.

**Acceptance:** the adapter adds no probability loss and introduces no extra charged ambient
queries in the adversary phase. Its budget theorem retains verification overhead and needs no
new adversary assumption beyond `RomQueryBound qh qs` and `qs ≤ 2^64`. The original variable-
context theorem remains available. Merge C with #912; the public adapter is part of its scope.

## D Preserve the independent PR 886 follow-up

Restack #886 onto merged #766 in its own worktree and review its unique changes again. Preserve
the corrected FORS order when reconciling provider-family lemmas. Its potential/fresh-answer,
joint-oracle, hidden-seed budget, and provider-naturality results have their own tests and gate.
It does not supply a new SLH-DSA security headline and is not a dependency of C.

Preferred queue: #766, then the independent #886 review and additive #912 review. Either
descendant can land first after #766; the other must then resync and validate its changed
boundaries. Do not block #912 on unrelated unfinished #886 work.

## Validation and review gates

Generation is preparation, performed before recording the validated commit:

```bash
lake exe cache get
./scripts/update-lib.sh
git diff --check
```

Review and commit every intended source change, including `lakefile.lean`, the dependency lock
if intentionally changed, and generated umbrella modules. Require a clean source tree, including
the index and nonignored untracked files, before final validation. Use a dedicated worktree so
unrelated user files do not need to be moved or committed. Put logs and validation evidence outside
the source tree; normal ignored build/cache outputs are permitted.

Run the [recorded-head gate](slh-dsa-pr766-pr912-evidence/validate-recorded-head.py) from that
committed implementation worktree. The helper must also be present in the committed tree:

```bash
python3 docs/design/slh-dsa-pr766-pr912-evidence/validate-recorded-head.py -- \
  ./scripts/validate.sh --lint --test --axioms
```

For A0 and B0, use the same helper with `lake build HashSig VCVioTest HashSigTest` as the command.
It records the source commit/tree, `lean-toolchain`, the active Lean version, a copy and hash of `lake-manifest.json`, and
actual revisions of every git dependency. Each installed dependency must match its locked revision
and have clean source. Both the initial and final active-version queries are bracketed by
read-only captures of the source commit/tree, source cleanliness, toolchain, manifest hash, and
every dependency revision and cleanliness; each query must preserve those inputs. The helper
also requires the snapshots before and after the validation command to match. A failed command
or any change fails
the gate, even when `git diff --check` would pass. The pinned plan uses git dependencies only.

Do not run `update-lib.sh` inside the final recipe. If validation or any generator changes source,
review and commit those changes, then start a new run at the new commit. A passed run certifies
only its recorded commit and lock; rebasing, merging or changing either invalidates that result
for the new head. Attach the external report and command log to the exact PR revision, rather
than committing a self-referential validation report after the run.

Use targeted module builds while iterating. The full validation command already covers the
library build, generated imports, isolation boundaries, style/environment linters, initialization,
tests, documentation, warning budgets, and axiom sweep; retain its log rather than rerunning the
same checks without a code change. `lake test` must continue to regenerate and independently
check the 18-row bound table. A failing test must not be resolved by deleting the API or test.

Record full and incremental `HashSig` build times and peak memory for the stabilized #766 and
the combined tree under the same dependency cache and parallelism. Treat sequential probe
timings as diagnostic data, not a Lake performance comparison. The default CI build must fit
its configured limits; address a limit violation rather than silently extending the timeout.

Inspect `#print axioms` for both original headlines and every new public adapter/bound theorem;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted. No new `sorry`, `admit`,
custom/native proof axiom, unsafe proof escape, linter suppression, or baseline increase is allowed.

The reviewer must independently check scheme identity, key consistency, canonical signature
freshness, fixed versus variable contexts, empty-cache sharing, the signing lifetime, actual
charged query kinds, and the verifier overhead. For #912's probability argument, review the
presampling bridge, coverage/thinning bounds, accepted-forgery shared bound, and the final
assembly separately. Record exact heads, commands, results, and unresolved findings in each PR.

Keep changes reviewable as separate commits: shared FORS repair; additive proof import;
wire/runtime/log adapter; budget transport and minimum bound; regressions and documentation.
Do not merge a commit with a failed gate or an unresolved finding about its claimed theorem.

## Validation record

These probes validate the repair scope and interface specification. They are distinct from
the required canonical-base Lake build and final integration validation.
The [machine-readable record](slh-dsa-pr766-pr912-evidence/validation-record.json) pins the
probe environment, artifact hashes, completed checks, and outstanding obligations.

| Check | Status and scope |
|---|---|
| PR heads and current `main` | Refreshed from GitHub at the revisions above |
| FIPS boundary contracts | Algorithm 16 selects the secret before computing its path; Algorithms 22/24 enforce the 255-byte context limit |
| #766 table | Existing compiled generator reproduced all 18 rows byte-for-byte; independent exact rational checker passed |
| #766 headline axioms | Three-oracle, single-SHAKE and wire headlines report only the three standard axioms |
| Existing wire executable | The pinned #766 executable passed its replay, fresh-pair, query-forwarding and codec regressions |
| Deletion restoration | Reverse-application probe identified ten files needing manual reconciliation, mainly imports, docs and later-edited fixtures |
| Shared FORS repair | All 61 affected modules required by the selected headline/regression targets compiled; [module results](slh-dsa-pr766-pr912-evidence/fors-rebuild-results.json) |
| Adapter boundary | Transformation and target propositions type-check; fixed-context signing equation and `V = 3929` are proved in the probe |
| Counted test runner | A computable runner and its equalities to the counted experiment compile; its new runtime fixture still requires a Lake-linked executable |
| Unchanged #912 coexistence | [168 of 238 modules](slh-dsa-pr766-pr912-evidence/new-proof-compatibility-results.json), including its full scheme bridge, compiled against the repaired environment; the broader probe was stopped after this checkpoint |
| Byte-range follow-up targets | All 36 proposed coefficient inequalities passed exact rational arithmetic; Lean range transport remains open |
| Recorded-head validation gate | 25 isolated-repository fixtures pass: the original 13 cover clean/ignored-build success, dirty source/index, generated-import mutation, moved HEAD, dependency mismatch/dirt, command failure, and wrong Lean; 12 cover dirty or committed source/dependency changes and committed manifest/toolchain changes during both initial and final version queries |
| Canonical-base checkpoint A0 | Passed at `65dc7c27bba380b9bfa1ae33d2df3e5fd7a8ce54`: `HashSig`, `VCVioTest` and `HashSigTest` built with clean source and all 11 locked dependencies; external report and hashes are recorded in the validation record |
| Full combined build and validation | Required on the canonical dependency lock after implementation; not discharged by these probes |

The repair and interface probes used Lean `v4.35.0`, cached dependencies from the clean pinned
#766 checkout, Mathlib at the revision above, and PolyFun
`ef4c157b3c6775fb55864303d96f9b400428d5f0`. Every affected module in the recorded target closure
was recompiled. The differing PolyFun revision is why these successes do not certify the final
canonical dependency lock. The nine-file repair changes no advertised security conclusion.

The [counted runner prototype](slh-dsa-pr766-pr912-evidence/counted-runner.lean.txt) validates
the executable definition/equality seam. Direct `lean --run` could not load the native
`OracleSpec.query` symbol from the cached library arrangement, so the fixture's numerical
output is not an executed check here. Build the named executable through Lake for that gate;
do not replace the runtime assertion with a theorem-only example. The remaining 70 #912
modules and its final headline have not been rebuilt by the coexistence probe.

Reproduce the validation-gate fixtures with
`python3 docs/design/slh-dsa-pr766-pr912-evidence/test-validate-recorded-head.py`.
These fixtures exercise commit/lock enforcement; the separate A0 compilation passed as recorded
above. B0 and full implementation validation remain pending.

## Follow-ups after both security developments coexist

### Honest hash work certificates

Add SLH-DSA instances of `SignatureAlg.RomWorkBounds` for the actual oracle-backed programs,
then use the existing `K + qh + qs*S + V` transport. Count secret-provider queries and the
message PRF as well as public hashes. Prove generic callback bounds and instantiate the typed
model at validated bundles and the byte model at all six SHAKE sets in both signing modes.
Do not use pure-PRF signing counts as the certificate for an oracle-backed signer, or use
#912's keygen lower bound as an upper certificate. Acceptance is the resulting whole-experiment
hash-work theorem with all honest hash caps discharged. Random-bit, input-length, cycle, and
wall-clock costs remain separate obligations.

### Byte-level range certificates

Extend `RangeBound`/`BoundCertificates` to the averaged byte bounds and wire profiles. Fix
`L = 2^32`, `U = 2^64`, and signing lifetime `S` in `{2^20, 2^32, 2^64}`. The uniform result is
`Adv ≤ qh / 2^bits` for `L ≤ qh ≤ U` and `qs ≤ S`. These bits normalize by `qh`, not by #912's
total work.

Use the existing structured coefficient plus the maximum additive byte term divided by `L`.
At `n = 32`, retain the weak-seed factor and bound it at the maximum budgets; replacing it
by one would destroy the intended coefficient. Prove the requisite monotonicity in Lean.
The following conservative integer targets passed exact rational checks at both shapes of
each security size:

| Node bits `8n` | Deterministic, `S ≤ 2^20` or `2^32` | Deterministic, `S ≤ 2^64` | Hedged, all three lifetimes |
|---|---:|---:|---:|
| 128 | 126 | 95 | 126 |
| 192 | 190 | 159 | 190 |
| 256 | 254 | 223 | 254 |

The deterministic byte term `(qs + 1)/2^(8n)` contributes approximately `S/L` to the coefficient.
It prevents carrying the structured `8n-2` floor unchanged into the last deterministic column.
These are sufficient floors for this rectangle, not optimal security levels or a weakening of
the existing point certificates. The [exact coefficients](slh-dsa-pr766-pr912-evidence/byte-range-coefficients.json)
are arithmetic feasibility evidence; kernel-checked certificates and security transport are
the follow-up's deliverables.

The intended certificate set contains 36 inequalities: six SHAKE sets, three lifetimes, and
two signing modes. Acceptance includes all 36 kernel-checked coefficient certificates,
their wire-profile corollaries for every budget in each rectangle, and an independent exact
arithmetic check. Retain the 18 current point certificates unchanged.

Reproduce the arithmetic check against the pinned #766 source snapshot, or the integration
tree retaining its evaluator and CSV:

```bash
python3 docs/design/slh-dsa-pr766-pr912-evidence/check-byte-range-targets.py /path/to/pr766-source
```

### Variable-length XOF adversaries

Define a prefix-consistent oracle on `(input bytes, requested length)`, using a per-input cached
prefix and fresh independent suffixes when extending it. An ordinary random oracle keyed by
the pair would be incorrect because different requested lengths must share prefixes.
Simulate it using the existing fixed-`m` oracle plus a cached private suffix, with at most one
charged fixed-oracle query per adversary request. Prove joint game and budget transport for
all six SHAKE sets, retaining context, signing-mode, seed, and freshness contracts. Test short,
zero, repeated, extended, and rate-boundary output lengths, and reuse the library's SHAKE
implementation and prefix results. Acceptance is a public security corollary for XOF
adversaries, not only deterministic SHAKE prefix consistency.

### Second construction and further security models

Pin the leanSPHINCS specification and implementation revision before beginning a reuse port.
Inventory its WOTS+C search, different forest/address grammar, 256-bit secrets versus 128-bit
nodes, failure, pruning, and master-seed-derived parameters. Define its actual programs and
prove correctness and security at that revision. Extract common provider/graph/probability
interfaces when consumed by this port, with equality/refinement back to both constructions;
do not generalize the specialized proof solely to reduce a file count. A parameter-bundle
instantiation alone is not acceptance for this milestone.

SHA-2 byte-level security, prehash collision accounting, standard-model reduction adversaries,
and quantum security remain separate projects. The standard-model lane must first specify
resource-bounded games and reduction costs; an unbounded, freely winnable assumption game
cannot supply a deployment security claim. Neither merge closes these milestones.

## Effort and checkpoints

Planning estimates are focused engineer-days, excluding independent review and CI queue time.

| Work | Estimate | Checkpoint |
|---|---:|---|
| Canonical-base #766 integration and shared FORS repair | 1-2 | A0 passes first; preserved headlines, table and regressions then pass |
| Additive #912 reconstruction and documentation | 0.5-1 | B0 builds both original theorem families on the canonical lock before C |
| Fixed-context wire/runtime/log adapter and budget/minimum theorems | 1-3 | Contracts in C are proved without extra loss or hypotheses |
| Combined gates and fixes | 0.5-2 | Exact-head validation and review packet are complete |
| Independent #886 restack and review preparation | 0.5-1 | Its unique nine-file follow-up validates on the new base |

The 3-8 implementation day estimate for A-C is provisional until A0 and B0 pass. Allow another
2-5 reviewer-days focused on the
statement, bridge and critical probability arguments. This is not a complete line-by-line
audit of the specialized proof. Revise the estimate if canonical-base integration reveals
additional semantic changes, an adapter requires a new adversary assumption or probability
loss, or a probability theorem needs redesign. Resolve such findings before proceeding to
the dependent merge.

Allow roughly 2-5 implementation days for honest hash caps, 1-3 for byte-range certificates,
and 5-10 for XOF game transport, subject to their stated gates. Scope the second construction
and architectural extraction separately as multiweek work after its pinned inventory; no
fixed completion estimate for those research tasks is implied by the integration estimate.

## Sources

- [PR 766](https://github.com/Verified-zkEVM/VCVio/pull/766) and its
  [validated follow-up record](https://github.com/Verified-zkEVM/VCVio/blob/aaf16f331e2d8cdc3e93f5bdb4029804c286689a/docs/design/slh-dsa-classical-rom-bound.md#validated-review-follow-up-2026-10-23).
- [PR 912](https://github.com/Verified-zkEVM/VCVio/pull/912), its
  [statement and bridge design](https://github.com/Verified-zkEVM/VCVio/blob/1e1a0b0e9d6ed78351e98409719d754f2acd7e64/docs/design/slh-dsa-shake128s-suf-cma.md), and its
  [deletion commit](https://github.com/Verified-zkEVM/VCVio/commit/e897ebb5570f7eaf60c4b8a0142c85e00dc05bf1).
- [PR 886](https://github.com/Verified-zkEVM/VCVio/pull/886).
- The repository's `AGENTS.md`, `CONTRIBUTING.md`, `scripts/validate.sh`, and SLH-DSA design records
  at the pinned integration revisions govern attribution, worktrees, layering, tests, and review.
