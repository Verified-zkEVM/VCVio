# B01 upstream-main / PR #593 integration review r0

Verdict: **FAIL** — 1 blocking finding, 1 nonblocking finding. S05 must not start and the
candidate must not be pushed from this review state.

Date: 2026-08-31

Reviewer role: fresh independent technical boundary reviewer

Candidate: `ef750c13f085a343637a05bbad91b25dc04a469c`

Candidate tree: `294c8164ae52bec04e8d118bcb9442f75d7c62ec`

Accepted predecessor: `ca84e4f18610ba40dadd44466cd987507a199c24`

The worktree was clean at review start. I did not implement S05, modify an implementation file,
merge another head, or push. This review artifact is the only intended repository change.

## Exact history and merge resolutions

The candidate has the required history, with no squash or rewritten parent:

- `15a26d7bafa91df1db8c1bd9af074e9df155fd91` has parents
  `ca84e4f18610ba40dadd44466cd987507a199c24` and
  `a9dd3bd2895d2ca8bbe02af480c1df7c3be64e24`.
- `07e625f99a56798d3087518a45167108d7a562e7` has parents
  `15a26d7bafa91df1db8c1bd9af074e9df155fd91` and
  `0caf09ca831ba0686db549b596ddfeb121de69ac`.
- `ef750c13f085a343637a05bbad91b25dc04a469c` has sole parent
  `07e625f99a56798d3087518a45167108d7a562e7`.

I inspected `git show --remerge-diff` for both merges. The seven conflicts in `15a26d7b` are
technically coherent:

- `.github/workflows/build.yml` retains the accepted SLH-DSA/KAT and computability checks while
  accepting upstream's axiom-sweep jobs.
- `HashSig/SLHDSA/Primitives.lean` accepts upstream's `CorePrimitives`, fixed-width `AdrsKey`,
  `adrsToKey`, variable-arity `Thash`, arity-specific `F`/`H`/`Tl`, and separate public hash
  interpretation. The accepted byte-injectivity law is moved to `CorePrimitives.ByteLaws`, so the
  concrete obligations are correctly stated on `(primitives).core.ByteLaws`.
- `LatticeCrypto/MLDSA/SecurityNMA.lean` accepts upstream's now-global ring sampleability
  instances rather than retaining redundant parameters.
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Chain.lean` accepts the upstream nested-support
  lemma and the required `noncomputable` annotations consistently.
- `VCVioTest.lean` and `VCVioTest/Computability.lean` retain the accepted local canaries and accept
  upstream's new imports, mixed-query canary, and `evalSPMF` wording.
- `lakefile.lean` retains the three SLH-DSA focused executables and accepts the upstream axiom-sweep
  executable and fixture library.

The sole `07e625f9` conflict deletes the old approval-coupled `ParameterSet`/`ParameterProfile`/
Boolean `Params.Valid` block and preserves PR #593's canonical mathematical `Params.Valid`,
proof-carrying `ValidatedParams`, twelve-member `FipsParameterSet`, and separate
`LimitedParameterSet`. The post-merge `HashSig/SLHDSA/FipsParams.lean` adds only category,
component-size, derived-width/WOTS facts, enumeration length, and family-aware `ofParams`; it does
not create a second validity or approval model.

## Technical integration audit

The upstream Lean 4.33.1 architecture remains authoritative. WOTS, XMSS, FORS, hypertree, and
Scheme expose monad/oracle-parametric programs over `CorePrimitives` and `publicHashSpec`; their
deterministic wrappers use `PublicHash.impl`. `PublicHashQuery.thash` retains the public seed,
fixed-width address key, and ordered node list, so singleton `F`, binary `H`, and variable-arity
`Tl` are distinguished by arity and payload. `Hmsg` is a separate dependent query. The core bundle
contains secret `PRF`/`PRFmsg` but no concrete public hash implementation.

The S02 compatibility edits consistently use upstream `PublicKeyCore prims.core` and
`SecretKeyCore prims.core` in generated key pairs, scheme interfaces, query indices, transcript
and ITSR definitions. The four affected finite role types have explicit complete `Fintype`
instances; their cardinality canaries elaborate.

The concrete boundary retains the intended FIPS grammar:

- SHA2 uses the checked canonical 22-byte `ADRSc` boundary, SHA-256 for `F` and `PRF` in all
  categories, SHA-256 for category 1 `H`/`Tl`/`Hmsg`/`PRFmsg`, and SHA-512 for the corresponding
  category 3/5 operations. Invalid structural addresses are rejected by the checked entry points;
  the total bundle uses the documented zero-key/zero-node projections pending successor-session
  reachable-address proofs.
- SHAKE uses the full 32-byte `Adrs.toVector` key for the single SHAKE256 `Thash` collection and
  the full address in `PRF`; `PRFmsg` and `Hmsg` have the required concatenation and output widths.
- All twelve `approvedPrimitives` cases dispatch by the canonical `FipsParameterSet.hashFamily`.
  `sha2Primitives_byteLaws`, `shakePrimitives_byteLaws`, and the all-set theorem prove
  `CorePrimitives.ByteLaws` on `.core`.

The fixed-width public/secret/signature codecs consume `FipsParameterSet` directly and the runtime
suite checks all twelve rows, rejecting short and long inputs. The data, primitive, oracle, WOTS,
XMSS, FORS, hypertree, and scheme canaries build under the new types. The exact five generated
compiler helpers are:

```text
SLHDSA.base2bFill._unsafe_rec
SLHDSA.base2bGo._unsafe_rec
SLHDSA.WotsChecksum.digitsOfBaseW._unsafe_rec
SLHDSA.chainWith._unsafe_rec
SLHDSA.C13.chain._unsafe_rec
```

The compiled audit checks each helper against its safe parent and reports the HashSig transitive
axiom union exactly `[propext, Classical.choice, Quot.sound]`. It reports no HashSig `sorryAx`,
generated `native_decide` axiom, source/user partial or unsafe declaration, extern, initializer, or
runtime override. Thus the old aggregate HashSig security `sorry` is genuinely absent rather than
hidden by a relaxed baseline. The repository axiom-sweep fixture matrix and baseline check also
pass.

PR #594 `c0930e49f74580fc8c0c22fbbffd8496df38972a`, PR #595
`be823fbb6745e95412efe2bf49e0e46055953413`, and PR #596
`7068fd993e35748822d07bba922fe70fe2953cd9` are present as inspectable refs but are not ancestors
of the candidate; their distinct new implementation/test files are absent. B01 and S05 do not
import or duplicate them. The records correctly reserve #594/#596 for S11--S16, but their PR #595
session range is incomplete as recorded in B01-R0-002.

## Finding

### B01-R0-001 — HIGH / blocking — the authoritative full wrapper rejects the Lean 4.33.1 link trace

`./scripts/slhdsa/validate.sh` reproducibly reaches the fresh, no-cache parser build and then fails:

```text
SLH-DSA harness check: FAIL: S01: parser executable trace has no unique structured linkObjs input
```

This is a stale trace-shape parser, not evidence that the parser executable linked the wrong
module. The fresh Lean/Lake 4.33.1 executable trace has schema `2025-09-10`, but its input is now
nested as:

```text
HashSigTest.SLHDSA.ACVP.ParserTests:linkInfo
  Module.moreLinkObjs
    .../ParserTests.c.o.export
    .../StrictJson.c.o.export
    .../Schema.c.o.export
    .../libleanhashing.a
    .../libleanmlkem.a
    .../libleanmldsa.a
    .../libleanfalcon.a
```

The independently retained trace bytes had SHA-256
`ad0fdbe2943bd2045f97fadc6f3b40cff8b130fb322cd516729a120b7f01d55f`. Each of the three expected
ACVP export objects appears exactly once with a structured 16-hex token. The candidate checker at
`scripts/slhdsa/check-harness.py:3063` still searches only for a top-level pair whose key is exactly
`linkObjs`; a focused mutation helper later in the same file makes the same old-shape assumption.
The executable itself therefore supplies positive dependency-isolation evidence, but the committed
authoritative wrapper cannot attest it and cannot proceed to its remaining production steps. This
contradicts the B01 handoff's claim that the full validation passes and is blocking under the
zero-finding acceptance rule.

Required repair: update the production trace validator to require exactly one
`<parser-module>:linkInfo` group and exactly one nested `Module.moreLinkObjs` array, preserving the
existing exact-object, object-output-token, module-source, direct-import, sidecar, mutation, and
fail-closed schema checks. Update the corresponding focused mutation cases to exercise the new
nested shape, then rerun the exact full wrapper from a clean candidate and obtain a fresh review.
Do not weaken the check to a recursive suffix search or accept both shapes without explicitly
pinning the active Lean/Lake version and structural path.

### B01-R0-002 — MEDIUM / nonblocking — PR #595's handoff omits its S07 ownership

The required ownership interval is S07--S09 because PR #595's `Position` line owns digest
decomposition and the digest-derived FORS address as well as hypertree layer trajectories. Both
`docs/slhdsa/sessions/B01-upstream-boundary-integration.md` and `docs/slhdsa/plan.md` instead reserve
it only for S08/S09. The exact PR head remains unmerged and its files are absent, so this is not a
premature code import, but the incomplete record could authorize S07 to duplicate PR #595's FORS
position work.

Required repair: change both active B01 handoff records to reserve PR #595 digest/position ownership
for S07--S09. Keep the exact digest and the existing prohibition on premature merge/duplication.

## Command evidence

The following commands were run at the exact candidate before this artifact was created:

```text
git status --porcelain=v1 --untracked-files=all
git rev-parse HEAD HEAD^{tree}
git cat-file -p 15a26d7b
git cat-file -p 07e625f9
git cat-file -p ef750c13
git show --remerge-diff 15a26d7b -- <all seven conflicted paths>
git show --remerge-diff 07e625f9 -- HashSig/SLHDSA/Params.lean
git diff --name-status 07e625f9..ef750c13
```

History, tree, cleanliness, and conflict inspection passed.

```text
./scripts/slhdsa/validate.sh
```

The initial harness and provenance checks passed; `lake build`, `lake build HashSig`, and
`lake build HashSigTest` completed successfully (the expected absent-native-submodule stub warnings
and unrelated pre-existing VCVio sorry warnings were observed). The fresh parser build produced the
correct executable and exact three ACVP objects, then failed only at B01-R0-001.

```text
lake env lean scripts/slhdsa/S02InventoryProbe.lean
lake env lean scripts/slhdsa/S03InventoryProbe.lean
lake env lean scripts/slhdsa/S04InventoryProbe.lean
lake env lean scripts/slhdsa/PolicyAudit.lean
```

The focused probes passed. The policy audit reported 32 HashSig modules, 2,561 owned constants,
the exact five compiler helpers, and exact axiom union
`[propext, Classical.choice, Quot.sound]`.

```text
lake exe slhdsa_kat
lake exe slhdsa_c13_kat
lake exe slhdsa_data_codec_tests
lake exe slhdsa_primitive_tests
```

All four runtime suites passed, including valid/tampered KAT behavior, all twelve codec rows, SHA2
address rejection, SHA2/SHAKE vectors, boundary inputs, and all twelve primitive fingerprints.

```text
lake exe mk_all --lib HashSig --module --check
bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh
bash scripts/check-complexity-backend-isolation.sh
bash scripts/check-polyfun-boundary.sh
./scripts/test-axiomsweep.sh
lake exe axiomsweep --check
./scripts/test-pmf-boundary.sh
./scripts/test-polyfun-boundary.sh
./scripts/test-complexity-backend-isolation.sh
./scripts/slhdsa/validate.sh --docs-only
python3 -B scripts/slhdsa/check-acvp-provenance.py
git diff --check ca84e4f18610ba40dadd44466cd987507a199c24..ef750c13f085a343637a05bbad91b25dc04a469c
```

Generated imports, isolation and boundary checks, negative fixtures, axiom sweep, docs-only
validation, provenance, and diff hygiene all passed.

```text
cd docs/slhdsa/report
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-b01-review-r0-tex slhdsa-formalization-audit.tex
```

Report rendering passed (8 pages; 329,059-byte PDF). Output stayed under `/tmp`.

## Final disposition

Finding counts: **1 blocking, 1 nonblocking**. Verdict: **FAIL**. The cryptographic and proof-level
boundary integration reviewed here is coherent, and the residual is convincingly diagnosed as a
Lean/Lake 4.33.1 trace-schema migration rather than a substituted dependency. Nevertheless the
authoritative full wrapper is red and its handoff claim is inaccurate. Repair B01-R0-001, rerun the
complete gate, repair B01-R0-002's ownership interval, and obtain a new independent zero-finding
review before push or S05.
