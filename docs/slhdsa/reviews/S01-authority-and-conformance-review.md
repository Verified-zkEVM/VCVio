# S01 adversarial review — authority and pinned conformance anchors

Verdict: **FAIL**

Reviewer: independent S01 authority/conformance review sub-agent; not an S00/S01 implementer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 tree

Date: 2026-08-24

Independence statement: I did not design or implement S01. I reviewed the frozen tree and did not
repair it. All reproduction artifacts and mutations were confined to `/tmp`; this verdict is my
only repository edit.

## Required checks

- [x] The frozen diff is confined to the S01 allowlist and contains no construction/security edit.
- [x] The S01 review was `PENDING` before this reviewer-authored verdict.
- [x] S00 r0-r8 remain canonical `FAIL` artifacts and r9 remains the accepted `PASS` artifact.
- [x] Primary-source bytes, sample files, projections, license, revisions, sizes, and hashes were
  independently reproduced from the pinned local inputs.
- [x] Final FIPS 205 controls the exact twelve normative parameter/API entries.
- [x] SP 800-230 is an Initial Public Draft, separate from FIPS 205, limited-use, and capped at
  `2^24` signatures per key.
- [x] ACVP-Server v1.1.0.38 is used only as the exact server-format compatibility boundary;
  current evidence is v1.1.0.43 and protocol Internet-Draft `-01`.
- [x] Public ACVP artifacts are called sample JSON, not approved vectors or certificates.
- [x] All 15 GenVal hashes/sizes, the protocol root and 15 sections, and every committed
  vendored/projection hash and extraction recipe reproduce.
- [x] The independently derived suite counts are keyGen 12/120, sigGen 72/624, and sigVer
  36/504 with 72 positive and 432 negative results.
- [x] The ordered 144-cell matrix is bijective; exactly the stated 24 pairs are positive; every
  set misses ten cells; SHA3-224 and SHAKE-128 are globally uncovered.
- [x] Negative cases are not used as evidence of correct pre-hash OID/digest binding.
- [x] Strict parser/schema inspection and independent probes cover duplicate keys, strict JSON,
  conditional fields, joins, widths, bounds, and sigVer exact/plus-or-minus-one behavior.
- [x] Context length 255 is accepted and 256 rejected.
- [x] `lake build HashSigTest` is distinguished from, and followed by, native execution of the
  63-case parser suite.
- [ ] The normal gate hard-pins and fails closed over all controlling S01 authority metadata.
- [ ] Profile identifiers unambiguously distinguish the six-set IPD authority profile from the
  one-set legacy current-code subprofile.
- [ ] Docs, bibliography, matrices, findings, TCB, report, and session record agree without factual
  or traceability defects.
- [ ] A comprehensive whitespace check, including untracked S01 files, is clean.
- [x] S00 r9 propagation is limited to evidence accepted by r9; F-015/F-016 remain open and
  COV-005 remains missing/S10.

## Commands and evidence

### Frozen state and scope

Before writing this file:

```text
git branch --show-current
codex/sphincsplus-formalization

git rev-parse HEAD
f1853af40da1efa11a71c2d7011996eebdbf6938

git status --short --branch
## codex/sphincsplus-formalization
 M lakefile.lean
?? HashSigTest/SLHDSA/ACVP/
?? docs/slhdsa/
?? scripts/slhdsa/
```

The tracked diff from HEAD contains only the minimal `slhdsa_acvp_parser` executable declaration
in `lakefile.lean`. Enumerating tracked and untracked paths found no change under `HashSig/**`; all
other S01 files are confined to `HashSigTest/SLHDSA/ACVP/**`, `scripts/slhdsa/**`, and
`docs/slhdsa/**`. The S01 review contained exactly `Verdict: **PENDING**`. Each immutable S00 review
has one canonical verdict: r0-r8 `FAIL`, r9 `PASS`; the historical findings and dispositions remain
semantically intact.

### Independent authority reproduction

I independently used `sha256sum`, `wc -c`, `pdfinfo`, `pdftotext`, `git rev-parse`, `git show`,
`find` in `LC_ALL=C` order, and separate `jq`/Python derivations against the pinned local inputs.

FIPS 205 at `/home/alh/SPHINCS/NIST.FIPS.205.pdf` is 1,055,752 bytes with SHA-256
`8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d`. The official NIST page
identifies the 2024-08-13 final standard. Table 2 independently yielded these paired SHA2/SHAKE
rows, shown as `(n,h,d,h',a,k,lg_w,m,pk,sk,sig)` in bytes where applicable:

| Sets | Exact tuple |
|---|---|
| 128s | `(16,63,7,9,12,14,4,30,32,64,7856)` |
| 128f | `(16,66,22,3,6,33,4,34,32,64,17088)` |
| 192s | `(24,63,7,9,14,17,4,39,48,96,16224)` |
| 192f | `(24,66,22,3,8,33,4,42,48,96,35664)` |
| 256s | `(32,64,8,8,14,22,4,47,64,128,29792)` |
| 256f | `(32,68,17,4,9,35,4,49,64,128,49856)` |

The profile contains each SHA2 and SHAKE member, for exactly twelve rows. Sections 10 and 11 also
confirmed the 255-byte context maximum, pure-domain byte 0, pre-hash-domain byte 1, DER OIDs for
SHA-256/SHA-512/SHAKE128/SHAKE256, category eligibility, deterministic versus hedged `opt_rand`,
and the exact SHA2/SHAKE primitive grammars. The ACVP schema accepts all twelve protocol hash names
without incorrectly imposing the narrower FIPS strength-eligibility table.

`/tmp/NIST.SP.800-230.ipd.pdf` is 282,069 bytes with SHA-256
`62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e`. The official NIST page
identifies it as the 2026-04-13 Initial Public Draft, not final; its strict cap is `2^24` signatures
per key. Its six separate, non-normative rows reproduce as:

| Set pair | Exact tuple `(n,h,d,h',a,k,lg_w,m,pk,sig)` |
|---|---|
| SHA2/SHAKE-128-24 | `(16,22,1,22,24,6,2,21,32,3856)` |
| SHA2/SHAKE-192-24 | `(24,21,1,21,25,9,3,32,48,7752)` |
| SHA2/SHAKE-256-24 | `(32,21,1,21,25,12,2,41,64,14944)` |

The two pinned checkouts were clean and at the declared commits:

```text
git -C /tmp/slhdsa-s01-acvp-server rev-parse HEAD
975de31eb83d87039ec88934fdc47d8c312b892d

git -C /tmp/slhdsa-s01-acvp-protocol rev-parse HEAD
892fd14710f3a7edbea230d0aecc5511e0257f8e
```

The server commit is tag/release v1.1.0.43. Official tag resolution gives v1.1.0.38 =
`85f8742965b2691862079172982683757d8d91db`; its release evidence supports only the documented
external-interface and pre-v38 sigGen/sigVer response compatibility boundary. The pinned protocol
root declares `draft-livelsberger-acvp-slh-dsa-01`, `revdate: 2024-06-25`, and an informational
work-in-progress Internet-Draft.

All 15 ACVP-Server GenVal artifacts independently measured as follows:

| Suite/artifact | Bytes | SHA-256 |
|---|---:|---|
| keyGen registration | 438 | `dfbf8116cb108209bc8fe539ec460dcda7036336ff460e4b0d9cf55c464fca08` |
| keyGen prompt | 32454 | `bce170976f257ee3dfc8c54ea46722ccb553539847daa6d8048f0216cc28b51c` |
| keyGen internalProjection | 75294 | `d7c53a1b6450087047b57aae83a5a51a0ac89ecdb23ebe071e83fbb69ae9d920` |
| keyGen expectedResults | 45192 | `f35f74b6676d6b369c87e88c36698f28c14d5929d31e507d910288c69258afee` |
| keyGen validation | 6792 | `df6726b334e4ab0ce0b48f716a423bd2b4366cea589d2878ff3023ba11494da9` |
| sigGen registration | 1776 | `f7db21f297028ae806a07b482a7bad73e49c8df2bf0dec492786c1313ba9fa72` |
| sigGen prompt | 5512830 | `afa673eacdf0aec53512a159159b7632684adfcd0d88f8640a7f6f5796aacdc8` |
| sigGen internalProjection | 38178342 | `62b42e7c27fda5de8a94aba2943ae413b59b6ea08141f3bc035b1eceae235dba` |
| sigGen expectedResults | 32595492 | `71e8e0f7e4b0cfd1747314299204d9d4d50968d200a4ae873921eaa7aabeaad1` |
| sigGen validation | 35520 | `4b3e13ff387d2b491b94a60f78b09d7c0d568154061773cb6d8faf6b28b448fc` |
| sigVer registration | 1730 | `afe3475e0e0f2680daf0f6b908832e8f0649f2dc6909b5df6be78802f09e5dde` |
| sigVer prompt | 30513796 | `4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb` |
| sigVer internalProjection | 30731848 | `a013fc2104f4ed4799d96d51141f65b965969b2cf10646626a021b6d456ce792` |
| sigVer expectedResults | 39216 | `259f5e2a0665de0adc0fefa45b5db3a2a6ed13c3c44d14bdaf64a80aee12c687` |
| sigVer validation | 28680 | `83335f44c1b91d90258da79e398eb7370e06b1eb2dd94279da01fffba64a54ee` |

The protocol root is 2,258 bytes with SHA-256
`d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061`. All 15 included sections'
sizes and hashes independently matched `provenance.json`; recomputing the documented
root-plus-sections manifest in exact path order gave composite SHA-256
`bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54`.

Current official evidence also confirmed issue #469 open with the positive-only SLH-DSA
OID/digest limitation, and PR #471 open/unmerged with no sample-JSON regeneration. The docs do not
treat either as closed or merged.

### License, projection, and matrix reproduction

The complete three-paragraph NIST ACVP-Server README license is present in `NOTICE-NIST.txt`, with
NIST acknowledgement, source release/commit, and a modification notice. Independent byte
comparison showed the five vendored files each equal the complete upstream file followed by one
documented final LF, with no other byte change; they are not falsely called byte-identical.

Independent extraction from the upstream prompt/result joins reproduced the selected projection
records: sigGen `(tgId,tcId)` = `(19,157)`, `(20,164)`, `(31,271)`, `(55,469)`, `(56,476)`,
`(67,583)`; sigVer = `(19,253)`, `(19,256)`, `(19,257)`, `(19,258)`, `(20,268)`, `(31,422)`.
Source hashes and upstream order match, and optional-checkout regeneration reproduces both
projections and the coverage matrix.

Independent whole-suite joins gave:

```text
keyGen: 12 groups, 120 tests
sigGen: 72 groups, 624 tests
  external/preHash deterministic=false 12/144; true 12/144
  external/pure    deterministic=false 12/84;  true 12/84
  internal         deterministic=false 12/84;  true 12/84
sigVer: 36 groups, 504 tests = 72 positive + 432 negative
  external/preHash 12/168; external/pure 12/168; internal 12/168
```

All prompt/result IDs join globally and bijectively. The exact matrix axes are parameter sets
`SHA2-128s, SHAKE-128s, SHA2-128f, SHAKE-128f, SHA2-192s, SHAKE-192s, SHA2-192f,
SHAKE-192f, SHA2-256s, SHAKE-256s, SHA2-256f, SHAKE-256f` and hashes `SHA2-224,
SHA2-256, SHA2-384, SHA2-512, SHA2-512/224, SHA2-512/256, SHA3-224, SHA3-256,
SHA3-384, SHA3-512, SHAKE-128, SHAKE-256`, in that order. Its exact positive evidence is:

```text
SHA2-128s:  SHA2-512 (tg20/tc268),       SHAKE-256 (tg20/tc271)
SHAKE-128s: SHA2-512/224 (tg26/tc351),   SHA2-512/256 (tg26/tc364)
SHA2-128f:  SHA2-256 (tg2/tc25),         SHA3-384 (tg2/tc19)
SHAKE-128f: SHA2-512/256 (tg8/tc111),    SHA3-512 (tg8/tc107)
SHA2-192s:  SHA2-256 (tg22/tc307),       SHA2-512/256 (tg22/tc302)
SHAKE-192s: SHA3-256 (tg28/tc386),       SHA3-384 (tg28/tc388)
SHA2-192f:  SHA2-512 (tg4/tc52),         SHA2-512/224 (tg4/tc53)
SHAKE-192f: SHA3-384 (tg10/tc139),       SHA3-512 (tg10/tc129)
SHA2-256s:  SHA2-512 (tg24/tc331),       SHA3-384 (tg24/tc328)
SHAKE-256s: SHA2-512/256 (tg30/tc417),   SHA3-256 (tg30/tc412)
SHA2-256f:  SHA2-224 (tg6/tc72),         SHA2-384 (tg6/tc84)
SHAKE-256f: SHA2-224 (tg12/tc167),       SHA2-256 (tg12/tc168)
```

Thus each set has exactly two positives and ten missing pairs; SHA3-224 and SHAKE-128 are globally
absent. Docs correctly keep the 432 negative cases out of OID/digest-binding evidence and do not
call sample JSON an approved vector set, certificate, or conformance result.

### Parser, schema, and executed gates

Manual inspection found the adapted strict JSON parser's recursive internals private and minimal.
It checks decoded keys before insertion, so literal and escaped-equivalent duplicates are rejected
at every nesting level, and it requires EOF. No new `unsafe`, axiom, `sorry`, `extern`, initializer,
runtime override, `implemented_by`, or opaque policy surface was found.

The schema enforces exact keys, types, enums, nonempty groups/tests, positive and globally unique
IDs, exact prompt/result joins, key/seed/signature widths, message/context bounds, interface and
pure/preHash conditions, deterministic/randomness rules, and all twelve ACVP hash names. For
sigVer, prompt signatures accept exact and plus/minus-one lengths; positive results require exact
length, while negative results accept the intended exact/plus/minus-one cases.

A separate Lean probe executed via `lake env lean --run /dev/stdin` rejected trailing junk,
trailing commas in objects and arrays, malformed/top-level types, a deeply nested
escaped-equivalent duplicate key, a global `tcId` duplicate, and a wrong result payload type; it
accepted the original keyGen pair.

The following production and independent gates passed on the frozen tree:

```text
python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: 9 committed artifacts; 15 server artifacts; 12/120, 72/624,
  36/504 (+72/-432); 144 cells/24 positive

SLHDSA_ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
SLHDSA_ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS, both exact checkouts and deterministic regeneration verified

lake build HashSigTest
  PASS (2743 jobs)

lake exe slhdsa_acvp_parser
  positive PASS (16); negative PASS (47); runtime PASS (63)

./scripts/update-lib.sh
  PASS (`No update necessary`)

./scripts/slhdsa/validate.sh --docs-only
  PASS

./scripts/slhdsa/validate.sh
  PASS, including builds, parser execution, policy audit, compiled-initializer rejection,
  update-lib, isolation, KAT, and C13 gates

bash -n scripts/slhdsa/validate.sh scripts/slhdsa/*.sh
JSON/JSONL syntax checks
TeX build to /tmp
  PASS; TeX emitted only minor overfull-box warnings
```

The parser's native-build warnings concern inherited absent ML-KEM/ML-DSA/Falcon/hash native
submodules and do not affect this pure executable. The full build's unrelated existing `sorry`
warnings were not introduced by S01.

The provenance checker is offline in normal mode. Its committed artifact hashes, included source
metadata, cell ordering/uniqueness, positive evidence IDs, and optional-checkout regeneration
checks are hard-coded and fail closed for the data it actually covers. In
`/tmp/s01-checker-probe.ls0lGp`, flipping the first coverage cell from covered to uncovered caused
the copied checker to reject the committed artifact hash.

Complete docs/matrices/session/findings/TCB/assumptions/declarations/report inspection confirmed
that F-015/F-016 stay open, COV-005 stays missing/S10, the SP draft remains non-normative, and S00
r9 is only propagated to evidence r9 accepted. The four test-only ACVP declaration rows are
accurately marked `load_bearing:false` and do not support a construction/security theorem claim.

Passing gates do not cure the four findings below.

## Findings

### S01-R0-001 — HIGH — the normal gate does not fail closed over controlling remote authority metadata

`check_reference_manifest()` requires only that a remote entry contain some `revision` key, then
skips it. `check_s01_metadata()` hard-checks the FIPS pin and part of the SP pin/profile, but it does
not check the exact ACVP-Server v1.1.0.38 compatibility-boundary revision. The provenance checker
does not read that reference-manifest entry. It also does not check the SP profile's
`publication_status`, although initial-draft status is a controlling authority boundary.

Exact reproduction used a copied tree under `/tmp/s01-docsgate-mutation.dlZkTo/repo`: change the
v1.1.0.38 revision `85f8742965b2691862079172982683757d8d91db` to forty zeroes in
`docs/slhdsa/reference-manifest.json`, and change the profile's `publication_status` from
`initial-public-draft` to `final`, then run:

```text
./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (...)
SLH-DSA docs-only validation: PASS
```

Thus the advertised normal gate accepts both a false exact compatibility pin and a false authority
status. This is a substantive fail-closed validation/provenance defect even though the frozen
metadata currently happens to be correct.

### S01-R0-002 — MEDIUM — `SP800-230-128-24` conflates two different scopes

The sole profile identifier `SP800-230-128-24` is used for a `scope.md` target and exact matrix
covering all six SHA2/SHAKE category 1/3/5 IPD sets. The same identifier is defined by D-002 as
“SP800-230 SHA2-128-24 ... a legacy reduced profile” and labels coverage/proof rows for the current
single SHA2-128-24 implementation. The prose discloses that current code implements only the
reduced set, but the identifier still has two incompatible referents: a six-set authority profile
and a one-set current-code subprofile. A matrix row bearing it therefore cannot unambiguously state
which scope it covers. This is a profile/traceability defect, not a demand that current code already
implement all six sets.

### S01-R0-003 — LOW — the pinned ACVP Internet-Draft has a false bibliography year

`docs/slhdsa/report/references.bib` cites `draft-livelsberger-acvp-slh-dsa-01` with
`year = {2026}`. The exact pinned root at protocol commit
`892fd14710f3a7edbea230d0aecc5511e0257f8e` declares `revdate: 2024-06-25`. A 2026 checkout or
review date does not change the dated `-01` draft's publication year. The source ledger correctly
pins the repository revision, so the bibliography should not substitute the evidence-collection
year for the cited document's date.

### S01-R0-004 — LOW — four untracked S01 JSON artifacts fail the comprehensive whitespace check

Plain `git diff --check` passes only because every affected S01 JSON file is untracked. Explicitly
checking every untracked file exposed S01-generated blank lines at EOF:

```text
for f in $(git ls-files --others --exclude-standard); do
  git diff --no-index --check -- /dev/null "$f" 2>&1 || true
done

HashSigTest/SLHDSA/ACVP/fixtures/positive-prehash-coverage.json:866: new blank line at EOF.
HashSigTest/SLHDSA/ACVP/fixtures/provenance.json:309: new blank line at EOF.
HashSigTest/SLHDSA/ACVP/fixtures/siggen-schema-slice.json:214: new blank line at EOF.
HashSigTest/SLHDSA/ACVP/fixtures/sigver-schema-slice.json:170: new blank line at EOF.
```

Byte inspection confirms extra terminal LFs. The two trailing-whitespace reports in immutable
historical `S00-adversarial-review-r5.md` are inherited and excluded from this S01 finding; they
must not be rewritten. The four ACVP JSON reports are new S01 polish defects and show that the
session's ordinary `git diff --check` did not account for untracked scope.

## Verdict rationale

The frozen authority values, source bytes, derived counts, matrix, parser behavior, and major build
and runtime gates reproduce. However, S01 has a fail-closed authority-metadata gap, an ambiguous
SP 800-230 profile identity, a false bibliography year, and four untracked whitespace defects.
The acceptance rule is zero findings, so passing functional gates cannot offset them.

S01 fails independent review r0. S02 must not start. No implementation repair was made; the issues
require a repair session followed by a fresh independent re-review.
