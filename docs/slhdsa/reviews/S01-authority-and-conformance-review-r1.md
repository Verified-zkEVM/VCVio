# S01 adversarial re-review r1 — authority and pinned conformance anchors

Verdict: **FAIL**

Reviewer: independent S01 r1 authority/conformance review sub-agent; not an S00/S01 implementer
or the S01 r0 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r1 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01, and I did not perform S01 r0.
The implementation remained frozen. All probes, cloned mutation trees, and TeX output were confined
to `/tmp`; this verdict is my only repository edit.

## Required checks

- [x] The immutable S01 r0 review remains byte-identical and canonically `FAIL`.
- [x] The repair diff remains within S01 scope and changes no `HashSig/**` construction/security file.
- [x] Normal offline docs and provenance gates hard-pin the v1.1.0.38 compatibility commit and
  reject independent corrupt-commit mutations.
- [x] Normal offline docs and provenance gates require SP 800-230 `initial-public-draft` status and
  reject independent false-`final` mutations.
- [ ] All coupled FIPS, protocol, current-server, compatibility, IPD, and profile metadata are
  fail-closed: the FIPS publication date and authority classification are not checked.
- [x] `SP800-230-IPD-6SET` currently refers only to the six-set non-normative draft
  authority/profile surface.
- [x] `LEGACY-SHA2-128-24` currently refers only to the single current-code legacy subprofile.
- [ ] Scope, D-002, matrices, JSON, report, ledger, session, and gates reject reconflation: the
  current content is separated, but the normal gate accepts reintroduction of the old ID in the
  canonical scope table.
- [x] The pinned Internet-Draft bibliography identifies `-01` and its 25 June 2024 date/year.
- [x] Comprehensive whitespace validation covers tracked and untracked S01 files and rejects
  terminal blank lines; only the two exact historical S00 r5 hard-break lines are excluded.
- [x] All four S01 r0 findings have honest pending-review dispositions and S02 remained blocked
  before this verdict.
- [x] Offline and optional provenance, parser runtime, builds, update-lib, docs-only/full
  validation, syntax, whitespace/scope/hygiene, and TeX gates pass on the nominal frozen tree.

## Frozen state and review history

Before writing this verdict:

```text
git branch --show-current
codex/sphincsplus-formalization

git rev-parse HEAD
f1853af40da1efa11a71c2d7011996eebdbf6938

git status --short
 M lakefile.lean
?? HashSigTest/SLHDSA/ACVP/
?? docs/slhdsa/
?? scripts/slhdsa/
```

The tracked diff is the four-line `slhdsa_acvp_parser` executable declaration in `lakefile.lean`.
All untracked implementation paths are under the three listed S01 roots. Separate tracked and
untracked path checks found no path under `HashSig/**`, and the full `HashSig` source composite
remains the pinned baseline value. The r1 artifact had exactly one canonical `PENDING` verdict and
SHA-256 `84b1e42fe0196b9e2cf557998e34a8d92d153d3d651b7d4accfd7c27c322a49d`
before reviewer authorship.

The immutable r0 artifact remains exactly:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  \
  docs/slhdsa/reviews/S01-authority-and-conformance-review.md
```

It has one canonical `FAIL` verdict. S00 r0-r8 remain `FAIL`, S00 r9 remains the accepted `PASS`,
and no historical finding or disposition was rewritten.

## Prior-finding dispositions

| r0 finding | Independent r1 disposition |
|---|---|
| S01-R0-001 | **The two cited defects are repaired, but the broader required authority gate is still incomplete.** Both checkers now compare the exact v1.1.0.38 tag/commit and SP IPD status, and six non-tautological in-process mutations reject. Independent on-disk mutations also reject. However, the normal gate accepts false FIPS publication-date and authority-classification metadata; see S01-R1-001. |
| S01-R0-002 | **Current content repaired; regression guard incomplete.** Every active current surface uses the two new IDs consistently, and the old ID occurs only in historical finding text. Selected matrix rows and D-002 are checked. The normal gate nevertheless accepts reintroduction of the old ID in `scope.md`; see S01-R1-002. |
| S01-R0-003 | **Repaired.** The pinned source says `draft-livelsberger-acvp-slh-dsa-01` and `revdate: 2024-06-25`; the bibliography says 2024 and 25 June 2024. An independent 2026-year mutation is rejected. Checkout and evidence-observation dates remain separately labelled. |
| S01-R0-004 | **Repaired.** The four JSON files now end in exactly one LF, the comprehensive scanner covers tracked and untracked active roots, its exclusions are two exact `(path,line)` pairs in immutable S00 r5, and an independent terminal-blank-line mutation is rejected. |

Because the acceptance rule is zero findings, the partial dispositions for R0-001 and R0-002 do
not permit S01 acceptance.

## Authority and provenance reproduction

Independent local measurements gave:

| Authority | Reproduced evidence |
|---|---|
| Final FIPS 205 | 1,055,752 bytes; SHA-256 `8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d`; PDF title `Stateless Hash-Based Digital Signature Standard`; first matter says `Published: August 13, 2024` |
| SP 800-230 IPD | 282,069 bytes; SHA-256 `62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e`; 12 pages; Initial Public Draft, April 2026, public-comment period beginning 2026-04-13 |
| ACVP-Server | clean local checkout at `975de31eb83d87039ec88934fdc47d8c312b892d`, exact tag v1.1.0.43 |
| Compatibility boundary | official repository tag `refs/tags/v1.1.0.38` resolves directly to commit `85f8742965b2691862079172982683757d8d91db`; used only for server-format compatibility |
| ACVP protocol | clean local checkout at `892fd14710f3a7edbea230d0aecc5511e0257f8e`; root declares Internet-Draft `draft-livelsberger-acvp-slh-dsa-01`, `revdate: 2024-06-25` |

The FIPS profile independently reproduces all twelve Table-2 rows and the exact key/signature
widths, 255-byte context bound, pure/pre-hash domains, four FIPS OID/digest records, and the exact
SHA2/SHAKE primitive grammars. The SP IPD table independently reproduces the six separate
SHA2/SHAKE category 1/3/5 rows, and the strict `2^24` signatures-per-key cap. The latter is a
non-normative draft profile, not a FIPS 205 profile or implementation claim.

All 15 server artifact sizes and SHA-256 values and all 15 protocol-section sizes and hashes matched
the committed provenance record. The protocol root is 2,258 bytes with SHA-256
`d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061`; independently rebuilding
the root-plus-sections manifest gave
`bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54`.

The three registration files and keyGen prompt/expected file each equal the complete upstream bytes
plus exactly one final LF. Their size transitions are respectively `438->439`, `1776->1777`,
`1730->1731`, `32454->32455`, and `45192->45193`; byte-prefix comparisons found no other change.
The complete three-paragraph NIST notice is preserved, followed by source acknowledgement and a
dated, specific modification notice.

Independent joins over the full pinned server files reproduced:

```text
keyGen: 12 groups / 120 tests, prompt/result IDs bijective
sigGen: 72 groups / 624 tests, prompt/result IDs bijective
sigVer: 36 groups / 504 tests, prompt/result IDs bijective; 72 positive / 432 negative
```

An independent prompt/result join over external/preHash sigVer produced 24 unique positive
`(parameterSet,hashAlg,tgId,tcId)` records, byte-for-record identical to the committed coverage
matrix. Each of the twelve parameter sets has exactly two positive cells and ten missing cells;
SHA3-224 and SHAKE-128 have zero positive cells globally. This confirms that negative cases are not
being used as OID/digest-binding evidence. Official issue #469 and PR #471 were both still open;
the PR says sample JSON is not regenerated.

Nominal provenance commands passed:

```text
python3 -B scripts/slhdsa/check-acvp-provenance.py
SLHDSA_ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
SLHDSA_ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
  python3 -B scripts/slhdsa/check-acvp-provenance.py
```

Both report 9 committed artifacts, 15 server artifacts, full-suite counts
`12/120, 72/624, 36/504 (+72/-432)`, 144/24 coverage, and four rejected in-process authority
mutations; the optional run also verifies both exact checkouts and deterministic regeneration.

## Parser and schema review

The strict parser is a minimal Apache-2.0 adaptation of Lean's parser with the original Gabriel
Ebner/Marc Huisinga attribution and Nicolas Consigny's modification notice. Its recursive helpers
are private. It tests a decoded object key before insertion at every nesting depth and requires EOF,
so literal and escaped-equivalent duplicates cannot be overwritten by the tree map.

The schema uses exact keys and discriminants, positive and globally unique IDs, nonempty groups and
tests, exact prompt/result bijections, all twelve FIPS rows, exact seed/key/signature widths,
1..8192-byte messages, 0..255-byte external contexts, exact internal/external and pure/preHash
conditional fields, deterministic/additional-randomness rules, and all twelve protocol hash names.
SigVer accepts only the pinned sample's exact and plus/minus-one signature lengths and requires exact
width for a positive result. No new `sorry`, axiom, `unsafe`, `extern`, runtime override,
initializer, or production-library import was found.

The native suite passed 16 positive and 47 negative cases. A separate stdin Lean probe accepted a
minimal valid keyGen prompt and rejected trailing junk, object/array trailing commas, deep and
top-level escaped-equivalent duplicates, and a globally duplicated `tcId` (seven independent
rejections total).

## Repair mutations and nominal gates

Inspection showed the built-in mutation tests are non-tautological: `copy.deepcopy` changes the
actual dictionaries passed to the same production validators. `check-harness.py` rejects corrupt
compatibility commit and false IPD status mutations; `check-acvp-provenance.py` independently rejects
those two document mutations plus the same two mutations in provenance controlling-source data.

In exact-base isolated trees with the frozen S01 allowlist overlaid, these independent mutations
failed for the intended reason:

```text
reference-manifest v1.1.0.38 revision -> 40 zeroes
  validate.sh --docs-only: FAIL: exact ACVP-Server v1.1.0.38 compatibility boundary mismatch
  check-acvp-provenance.py: FAIL: reference manifest v1.1.0.38 compatibility pin mismatch

sp800-230-ipd-profile publication_status -> final
  validate.sh --docs-only: FAIL: SP 800-230 profile status/cap mismatch
  check-acvp-provenance.py: FAIL: SP 800-230 IPD controlling profile metadata mismatch

ACVP bibliography year 2024 -> 2026
  validate.sh --docs-only: FAIL: ACVP bibliography identity/date mismatch

append one LF to positive-prehash-coverage.json
  validate.sh --docs-only: FAIL: terminal blank line
```

The comprehensive whitespace code recursively scans `docs/slhdsa`, `scripts/slhdsa`, and
`HashSigTest/SLHDSA/ACVP`, independent of Git tracking. It requires one final LF, rejects terminal
blank lines and trailing whitespace, and excludes only
`S00-adversarial-review-r5.md:{7,32}`. Direct `git diff --no-index --check` over every untracked file
found only those two preserved Markdown hard breaks. The four formerly defective JSON tails are
now `] LF } LF` or `} LF } LF`, not double LF. No Python debris exists.

The complete nominal gates passed:

```text
lake build HashSigTest                         PASS, 2743 jobs
lake exe slhdsa_acvp_parser                   PASS, 16 + 47 = 63 runtime cases
./scripts/update-lib.sh                       PASS, no update necessary
./scripts/slhdsa/validate.sh --docs-only      PASS
./scripts/slhdsa/validate.sh                  PASS
```

The full gate completed a 3,007-job repository build, 2,744-job HashSig build, 2,743-job
HashSigTest build, parser execution, both semantic policy audits including compiled IR, generated
umbrella check, extern/interop isolation, and both legacy runtime regressions. Warnings are the
documented missing-native-submodule stubs, unrelated repository admissions, and the single existing
HashSig security admission; none is introduced by S01.

All JSON and JSONL records parsed, Bash syntax passed, and the declaration spans/import boundaries
passed the harness. TeX built a five-page PDF under `/tmp/slhdsa-r1-review.0ll6bp/tex`; only minor
overfull-box warnings remain. `git diff --check` is clean for tracked content.

Current administrative surfaces honestly record r0 `FAIL`, F-030 through F-033 as
`REMEDIATED-PENDING-REVIEW`, r1 `PENDING` before this verdict, F-015/F-016 `OPEN`, COV-005
`missing` with S10 ownership, and S02 blocked. Sample JSON is never called a certificate,
independently approved vector corpus, or implementation-conformance result.

## Findings

### S01-R1-001 — HIGH — FIPS authority metadata is not fail-closed

`reference-manifest.json` claims exact FIPS 205 metadata including
`publication_date: 2024-08-13` and `authority: primary-normative`. The source ledger repeats that
date and relies on the normative classification. `validate_s01_authority_metadata()` checks the
FIPS hash, size, and `final` status, but not either field. `check_reference_manifest()` verifies the
local PDF hash but ignores metadata besides the path/hash mechanics. The provenance checker does not
validate the FIPS entry at all.

Exact reproduction used isolated exact-base trees at
`/tmp/slhdsa-r1-review.0ll6bp/git2-bad-fips-date` and
`/tmp/slhdsa-r1-review.0ll6bp/git2-bad-fips-authority`, with the frozen S01 allowlist overlaid and
the real sibling bundle enabled:

```text
publication_date: 2024-08-13 -> 2099-01-01
SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (...)
SLH-DSA docs-only validation: PASS

authority: primary-normative -> secondary-untrusted
SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (...)
SLH-DSA docs-only validation: PASS
```

The PDF bytes remain genuine in both probes, proving the defect is specifically unchecked claimed
authority metadata rather than a missing source bundle. This violates the required coupled FIPS
`final/hash/size/date` pin and the ledger's authority classification.

### S01-R1-002 — MEDIUM — profile separation is correct in content but not fail-closed across active docs

Current active content is clean: `SP800-230-IPD-6SET` names the six-set draft authority/profile,
`LEGACY-SHA2-128-24` names the one-set current-code profile, and `SP800-230-128-24` appears only in
the historical F-031 description and immutable review history. The checker locks selected CSV rows,
D-002's mention of both IDs, the SP profile JSON, and provenance.

It does not inspect the canonical `scope.md` table, source-ledger prose, report prose, or all active
surfaces for the old ID or contradictory use. This contradicts `validation.md`'s statement that the
normal gates require the two distinct profile identifiers and leaves the r0 defect regressible.

Exact reproduction used `/tmp/slhdsa-r1-review.0ll6bp/git2-old-id-scope`, an exact-base isolated tree
with the frozen S01 allowlist and real sibling reference bundle. I changed only the six-set row's
identifier in `scope.md`:

```text
SP800-230-IPD-6SET -> SP800-230-128-24
SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (...)
SLH-DSA docs-only validation: PASS
```

The mutated canonical scope then simultaneously had the old ambiguous six-set identifier and the
separate `LEGACY-SHA2-128-24` current-code row. A similar single-line mutation replacing the six-set
row with `LEGACY-SHA2-128-24` also passed. Therefore the current repair is textually correct but its
advertised cross-surface regression guard is incomplete.

## Verdict rationale

The exact four r0 examples are repaired in current content, and the authority bytes, projections,
counts, coverage matrix, parser behavior, build/runtime gates, whitespace hygiene, and status
language reproduce. However, the normal gate still accepts false controlling FIPS metadata and
accepts profile-ID reconflation in the canonical scope document. Those are substantive new
fail-closed findings under the explicitly required r1 checks.

The acceptance rule is zero findings. S01 r1 therefore **FAILS** independent review. S02 must not
start. No implementation repair was made; preserve this artifact and create a fresh r2 review only
after both findings are repaired and all gates are rerun.
