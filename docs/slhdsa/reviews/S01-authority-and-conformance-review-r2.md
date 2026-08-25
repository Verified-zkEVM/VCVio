# S01 adversarial re-review r2 — authority and pinned conformance anchors

Verdict: **FAIL**

Reviewer: independent S01 r2 authority/conformance review sub-agent; not an S00/S01 implementer,
the S01 r0 reviewer, or the S01 r1 reviewer

Reviewed commit/tree: VCVio `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
`codex/sphincsplus-formalization`, plus the frozen uncommitted S01 r2 tree

Date: 2026-08-24

Independence statement: I did not design, implement, or repair S01, and I did not perform S01 r0 or
r1. The implementation remained frozen. All probes, isolated mutation trees, derived manifests,
and TeX output were confined to `/tmp/slhdsa-r2-review.4CqiLx`; this verdict is my only repository
edit.

## Required checks

- [x] Immutable S01 r0 and r1 reviews remain byte-identical and canonically `FAIL`.
- [x] The repair remains within S01 scope and changes no `HashSig/**` construction/security file.
- [x] The normal offline gate validates the exact complete FIPS 205 manifest record, including
  identity, kind, root, locator, hash, size, final status, 2024-08-13 date, and primary-normative
  authority.
- [x] Genuine sibling FIPS PDF byte/hash verification remains independent of metadata validation.
- [x] Built-in and independent mutations of FIPS date and authority fail with the real sibling
  reference bundle enabled.
- [x] Current server, compatibility boundary, protocol, SP IPD, and profile records are exact-key,
  exact-value pins for every claimed controlling classification field.
- [x] The canonical scope table has one exact six-set non-normative authority/profile row and one
  exact, distinct single-set current-code row, with no duplicate or contradictory profile ID.
- [x] The exact historical r0/r1 review files are hash-locked, and the exact F-031 line is the sole
  allowed current occurrence of the deprecated identifier in the roots actually scanned.
- [ ] Every active S01 source and canonical matrix is guarded against deprecated IDs or incorrect
  profile associations; see S01-R2-001.
- [ ] The parser support and canonical report make no inaccurate conformance/traceability claim;
  see S01-R2-002.
- [x] F-034/F-035 and the review/session/index/report/matrix state honestly record r1 `FAIL`, r2
  `PENDING` before this verdict, and S02 blocked.
- [x] F-015/F-016 remain `OPEN`, and COV-005 remains `missing`, S10-owned, and pending.
- [x] Offline and optional provenance, parser runtime, builds, update-lib, docs-only/full validation,
  syntax, nominal whitespace/scope/hygiene, and TeX gates pass on the frozen pending tree.

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

The sole tracked diff is the four-line `slhdsa_acvp_parser` executable declaration in
`lakefile.lean`. All untracked implementation paths are under `HashSigTest/SLHDSA/ACVP/**`,
`docs/slhdsa/**`, and `scripts/slhdsa/**`. Separate tracked and untracked path enumeration found no
change under `HashSig/**`. Independently rebuilding the documented 22-file HashSig source manifest
gave the pinned composite:

```text
d6b782daf07d6cbd4a9a3542361ff22176db139d14e98911abe512a9546101b7  -
```

The r2 artifact had one canonical `PENDING` verdict and SHA-256
`b88992d599feebce2639e6e339858f7933ab691e2a8630577741ae37ebbac4d7` before reviewer
authorship. The two immutable S01 failures remain exactly:

```text
ab4f964df0bc5f48840c46c8ddffc35f4e15e5f1ea85123a2aae6ab1c46b1a76  \
  docs/slhdsa/reviews/S01-authority-and-conformance-review.md
9b369bba832820d114a041db30bfd16d10289851da3a507484f8f259572047ec  \
  docs/slhdsa/reviews/S01-authority-and-conformance-review-r1.md
```

Each has exactly one canonical `FAIL` verdict. S00 r0-r8 remain `FAIL`, S00 r9 remains `PASS`, and
no historical finding or disposition was rewritten.

## Prior-finding dispositions

| Prior finding | Independent r2 disposition |
|---|---|
| S01-R0-001 | **Repaired for the cited authority defects and the complete current record set.** Both normal checkers use literal complete-record equality for FIPS, current server, compatibility, protocol, and SP IPD/profile metadata. Independent on-disk mutations of every claimed controlling field reject in both gates. |
| S01-R0-002 | **Current canonical identifiers are separated, but the advertised all-active-surface guard remains incomplete.** The exact scope rows and directly gated prose are correct; deprecated-ID and contradictory-current-association mutations outside the narrow checks pass. See S01-R2-001. |
| S01-R0-003 | **Repaired.** The pinned root says `draft-livelsberger-acvp-slh-dsa-01` and `revdate: 2024-06-25`; the bibliography says 2024 and 25 June 2024, and the normal gates pin both. |
| S01-R0-004 | **The four cited JSON EOF defects and all currently added S01 files are clean, but the comprehensive scope claim is incomplete.** Direct checks found only the two exact immutable S00 r5 hard breaks. However, files under the session's broader `HashSigTest/SLHDSA/**` allowed scope but outside `ACVP/**` escape the active-file scanner; see S01-R2-001. |
| S01-R1-001 | **Repaired.** Complete FIPS record equality rejects date, authority, identity, kind, root, locator, hash, size, status, missing-field, and extra-field mutations. The real sibling PDF independently matches its pinned hash. |
| S01-R1-002 | **The exact canonical scope table and its two original reconflation mutations are repaired; the broader cross-surface regression guard remains incomplete.** Incorrect associations can be added to an active source or substituted into the canonical coverage row without failing. See S01-R2-001. |

The acceptance rule is zero findings. The partial dispositions for R0-002, R0-004, and R1-002 do
not permit S01 acceptance.

## Authority and provenance reproduction

### Final FIPS 205 and SP 800-230 IPD

The supplied FIPS source reproduced independently:

```text
sha256sum /home/alh/SPHINCS/NIST.FIPS.205.pdf
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d

wc -c /home/alh/SPHINCS/NIST.FIPS.205.pdf
1055752

pdfinfo /home/alh/SPHINCS/NIST.FIPS.205.pdf
Title: Stateless Hash-Based Digital Signature Standard
Author: National Institute of Standards and Technology
Pages: 61
```

The official NIST CSRC page identifies FIPS 205 as final and published 13 August 2024. Independent
PDF text extraction reproduced Table 2's paired SHA2/SHAKE tuples
`(n,h,d,h',a,k,lg_w,m,category,pk,sk,sig)`:

```text
128s: (16,63,7,9,12,14,4,30,1,32,64,7856)
128f: (16,66,22,3,6,33,4,34,1,32,64,17088)
192s: (24,63,7,9,14,17,4,39,3,48,96,16224)
192f: (24,66,22,3,8,33,4,42,3,48,96,35664)
256s: (32,64,8,8,14,22,4,47,5,64,128,29792)
256f: (32,68,17,4,9,35,4,49,5,64,128,49856)
```

Each tuple has both the SHA2 and SHAKE member, for exactly twelve rows. Sections 10 and 11 also
reproduced the 255-byte context limit, pure/pre-hash domain bytes, four displayed DER OIDs and
digest sizes, deterministic/hedged `opt_rand` semantics, and SHA2/SHAKE primitive grammars.

The draft source reproduced independently:

```text
sha256sum /tmp/NIST.SP.800-230.ipd.pdf
62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e

wc -c /tmp/NIST.SP.800-230.ipd.pdf
282069

pdfinfo /tmp/NIST.SP.800-230.ipd.pdf
Title: NIST SP 800-230 ipd: Additional SLH-DSA Parameter Sets for Limited-Signature Use Cases
Pages: 12
```

The official NIST page identifies the 13 April 2026 Initial Public Draft, six additional category
1/3/5 parameter sets, and a strict `2^24` signatures-per-key cap; it is not final and the sets are
not approved for general-purpose use. Independent Table-1 extraction reproduced the six rows as
paired SHA2/SHAKE tuples `(n,h,d,h',a,k,lg_w,m,category,pk,sig)`:

```text
128-24: (16,22,1,22,24,6,2,21,1,32,3856)
192-24: (24,21,1,21,25,9,3,32,3,48,7752)
256-24: (32,21,1,21,25,12,2,41,5,64,14944)
```

The committed profile contains exactly those six ordered rows, status/date/hash/size/cap, the
non-normative Boolean, and distinct six-set/legacy identifiers.

### ACVP server, protocol, and compatibility pins

The two optional checkouts were clean and at the declared current commits:

```text
git -C /tmp/slhdsa-s01-acvp-server rev-parse HEAD
975de31eb83d87039ec88934fdc47d8c312b892d

git -C /tmp/slhdsa-s01-acvp-protocol rev-parse HEAD
892fd14710f3a7edbea230d0aecc5511e0257f8e
```

Official GitHub API reproduction on 2026-08-24 gave tag v1.1.0.43 =
`975de31eb83d87039ec88934fdc47d8c312b892d` and tag v1.1.0.38 =
`85f8742965b2691862079172982683757d8d91db`, both direct commit refs. The former is the current
sample-generator release; the latter is used only as the documented external-interface
server-format compatibility boundary, not a protocol-schema revision.

The protocol root declares `draft-livelsberger-acvp-slh-dsa-01` and `revdate: 2024-06-25`. Its root
is 2,258 bytes with SHA-256
`d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061`. Independent
`sha256sum` over the root plus the 15 exact section files in C-locale path order gave:

```text
bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54  -
```

All 15 section sizes/hashes and all 15 server artifact sizes/hashes matched the committed
provenance record. The server's registration discriminants remain algorithm `SLH-DSA`, modes
`keyGen`/`sigGen`/`sigVer`, and revision `FIPS205`.

GitHub's official issue/PR records showed issue #469 `open`, PR #471 `open`, `merged:false`, and
the PR body explicitly says the sample JSON files were not regenerated. The docs therefore
correctly preserve the measured limitation and do not treat the proposed change as current data.

### Exact-record mutation matrix

I cloned the exact base into `/tmp`, overlaid the frozen S01 tree, enabled the genuine sibling
bundle, changed one field per tree, and invoked both the standalone provenance gate and the normal
docs gate. Both rejected every one of these 33 authority/profile mutations for the intended exact
record, byte, or profile mismatch:

```text
FIPS: id, kind, root, locator, hash, size, final status, date, authority,
      missing locator, extra key
current server: release, commit, authority, extra key
protocol: document identity, document date, authority, missing root hash
compatibility boundary: tag, commit, scope/authority, extra key
SP profile: status, date, authority, profile ID, cap, hash, tuple,
            normative Boolean, missing field, extra key
```

Representative real-sibling commands/results were:

```text
publication_date: 2024-08-13 -> 2099-01-01
SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: FAIL: S01: exact controlling authority record mismatch for fips205

authority: primary-normative -> secondary-untrusted
python3 -B scripts/slhdsa/check-acvp-provenance.py
SLH-DSA ACVP provenance: FAIL: reference manifest final FIPS 205 authority record mismatch

compatibility release: v1.1.0.38 -> v1.1.0.39
SLH-DSA harness check: FAIL: S01: exact controlling authority record mismatch for
  acvp-server-v1.1.0.38

SP first-row h: 22 -> 23
SLH-DSA harness check: FAIL: S01: SP 800-230 profile must match the exact six
  non-normative IPD tuples
```

The two checkers express their own literal expected dictionaries; mutation helpers deep-copy and
change the actual data passed to production validators. Independent on-disk mutations confirm that
the built-in self-tests are not passing tautologically.

## License, normalized copies, projections, counts, and positive cells

Whitespace-normalized comparison of the upstream README license with `NOTICE-NIST.txt` reproduced
the complete three-paragraph NIST notice. The fixture then gives NIST acknowledgement, exact
repository/release/commit, and a dated description of each normalization/projection.

Independent byte comparisons showed exactly these upstream-to-vendored size transitions:

```text
keyGen registration: 438 -> 439
sigGen registration: 1776 -> 1777
sigVer registration: 1730 -> 1731
keyGen prompt: 32454 -> 32455
keyGen expectedResults: 45192 -> 45193
```

Each vendored file equals the complete upstream bytes followed by exactly one LF, with no other
byte change. The docs accurately call this final-LF normalization rather than byte identity.

An independent script that did not import either production checker joined full prompt/results by
`(tgId,tcId)`, checked global uniqueness and exact order, compared every projected group/test
record to upstream, and derived:

```text
keyGen: 12 groups / 120 tests
sigGen: 72 groups / 624 tests
sigVer: 36 groups / 504 tests = 72 positive + 432 negative

sigGen external/preHash false: 144; true: 144
sigGen external/pure    false:  84; true:  84
sigGen internal         false:  84; true:  84

sigGen selected: (19,157), (20,164), (31,271), (55,469), (56,476), (67,583)
sigVer selected: (19,253), (19,256), (19,257), (19,258), (20,268), (31,422)
```

The registration axes are ordered unique 12-by-12 sets/hashes. The independently generated
144-cell cross product is byte-for-record equal to the committed cell list. Its 24 positive pairs
are:

```text
SHA2-128s:  SHA2-512 tg20/tc268;       SHAKE-256 tg20/tc271
SHAKE-128s: SHA2-512/224 tg26/tc351;   SHA2-512/256 tg26/tc364
SHA2-128f:  SHA2-256 tg2/tc25;         SHA3-384 tg2/tc19
SHAKE-128f: SHA2-512/256 tg8/tc111;    SHA3-512 tg8/tc107
SHA2-192s:  SHA2-256 tg22/tc307;       SHA2-512/256 tg22/tc302
SHAKE-192s: SHA3-256 tg28/tc386;       SHA3-384 tg28/tc388
SHA2-192f:  SHA2-512 tg4/tc52;         SHA2-512/224 tg4/tc53
SHAKE-192f: SHA3-384 tg10/tc139;       SHA3-512 tg10/tc129
SHA2-256s:  SHA2-512 tg24/tc331;       SHA3-384 tg24/tc328
SHAKE-256s: SHA2-512/256 tg30/tc417;   SHA3-256 tg30/tc412
SHA2-256f:  SHA2-224 tg6/tc72;         SHA2-384 tg6/tc84
SHAKE-256f: SHA2-224 tg12/tc167;       SHA2-256 tg12/tc168
```

Every parameter set has exactly two positive and ten missing cells. SHA3-224 and SHAKE-128 have no
positive cell anywhere. The docs correctly exclude the 432 negative cases from evidence of correct
pre-hash OID/digest binding.

## Parser and schema review

Manual inspection found the strict parser to be a small Apache-2.0 adaptation with the original
Gabriel Ebner/Marc Huisinga attribution and Nicolas Consigny's dated modification attribution. Its
recursive helpers are private, it compares decoded keys before tree-map insertion at every nesting
depth, and it requires EOF. Literal and escaped-equivalent duplicate keys cannot overwrite values.

The typed schema requires exact object keys/types/discriminants, `isSample=true`, positive and
globally unique IDs, nonempty groups/tests, exact prompt/result joins, all twelve FIPS rows, exact
seed/key/signature widths, 1..8192-byte messages, 0..255-byte external contexts, exact
internal/external and pure/preHash conditional fields, deterministic/randomness rules, and all
twelve ACVP hash enums. SigVer accepts only exact and plus/minus-one signature lengths from the
pinned sample, and a positive result requires exact width. No new `sorry`, axiom, unsafe/extern,
runtime override, initializer, or production `HashSig` declaration was introduced.

The native suite passed 16 positive and 47 negative cases. A separate 13-check Lean runtime probe
accepted a minimal valid prompt and an 8192-byte message, and rejected trailing junk, object/array
trailing commas, top/deep escaped-equivalent duplicates, duplicate global `tcId`, duplicate `tgId`,
unknown group keys, empty tests, zero-byte messages, and 8193-byte messages.

This functional behavior does not cure the inaccurate assurance label in S01-R2-002.

## Profile, history, and nominal hygiene mutation evidence

The exact ordered `scope.md` table currently contains the six unique rows
`FIPS205-12`, `SPX-TW-ABS`, `SP800-230-IPD-6SET`, `LEGACY-SHA2-128-24`, `C13-ETH`, and
`DEPLOY-TBD`. The six-set and one-set cells match their exact expected prose. Independent isolated
mutations to the deprecated ID, legacy-ID conflation, a duplicate row, missing ID, reordered/wrong
ID, and a contradictory scope cell all failed under the normal docs gate.

Changing one byte in either historical S01 failure rejected on its complete-file hash. Adding the
deprecated ID to a current file under `ACVP/**`, to the report, or to a new file under
`docs/slhdsa/**` rejected. Altering the exact ledger or report association marker rejected. Adding
a terminal blank line to a new file under `docs/slhdsa/**` rejected. These 13 non-authority
on-disk mutations demonstrate that the paths actually covered by the implementation behave as
documented.

Independent direct whitespace checking over every current file under `docs/slhdsa/**`,
`scripts/slhdsa/**`, and `HashSigTest/SLHDSA/ACVP/**` found only the two preserved Markdown hard
breaks at `S00-adversarial-review-r5.md:{7,32}`. JSON, JSONL, Bash syntax, and Python execution were
clean, and no Python debris remained. The wider allowed-scope escape in S01-R2-001 is distinct from
the nominal cleanliness of the current tree.

## Executed nominal gates

All required nominal commands passed on the frozen pending tree:

```text
python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: 9 committed; 15 server; 12/120, 72/624, 36/504 (+72/-432); 144/24

SLHDSA_ACVP_SERVER_ROOT=/tmp/slhdsa-s01-acvp-server \
SLHDSA_ACVP_PROTOCOL_ROOT=/tmp/slhdsa-s01-acvp-protocol \
  python3 -B scripts/slhdsa/check-acvp-provenance.py
  PASS: exact checkouts, artifacts, projections, counts, and protocol composite verified

lake build HashSigTest
  PASS: 2743 jobs

lake exe slhdsa_acvp_parser
  PASS: 16 positive + 47 negative = 63 runtime cases

./scripts/update-lib.sh
  PASS: No update necessary

./scripts/slhdsa/validate.sh --docs-only
  PASS

./scripts/slhdsa/validate.sh
  PASS: 3007-job repository build, 2744-job HashSig build, 2743-job HashSigTest build,
  parser runtime, policy audit, ordinary/IR compiled fixture, generated umbrella,
  isolation gates, and both legacy KATs

bash -n scripts/slhdsa/validate.sh
jq JSON/JSONL checks
git diff --check
direct tracked-and-untracked whitespace checks
  PASS, subject only to the two exact immutable S00 r5 hard breaks

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-r2-review.4CqiLx/tex slhdsa-formalization-audit.tex
  PASS: five-page PDF; minor overfull boxes only
```

Full-validation warnings are the documented missing-native-submodule stubs, unrelated repository
admissions, and the existing allowlisted HashSig security admission. None is introduced by S01.

The current administrative surfaces honestly record r0/r1 `FAIL`, F-030 through F-035 as
`REMEDIATED-PENDING-REVIEW`, r2 `PENDING` before this verdict, F-015/F-016 `OPEN`, COV-005
`missing`/S10/pending, and S02 blocked. The NIST data is otherwise consistently called sample JSON,
not a certificate or independently approved KAT corpus.

## Findings

### S01-R2-001 — MEDIUM — profile and active-file regression guards still have blind spots

The r2 checker scans `docs/slhdsa/**`, `scripts/slhdsa/**`, and
`HashSigTest/SLHDSA/ACVP/**` for deprecated identity use and whitespace. The S01 session's allowed
fixture/parser/test-support scope is the broader `HashSigTest/SLHDSA/**`. In addition, current-ID
association checking requires a few exact positive markers but does not reject an additional
contradictory association or contradictory content in the canonical matrix row. This falls short of
the handoff's all-active-surface and matrix-association claims.

Four independent exact-base isolated mutations demonstrate the gaps. First, append a comment using
the deprecated six-set/single-set identifier to the existing active S01-allowed test source outside
`ACVP/**`:

```text
/tmp/slhdsa-r2-review.4CqiLx/current-source-outside-acvp/
HashSigTest/SLHDSA/Sha2KAT.lean:
  + -- SP800-230-128-24

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (...)
SLH-DSA docs-only validation: PASS
```

Creating `HashSigTest/SLHDSA/new-profile-note.md` with the same identifier also passed. Thus the
recursive scan and comprehensive-whitespace claim do not cover the full recorded S01-allowed test
scope or future untracked files there.

Second, add a contradictory association using only the two current identifiers inside a scanned
current source:

```text
/tmp/slhdsa-r2-review.4CqiLx/contradictory-current-association/
HashSigTest/SLHDSA/ACVP/Schema.lean:
  + SP800-230-IPD-6SET is the single current-code set;
    LEGACY-SHA2-128-24 is the six-set profile.

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA docs-only validation: PASS
```

Third, keep COV-014's profile-column identity but change its claim/evidence/notes to say it is the
single implemented legacy profile:

```text
/tmp/slhdsa-r2-review.4CqiLx/contradictory-matrix-cell/
docs/slhdsa/matrices/coverage.csv, COV-014:
  claim -> Single current-code parameter set
  evidence -> Current one-set implementation complete
  notes -> This is the legacy implementation profile

SLHDSA_REFERENCE_ROOT=/home/alh/SPHINCS ./scripts/slhdsa/validate.sh --docs-only
SLH-DSA docs-only validation: PASS
```

These are not Unicode or spelling tricks: they use the exact deprecated/current identifiers and
ordinary files inside the recorded S01 scope. The canonical content is presently correct, but the
normal gate still accepts the profile regressions it claims to exclude. F-035 and parts of F-031/
F-033 therefore remain only partially disposed.

### S01-R2-002 — MEDIUM — canonical assurance surfaces contain inaccurate conformance and profile claims

This finding has two directly observable documentation defects.

#### Schema-only parser described as conformance evidence

`HashSigTest/SLHDSA/ACVP/ParserTests.lean:13-15` says:

```text
The positive gate parses the committed NIST sample fixtures. The separate negative gate exercises
fail-closed syntax, schema, conditional-field, width, identifier, and pairing behavior. These tests
are conformance evidence only; they make no construction or security claim.
```

The implemented suite parses sample JSON and validates transport/schema constraints. It does not
run a Lean SLH-DSA implementation against keyGen, sigGen, or sigVer answers, and the canonical
coverage matrix correctly records COV-005 implementation conformance as `missing`, required, and
owned by S10. `docs/slhdsa/README.md` and the S01 session also say that these anchors make no
implementation-conformance claim.

Calling the schema-only tests “conformance evidence” without the limiting “future” or
“schema-format” qualification is therefore an affirmative assurance claim inconsistent with the
actual test and canonical status. The following exact scan isolates the sole active statement:

```text
rg -n -i 'conformance evidence|implementation conformance' \
  HashSigTest/SLHDSA/ACVP docs/slhdsa --glob '!reviews/**'
HashSigTest/SLHDSA/ACVP/ParserTests.lean:15:are conformance evidence only; ...
docs/slhdsa/README.md:... strict sample-schema parser anchors do not claim implementation conformance.
docs/slhdsa/matrices/coverage.csv:COV-005,...,missing,...,S10,pending,...
```

Passing parser and provenance gates cannot turn schema validation into implementation-conformance
evidence. This violates the required no-conformance-overclaim check.

#### Canonical report miscounts its profile matrix

The report abstract at lines 19-22 enumerates six separate profiles: FIPS205-12, SPX-TW-ABS, the
six-set SP IPD authority profile, the one-set legacy current implementation, C13-ETH, and the future
deployment profile. The exact canonical `scope.md` table also contains six ordered rows. Yet the
report's profile section says at line 48:

```text
Present the five-profile decision matrix.
```

This is a direct traceability inconsistency in the canonical report. It is not a TeX rendering
problem: the five-page report builds successfully with that false count.

## Verdict rationale

The r2 repair materially improves authority validation: complete exact FIPS/server/protocol/
compatibility/SP records, genuine local FIPS bytes, all official hashes, counts, joins, projections,
24 positive cells, strict parsing, and every major nominal gate reproduce. The exact original
authority and canonical-scope mutations now fail closed.

However, the active-surface/profile-association guard still accepts concrete regressions inside the
recorded S01 scope, a schema-only parser suite overstates its assurance role as conformance evidence,
and the canonical report miscounts six profiles as five. The review protocol makes any issue a
failure. S01 r2 therefore **FAILS** independent review, and S02 must not start. No implementation
repair was made.
