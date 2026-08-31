# S04 independent primitive review

Verdict: **FAIL**

Blocking findings: **1**
Nonblocking findings: **0**

Reviewer: fresh independent S04 reviewer; not the S04 implementer.
Review date: 2026-08-31.
Reviewed commit: `7f115c0ed5e6342d20db902c163b319b6b0df43d`, parent and exact S04 launch
`4ce439ae38aea4f97189db8cd8781a62faaf8459`, tree
`7d31e74f9d16967f9214b130ad25c80bf93aec86`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the accepted S03 r2 review and launch, the exact cumulative S04 diff, every changed Lean declaration
and helper, the session/plan/validation records, source ledger and reference manifest, specification,
blueprint, findings, all matrices, focused tests and vector projection, compiled policy, and report.
I directly inspected the pinned primary sources and did not rely on the implementer's narrative for
technical conclusions. Reviewer-only differential and axiom probes were confined to `/tmp`; the
rendered report output was removed after inspection. I did not implement or repair the candidate.
This FAIL artifact is my only repository edit from the reviewed clean state.

## Decision summary

The primitive implementation is technically sound in the reviewed scope. Direct source and code
inspection found correct SHA-256/SHA-512 padding, schedules, constants, rounds, input bounds, HMAC
key normalization and block widths, MGF1 counters and bounds, SHAKE256 domain/rate/absorb/squeeze,
all six FIPS 205 grammars for each family, all twelve profile selections and result widths, the
checked compressed-address domain, exact conversions, and fail-closed total behavior. Independent
Python differential execution matched the Lean implementation across padding, key-length, MGF1
truncation, absorb-rate, and multi-block squeeze boundaries. All focused builds, runtime suites,
axiom probes, documentation checks, the full frozen wrapper, and report rendering pass.

Those successes are insufficient under the zero-finding protocol. Four active SHAKE256 runtime
oracles have expected bytes embedded in `PrimitiveTests.lean` but no corresponding record in the
required `PrimitiveVectors/vectors.json` projection: the 272-byte empty-message squeeze and the
135-, 136-, and 137-byte `0x61` absorb cases. The projection contains only empty-message outputs of
32 and 137 bytes and the 200-byte `0xa3` input case. The three absorb-boundary values have no active
source locator or independent-derivation classification at all, while active source-ledger, test,
and report prose says every case and expected byte string is identified or pinned. The values are
correct when independently recomputed; the defect is missing mandatory evidence and an active
overclaim, not a SHAKE algorithm error.

Any issue, including documentation overclaim, requires FAIL. S04 remains unaccepted and S05 must
not start. Repair requires a successor commit and a fresh `S04-primitives-review-r1.md`; this review
does not make the repair.

## Exact reviewed state, history, and scope

Before reviewer authorship:

```text
HEAD    7f115c0ed5e6342d20db902c163b319b6b0df43d
parent  4ce439ae38aea4f97189db8cd8781a62faaf8459
subject feat(slhdsa): implement FIPS primitive families
tree    7d31e74f9d16967f9214b130ad25c80bf93aec86
status  clean
```

The parent is exactly the S04 launch commit containing the accepted S03 r2 artifact; its parent is
the exact accepted S03 repair `79b42bf9662dcfe4336401096e9bd4ae0ed924d3`. The cumulative diff
from launch changes 29 expected files: the primitive abstraction, SHA2 and Keccak foundations, a
new FIPS concrete module, umbrella/Lake/wrapper routing, focused tests and primitive projection,
the S04 inventory probe, and S04 documentation/matrices/report. Both launch-to-candidate
`git diff --check` and the candidate's clean-state check pass.

The diff does not edit security definitions, WOTS, XMSS, FORS, hypertree, scheme construction,
external APIs, the ACVP parser/runner, or inherited KAT fixtures. The small harness and wrapper edits
only register the S04 files, source-tree pin, focused probe, and test target. Source and diff scans
found no new or moved `sorry`/`admit`, source or generated axiom, explicit `unsafe`, `extern`, source
`partial`/`partial_fixpoint`, initializer, runtime override, noncomputable declaration, linter
suppression, Extern import, Interop import, or `native_decide`. The one inherited security
placeholder and exact seven compiler-generated recursion helpers are unchanged.

## Primary-source and pin review

Every supplied primary source and projection reproduced its manifest byte count and SHA-256:

| source | bytes | SHA-256 |
| --- | ---: | --- |
| FIPS 205 final | 1,055,752 | `8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d` |
| FIPS 180-4 update 1 | 833,315 | `0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82` |
| FIPS 202 | 1,459,683 | `1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e` |
| FIPS 198-1 | 129,454 | `67661ba1407b391c799ff407471de18f36697af51d78a777e817c067ac30da23` |
| RFC 8017 text | 154,696 | `1e72dc473d18df3fc5598cdc12795a9f18f36f1aef15abc23a55eb0d58151d11` |
| SHA byte-vector archive | 4,909,729 | `929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8` |
| SHAKE byte-vector archive | 2,116,268 | `debfebc3157b3ceea002b84ca38476420389a3bf7e97dc5f53ea4689a16de4c7` |
| HMAC byte-vector archive | 452,025 | `418c3837d38f249d6668146bd0090db24dd3c02d2e6797e3de33860a387ae4bd` |
| HMAC-SHA-256 example | 97,884 | `ebb45f0b987ce07fc433cc5598c8948f127d6d0e1ebcbfd1af5a27944856c786` |
| HMAC-SHA-512 example | 109,794 | `391a955dfd884bcb3b310cb25679c36e3c7fbd058332cb3571b2a9e8fb63c09f` |
| SHAKE256 empty example | 251,349 | `d736c1a93eb6440e1e6b640402e31ea5258281b2b9237f84ea0ba4186518fc59` |
| SHAKE256 1600-bit example | 316,397 | `f4226f5c72914e5d2b331812c5973d8d685c8af1ccb97c2a3a2fd1c02fd173d1` |
| committed vector projection | 8,950 | `b086e6e79d07e6fc64dbf6fad56219015d96f7c2c7a22fbfd4d699b27d6406ec` |

The SHA and SHAKE archive member hashes also reproduce. The 28-file source-tree composite is
`39990d89588702c566869e8262b145cc83b56ef125988ff842e0eb5c744aff59` under the exact
documented GNU `sha256sum` recipe.

Direct inspection established the following correspondence:

- FIPS 180-4 appends one bit, enough zeroes to reach 448 modulo 512 or 896 modulo 1024, and a
  64- or 128-bit big-endian bit length. The code's 64-/128-byte blocks, IVs, 64/80 constants,
  schedules, rotations, Boolean functions, and feed-forward rounds match. The checked byte limits
  are exactly `< 2^61` and `< 2^125`, equivalent to the standard's bit-length domains.
- FIPS 198-1 uses 64-byte and 128-byte blocks for SHA-256 and SHA-512, hashes keys longer than the
  block, zero-pads shorter results, and applies `0x36`/`0x5c`. Both implementations match, including
  exact-block and hash-then-pad behavior.
- RFC 8017 Appendix B.2.1 permits `maskLen <= 2^32 hLen`, serializes each counter in four-byte
  big-endian form, concatenates hashes for counters zero through the last required block, and takes
  the leading requested bytes. The checked maxima are exactly `2^32 * 32` and `2^32 * 64`; the
  zero-length, second-block, truncation, and `maximum + 1` behavior matches.
- FIPS 202 defines SHAKE256 with capacity 512, rate 1088 bits or 136 bytes, and the SHAKE delimited
  suffix represented by `0x1f` for byte-oriented absorb. The code absorbs a full extra padded block
  on rate-aligned input, merges the terminal `0x80` when one byte remains, emits the initial state
  first, and applies one new Keccak-f[1600] permutation before each later squeeze block. SHA3
  `0x06` and Ethereum Keccak `0x01` remain distinct.
- FIPS 205 Section 11 uses a 22-byte SHA2 compressed address consisting of the one-byte layer,
  eight-byte tree, one-byte type, and final twelve bytes, and a full 32-byte address for SHAKE.
  The six SHA2 and six SHAKE concatenation grammars and their family-specific digest choices agree
  with Sections 11.1 and 11.2.

The notice correctly distinguishes credited NIST government material from IETF-copyrighted RFC
text and disclaims endorsement/certification. Recorded SHA, HMAC, and SHAKE records are official
example/CAVP projections; MGF1 cases are explicitly derived regression evidence; all-profile
fingerprints are explicitly independently derived composition evidence. Finding S04-001 concerns
additional active runtime cases that fall outside those otherwise accurate classifications.

## Lean declaration and helper review

I inspected every changed definition/theorem and its callers, not only the eleven inventory roots.
No helper chain establishes a positive claim through `False`, an empty target, an impossible
hypothesis, an arbitrary distribution, or quantitative slack.

`Primitives.ByteLaws` adds exactly injectivity of `yToBytes`, separated from the structural bundle.
`yToBytes_eq_iff` uses injectivity in the forward direction and `congrArg` in the reverse direction;
the fixed-width concrete families use identity encodings, so their witnesses are valid.

In `Concrete.Sha2`, big-endian parsing and serialization, wrapping `UInt32`/`UInt64` arithmetic,
SHA-512 padding, compression, HMAC key processing, MGF1 block enumeration, truncation, and checked
bounds are correct. The unchecked compatibility functions remain total outside the normative input
domain, while the checked functions state and reject the exact standard boundaries; active text
does not claim the unchecked wraparound domain is normative.

In `Concrete.Keccak`, the lane order, rho/pi tables, 24 round constants, theta/rho/pi/chi/iota
steps, little-endian lane absorb/squeeze, rate padding, and repeated squeeze are correct. Zero output
executes zero blocks; outputs of 136, 137, 272, and 273 bytes use the expected state transitions.

In `Concrete.FIPS`:

- `Sha2Address.ofAdrs` requires full canonicality, a one-byte layer, and an eight-byte tree.
  `compressSha2Checked_eq` and `bytes_toList` connect the proof-carrying adapter exactly to the
  existing 22-byte checked and concrete serialization.
- SHA2 `F` and `PRF` always use SHA-256 and the 64-byte prefix. `H` and `T_l` use SHA-256 at `n=16`
  and SHA-512 with the 128-byte prefix at `n=24/32`. `PRF_msg` makes the corresponding HMAC choice.
  `H_msg` hashes `R || PK.seed || PK.root || M` and applies the matching MGF1 to
  `R || PK.seed || inner`, returning exactly `m` bytes.
- All six SHAKE functions use SHAKE256, the full 32-byte address where required, and exact leading
  `n` or `m` bytes. `approvedPrimitives` dispatches on the closed profile family, producing all six
  SHA2 and six SHAKE bundles with the required choices.
- `byteArrayPrefixChecked` rejects a short source. `byteArrayPrefixOrZero` never retains a partial
  digest; it returns exactly `n` zero bytes on failure. Every invalid SHA2 address is rejected by
  the checked entry points and maps to the exact all-zero node in the pre-existing total bundle.
  Accepted cases preserve exact widths throughout.

The manual declaration inventory's populated spans, types, dependencies, reverse-use anchors, and
axiom fields were checked against source and compiled output. Some rows are deliberately not an
exhaustive dependency export; active F-018 and TCB-009 explicitly classify the complete inventory
as manual/bootstrap and forbid a completeness claim. I therefore do not misclassify an omitted
transitive/helper edge as an additional S04 defect. All facts the S04 rows do assert are true.

## Axiom and policy replay

The permanent eleven-root probe reproduced exactly:

```text
SLHDSA.Primitives.ByteLaws.yToBytes_eq_iff: []
SLHDSA.Concrete.Sha2Address.compressSha2Checked_eq:
  [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.Sha2Address.bytes_toList:
  [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.sha2Primitives: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.shakePrimitives: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.approvedPrimitives: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.sha2Primitives_byteLaws: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.shakePrimitives_byteLaws: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.approvedPrimitives_byteLaws: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.Sha2.sha512: [propext, Classical.choice, Quot.sound]
SLHDSA.Concrete.Keccak.shake256: [propext, Quot.sound]
```

A broader reviewer-specific probe printed changed SHA2/SHAKE helpers, checked bounds, address
adapter/conversion helpers, all twelve grammar functions/bundles, dispatch, and byte-law witnesses.
Every root used a subset of exactly `[propext, Classical.choice, Quot.sound]`; none used `sorryAx`
or a nonstandard axiom. The full compiled policy audit observed 29 HashSig modules and 2,139 owned
constants, retained the exact seven reviewed compiler helpers, and retained the exact union
`[propext, Classical.choice, Quot.sound, sorryAx]`, with `sorryAx` confined to the inherited security
placeholder.

## Boundary and adversarial execution

The focused suite covers the official SHA-256 padding neighbors at 55/56 bytes, SHA-512 neighbors
at 111/112 bytes, complete input blocks, SHA input rejection boundaries, HMAC short and long keys,
MGF1 zero/second-block/truncation/wrap rejection, SHAKE output rate crossings, input rate crossings,
domain separation, canonical and malformed SHA2 addresses, output widths, and all twelve exact
profile fingerprints.

I separately compared Lean output byte-for-byte with Python 3 `hashlib`/`hmac` over 111 output
records. Inputs included SHA-256/SHA-512 lengths 0, 1, 54--65, 100, 111--113, 127--129, 200, and
255; HMAC key lengths 0, 1, 63--65, 100, 127--129, and 200; MGF1 zero, block, and truncation lengths
through 273; SHAKE outputs 0, 1, 31--33, 63--65, 100, 135--137, 271--273; and SHAKE inputs 0, 1,
134--137, 200, and 271--273. `diff -u` was empty. Independent recomputation also matched both
derived MGF1 cases and all twelve recorded
`SHA256(F || H || T_l || PRF || PRF_msg || H_msg)` fingerprints.

Address probes accepted the canonical maximum permitted compressed widths, rejected noncanonical
padding/type layouts, layer `256`, and tree `2^64`, and confirmed the four checked SHA2 operations
agree with their exact FIPS input construction on accepted addresses. Short prefix conversion
rejects and its total counterpart returns the exact requested all-zero vector.

## Finding

### S04-001 — active SHAKE boundary vector oracles are absent from the required projection

Severity: **HIGH**.

`PrimitiveTests.lean:147-155` embeds a 272-byte empty-message SHAKE256 expected value, and
`PrimitiveTests.lean:160-168` embeds three 32-byte expected values for 135, 136, and 137 repetitions
of byte `0x61`. None is a record in `PrimitiveVectors/vectors.json`. A structural query over the
projection returns:

```text
empty output length 272: false
0x61 absorb length 135: false
0x61 absorb length 136: false
0x61 absorb length 137: false
```

The only projected SHAKE cases are empty input with output lengths 32 and 137, and 200 repetitions
of `0xa3` with output length 64. The pinned NIST empty-message example contains a long XOF stream
from which the 272-byte prefix can be checked, but the committed projection neither identifies that
case nor records its expected bytes. More importantly, the three `0x61` absorb-boundary cases have
no active source, locator, classification, method/tool/version, or independent derivation record.

This contradicts the test header at lines 15--16, which directs reviewers to the projection for
exact hashes, case identifiers, classifications, and expected bytes; the source ledger at lines
59--64, which says adjacent absorb-rate cases identify their independent derivation; and the report
at lines 116--121, which says the projection pins every source/member/case. It also violates the S04
preflight and vector gate requiring every primitive-vector case to carry exact provenance, mode,
expected result, and licensing/classification before supporting a claim. The normal harness
byte-pins and schema-checks the projection but does not compare its case set against every expected
literal in the Lean runtime suite, which is why all automated gates pass.

Independent recomputation with Python `hashlib.shake_256` confirms all four embedded values, so no
algorithm correction is indicated. Required repair: add exact records for all four cases, including
the precise source/member/case locator where official or the reproducible independent-derivation
method/tool/version where derived, expected bytes, algorithm/mode, input/output lengths,
classification, and applicable notice/license boundary. Then correct any active completeness claim
to the exact recorded scope, deliberately update the projection manifest/hash and validation pins,
rerun every S04 gate, and request a fresh full review. Do not relabel derived values as NIST vectors.

## Documentation, matrices, and report

Apart from S04-001, the session, plan, validation text, source pins, manifest, specification,
blueprint, findings dispositions, coverage/proof-obligation/assumption/TCB/declaration matrices,
and report agree with the Lean implementation and reviewed scope. F-007/PO-007 accurately remain
pending review at this failed boundary; F-093/F-094 and COV-015/PO-017 describe executable
primitive evidence without claiming construction correctness, ACVP certification, or a
mathematical refinement. F-015, F-016, and F-018 remain open. No successor construction or security
claim is activated.

The TeX report renders successfully to eight pages. Its box-layout warnings are cosmetic. The one
substantive report defect is the same S04-001 completeness overclaim, not a second independent
finding.

## Reproduced commands and gates

Commands are classified as static audit, elaboration/build, runtime, or report rendering.

```text
# Static history/scope/hygiene
git show -s --format='%H%n%P%n%s%n%T' 7f115c0e
git diff --name-status 4ce439ae..7f115c0e
git diff --check 4ce439ae..7f115c0e
git status --short --untracked-files=all
PASS: exact candidate/parent/tree; allowed 29-file scope; whitespace clean; clean state

# Static source/vector reproduction
sha256sum <all pinned source files and vectors.json>
wc -c <all pinned source files and vectors.json>
LC_ALL=C sha256sum HashSig/SLHDSA/*.lean HashSig/SLHDSA/C13/*.lean \
  HashSig/SLHDSA/Concrete/*.lean HashSig/SLHDSA/Security/*.lean | sha256sum
PASS: every manifest hash/size and source-tree composite reproduced

# Focused elaboration/build
lake build HashSig.SLHDSA.Concrete.FIPS
lake build HashSigTest.SLHDSA.PrimitiveTests
PASS

# Focused runtime
lake exe slhdsa_primitive_tests
SLH-DSA S04 primitive tests: PASS (SHA2/SHAKE vectors; 12 profile grammars)

# Exact and broad elaborated axiom probes
lake env lean scripts/slhdsa/S04InventoryProbe.lean
S04 declaration/axiom probe: PASS (11 exact load-bearing roots)
lake env lean /tmp/S04ReviewerAxioms.lean
PASS: all reviewed roots within the standard axiom allowlist; no sorryAx

# Independent differential runtime
lake env lean --run /tmp/S04ReviewerDifferential.lean
python3 /tmp/s04_reviewer_differential.py
diff -u <Lean output> <Python output>
PASS: 111 records; empty diff

# Documentation/provenance/schema gate
./scripts/slhdsa/validate.sh --docs-only
SLH-DSA docs-only validation: PASS

# Full frozen build, policy, isolation, regressions, probes, and runtimes
./scripts/slhdsa/validate.sh
SLH-DSA full baseline validation: PASS

# Report rendering
cd docs/slhdsa/report
latexmk -pdf -interaction=nonstopmode -halt-on-error slhdsa-formalization-audit.tex
PASS: eight-page PDF; cosmetic box warnings only
```

The full wrapper includes repository-wide `lake build`, `lake build HashSig`, and
`lake build HashSigTest`; fresh parser/schema execution and artifact binding; source and compiled
policy mutations; S02/S03/S04 inventory probes; generated umbrella, extern, and interop isolation;
both inherited regression KATs; S03 data/codec runtime; and the S04 primitive runtime. Every
component passed. Automated success does not cure S04-001 because the projection-to-runtime case
completeness relation is not currently gated.

## Verdict and successor condition

Verdict: **FAIL**, with one blocking HIGH finding and zero nonblocking findings. The reviewed Lean
primitive implementation and primary-source correspondence have no identified technical defect,
but the mandatory vector-evidence record is incomplete and active documentation overclaims it.
S04 is not accepted at `7f115c0ed5e6342d20db902c163b319b6b0df43d`. S05 remains blocked
until S04-001 is repaired and a fresh independent r1 review returns zero findings.
