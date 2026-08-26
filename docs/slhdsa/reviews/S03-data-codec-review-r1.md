# S03 independent data and codec review r1

Verdict: **FAIL**

Blocking findings: **1**
Nonblocking findings: **0**

Reviewer: fresh independent S03 r1 reviewer; not the S03 implementer, repair implementer, or
initial S03 reviewer.
Review date: 2026-08-26.
Reviewed repair commit: `dab93b0a88543f21c5eb6e52c36d5fcc29c4e75e`, parent
`963a3e7dd425b8a8c9bb9e2e91b73868f6918768`, relative to exact accepted S02 commit
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b3` and the immutable initial S03 FAIL artifact
`reviews/S03-data-codec-review.md`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the accepted S02 state, the exact cumulative S03 and repair diffs, every changed Lean declaration,
the pinned FIPS source and profile, matrices, tests, generated inventory, compiled policy, initial
FAIL artifact, findings dispositions, and S04 bootstrap. I did not implement the candidate or its
repairs. Temporary reviewer Lean probes were removed after execution. This r1 FAIL artifact is my
only repository edit from the reviewed clean state.

## Decision summary

All five initial S03 findings pass substantive re-review. Parameter lookup now carries the hash
family and has an exact all-twelve constructor inverse. Algorithm 3 now has total modulo
reconstruction, an in-range corollary, and a checked-encoder connection. ADRS serialization now
reconstructs the structured six-field value under exact bounds and connects canonical bytes,
checked encoding, decoding, and semantic wire values. The declaration matrix and permanent
26-root compiled probe agree exactly. Codec documentation now consistently describes transparent,
exact-width aliases.

The exact candidate nevertheless contains one active documentation defect. The S03 session claims
the proved law as `toInt (toByte len x) = x % 256^len`, reversing the actual `toByte x len`
arguments. This is not merely alternate notation: for `len = 1` and `x = 2`, the written left side
evaluates to `1` while its right side evaluates to `2`. The definition, compiled theorem, FIPS
notation, declaration matrix, specification, report, and every proof use the correct order.

The independent-review protocol permits PASS only with zero issues, including documentation
issues. S03 therefore remains unaccepted and S04 remains blocked. Repair the one active sentence,
rerun the complete gates, preserve this FAIL artifact, and obtain a fresh
`S03-data-codec-review-r2.md` review of the exact successor tree.

## Exact reviewed state, history, and scope

Before reviewer authorship:

```text
HEAD    dab93b0a88543f21c5eb6e52c36d5fcc29c4e75e
parent  963a3e7dd425b8a8c9bb9e2e91b73868f6918768
subject fix(slhdsa): resolve S03 data codec review findings
tree    e679950fe081c65dcaef470a0702f2e8bc48a2c5
status  clean
```

Both repair and cumulative diffs pass `git diff --check`. The repair diff is confined to the four
S03 Lean modules, focused runtime tests, the failed-review/findings and successor-routing records,
declaration inventory and its exact probe/harness/wrapper routing, reference pin, report, and other
S03 documentation. The cumulative S03 diff remains within the S03 source/test allowlist,
umbrella/Lake/wrapper routing, documentation and matrices, and the accepted/failed review artifacts.
It does not edit the frozen legacy security theorem, accepted S02 security modules, primitive
implementations, WOTS/XMSS/FORS/hypertree/construction algorithms, external API, ACVP parser, or
vector fixtures.

The immutable initial S03 review reproduces as:

```text
8a21aa42caec8659ed4cafc8e56ddb1dfcc0ec0559f6bc9b678ad3e65a07586b  S03-data-codec-review.md
```

The repaired source and inventory hashes are:

```text
1007bb07f8f92317d743da852ac7acd4e47130d3fb35ce2f8d8988d2236efa9a  Params.lean
abdfdd9700a7c0c05e69886c212d79b05833bb753688be23fd98102d93ed0516  Encoding.lean
df07d534138596d54ee3a817574f2e15de49c732ba2ef8c6b2b8ff564359ee28  Address.lean
065d6ee23a4ec93498e4411f66828037c7f216d2ab3b51f4865e3ba17973ea01  Codec.lean
ff9036ad12879610b0e99258ec3f14a3f8ea18c761f32408bc49e310a7fe847d  DataCodecTests.lean
4e27146a7bb1165b130e446d31cd1663016d53457e7db0efe219476f57029490  S03InventoryProbe.lean
3c1d200444122c00407ae6e789db3064c97603d57f9b7248d85f90a03031b25d  declarations.jsonl
```

Source and compiled scans found no new or moved `sorry`/`admit`, source or generated axiom,
explicit `unsafe`, `extern`, source `partial`/`partial_fixpoint`, initializer, runtime override,
noncomputable declaration, linter suppression, Extern import, or Interop import in the S03 changes.
The exact seven reviewed compiler helpers remain unchanged.

## Initial finding dispositions

### S03-001 / F-087 — substantive repair passes re-review

`ParameterSet.ofParams` now takes both `HashFamily` and `Params` and searches on their conjunction.
`ParameterSet.ofParams_profile` proves exact recovery for each constructor by cases. Independent
evaluation returned `true` for all twelve named rows, including every SHAKE row; the runtime test
compares the returned constructor itself and separately exercises paired-family selection and a
malformed row. The S04 family-selection input no longer aliases SHAKE to SHA2.

### S03-002 / F-088 — substantive repair passes re-review

`toByte` is a fixed-length reversal of bounded base-256 digits. `toInt_eq_ofDigits` bridges the
big-endian fold to `Nat.ofDigits`; `toInt_toByte_mod` proves
`toInt (toByte x len) = x % 256 ^ len`; `toInt_toByte` derives exact reconstruction under
`x < 256 ^ len`; and `toByteChecked_toInt` connects successful checked output to that identity.
The runtime suite distinguishes zero-width truncation, cross-byte values, the one-byte maximum,
and one-byte overflow. Reviewer evaluation reproduced `(0, 86, 1193046)` for widths zero, one, and
three on `0x123456`, plus acceptance of 255 and rejection of 256 at one byte.

### S03-003 / F-089 — substantive repair passes re-review

`Adrs.toVector` packages the full 32-byte structured serialization. `fromVector_toVector` proves
all six fields reconstruct under their 4/12/4/4/4/4-byte bounds;
`fromVector_toVector_of_isCanonical` derives those bounds from canonicality. `toWire`,
`decode_toBytes`, and `toWire_value` then connect canonical structured values to the rejecting
decoder and its semantic wire value. The tests exercise all seven type layouts at maximum full
field widths and retain unknown-type, padding, short/long, setter-range, and compressed-address
negative cases. Quantifiers and side conditions match the actual arithmetic and canonicality
boundaries; no impossible premise or carrier-only identity substitutes for structured recovery.

### S03-004 / F-090 — substantive repair passes re-review

DECL-040 through DECL-042 and DECL-044 through DECL-046 now record `[propext]`, matching compiled
output. The harness pins exact full source spans and axiom footprints for all 23 S03 declaration
rows. `S03InventoryProbe.lean` checks those roots plus three load-bearing supporting theorems,
giving 26 exact roots in total; the full wrapper invokes it permanently before the aggregate policy
audit. Both the permanent probe and the reviewer-specific explicit prints passed.

### S03-005 / F-091 — substantive repair passes re-review

`Codec.lean`, the specification, S03 session, report, and other active S03 prose now call
`PublicKeyBytes`, `SecretKeyBytes`, and `SignatureBytes` transparent exact-width aliases. No active
codec claim asserts nominal or definitional opacity. Historical wording remains only in the
byte-pinned immutable FAIL artifact and findings description, where it accurately records the old
defect.

## Primary-source and quantitative replay

The local primary source reproduced as:

```text
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d  NIST.FIPS.205.pdf
size: 1055752 bytes
title: Stateless Hash-Based Digital Signature Standard
pages: 61
status/date: final, 2024-08-13
```

Direct inspection of FIPS 205 Sections 4, 5, 9, and 11 reconfirmed the six paired Table 2 rows,
big-endian Algorithms 2--4, 4/12/4/12-byte full ADRS layout, seven type tags and padding layouts,
clear-on-type-change rule, and 1/8/1/12-byte SHA2 compression. The independently evaluated pairs
remain:

| pair | `(n,h,d,h',a,k,lgw)` | `(len1,len2)` | digest parts | `m` | `(pk,sk,sig)` |
| --- | --- | --- | --- | --- | --- |
| 128s | `(16,63,7,9,12,14,4)` | `(32,3)` | `(21,7,2)` | 30 | `(32,64,7856)` |
| 128f | `(16,66,22,3,6,33,4)` | `(32,3)` | `(25,8,1)` | 34 | `(32,64,17088)` |
| 192s | `(24,63,7,9,14,17,4)` | `(48,3)` | `(30,7,2)` | 39 | `(48,96,16224)` |
| 192f | `(24,66,22,3,8,33,4)` | `(48,3)` | `(33,8,1)` | 42 | `(48,96,35664)` |
| 256s | `(32,64,8,8,14,22,4)` | `(64,3)` | `(39,7,1)` | 47 | `(64,128,29792)` |
| 256f | `(32,68,17,4,9,35,4)` | `(64,3)` | `(40,8,1)` | 49 | `(64,128,49856)` |

Each row occurs once per SHA2/SHAKE family. Every approved denominator is positive, `h = h' * d`,
the digest parts sum to `m`, and the key/signature formulas equal the recorded widths. The legacy
reduced row remains outside the approved closed family. No new conformance vector is claimed; the
two inherited KATs remain legacy C-reference regressions only.

## Load-bearing declarations and axiom replay

I reviewed every changed definition and theorem in `Params.lean`, `Encoding.lean`,
`Address.lean`, and `Codec.lean`; every focused runtime case; direct and reverse usages under
`HashSig/**` and `HashSigTest/**`; the declaration rows; and the compiled probe. No helper chain uses
`False`, an empty target, impossible hypotheses, arbitrary distributions, or quantitative slack.

The explicit reviewer replay produced:

```text
ParameterSet.profile: []
ParameterSet.profile_sizes: [propext]
ParameterSet.wots_widths: [propext]
ParameterSet.ofParams_profile: []
ParameterSet.valid: [propext, Classical.choice, Quot.sound]
toInt_lt_pow: [propext, Classical.choice, Quot.sound]
toInt_eq_ofDigits: [propext, Quot.sound]
toInt_toByte_mod: [propext, Classical.choice, Quot.sound]
toInt_toByte: [propext, Classical.choice, Quot.sound]
toByteChecked_toInt: [propext, Classical.choice, Quot.sound]
decodeExact_encode: [propext]
base2b_bigEndian: [propext]
base2bChecked: [propext]
Adrs.isCanonical: [propext]
Adrs.fromVector_toVector: [propext, Classical.choice, Quot.sound]
Adrs.fromVector_toVector_of_isCanonical: [propext, Classical.choice, Quot.sound]
Adrs.decode: [propext]
Adrs.decode_encode: [propext]
Adrs.decode_toBytes: [propext, Classical.choice, Quot.sound]
Adrs.toWire_value: [propext, Classical.choice, Quot.sound]
decodePublicKey: [propext]
decodeSecretKey: [propext]
decodeSignature: [propext]
decodePublicKey_encode: [propext]
decodeSecretKey_encode: [propext]
decodeSignature_encode: [propext]
```

No completed root reports `sorryAx` or an axiom outside the exact standard allowlist.

## New finding

### S03-R1-001 — the S03 evidence record reverses the proved `toByte` arguments

Severity: **LOW**, blocking under the zero-finding protocol.

`docs/slhdsa/sessions/S03-data-widths-parameters-adrs-codecs.md:74` records the repair as:

```text
toInt (toByte len x) = x % 256^len
```

The actual public definition and compiled theorem use value first and width second:

```text
toByte (x len : ℕ)
toInt (toByte x len) = x % 256 ^ len
```

FIPS 205 Algorithm 3 likewise writes `toByte(x, n)`. Because both arguments are naturals, the
reversal still denotes a Lean term but asserts the wrong arithmetic relationship. Independent
execution with `len = 1` and `x = 2` produced `(1, 2)` for the written left and right sides. The
machine-readable declaration row has the correct theorem type, so the active session narrative
contradicts its own compiled evidence.

Required repair: change the session formula to
`toInt (toByte x len) = x % 256 ^ len`; register and disposition S03-R1-001 in the findings and
active review/session/successor records; preserve and byte-pin this r1 FAIL artifact; rerun the full
wrapper and report render; and obtain fresh independent r2 review of the complete exact repaired
tree. Do not mark F-087--F-091 fixed or unblock S04 until that review passes with zero findings.

## Reproduced commands and gates

Commands are classified as static audit, elaboration, runtime, or report rendering.

```text
git show -s --format='%H%n%P%n%s%n%T' dab93b0a
git diff --name-status a80e4d33..dab93b0a
git diff --name-status 963a3e7d..dab93b0a
git diff --check a80e4d33..dab93b0a
git diff --check 963a3e7d..dab93b0a
git status --short
  PASS (static exact identity, cumulative/repair scope, whitespace, and clean prestate).

sha256sum ../NIST.FIPS.205.pdf
pdfinfo ../NIST.FIPS.205.pdf
pdftotext -layout <focused FIPS pages> <temporary output>
  PASS (static primary-source identity and direct Sections 4/5/11 inspection).

lake env lean scripts/slhdsa/S03InventoryProbe.lean
  PASS (elaboration): 26 exact load-bearing roots.

lake env lean /tmp/S03R1IndependentProbe.lean
  PASS (reviewer-specific elaboration/execution): exact types and axiom prints, all twelve table
  evaluations and family-aware inverses, integer boundaries. The temporary probe was removed.

lake env lean /tmp/S03R1DocumentationCounterexample.lean
  PASS (reviewer-specific execution): `(1, 2)` exposes the active prose's reversed-argument law.
  The temporary probe was removed.

./scripts/slhdsa/validate.sh
  PASS (complete wrapper): documentation/provenance and mutation harness; 3,007-job repository,
  2,749-job HashSig, and 2,755-job HashSigTest builds; exact fresh 68-case parser runtime;
  S02/S03 probes; authoritative aggregate policy and ordinary/IR initializer fixture; generated
  umbrella; extern/interop isolation; both legacy positive/tamper KATs; and S03 runtime tests.

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s03-r1-tex slhdsa-formalization-audit.tex
  PASS (report rendering): seven pages, 326,134 bytes; box-layout warnings only.
```

The aggregate policy observed 28 HashSig modules, 2,010 owned constants, the exact seven permitted
compiler helpers, and transitive union `[propext, Classical.choice, Quot.sound, sorryAx]`, with
`sorryAx` confined to the frozen legacy security placeholder. Runtime execution printed:

```text
SLH-DSA-SHA2-128-24 KAT: PASS (valid signature accepted, tampered rejected)
SLH-DSA-C13 KAT: PASS (valid signature accepted, tampered rejected)
SLH-DSA S03 data/codec tests: PASS (12 profiles; endian, ADRS, rejection)
SLH-DSA full baseline validation: PASS
```

These successful gates establish the five substantive repairs but cannot override the
zero-finding stop rule.

## Final decision

Final result: **FAIL with one blocking and zero nonblocking findings**. All five initial technical
and traceability defects are substantively repaired, but the active S03 session misstates the
central reconstruction theorem by reversing its arguments. S03 is not accepted at
`dab93b0a88543f21c5eb6e52c36d5fcc29c4e75e`; S04 must not begin. Correct the one sentence and seek
record its disposition and routing, then seek a fresh r2 review of the exact repaired successor.
