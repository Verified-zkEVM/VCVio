# S03 independent data and codec review r2

Verdict: **PASS**

Blocking findings: **0**
Nonblocking findings: **0**

Reviewer: fresh independent S03 r2 reviewer; not the S03 implementer, repair implementer, or either
prior S03 reviewer.
Review date: 2026-08-31.
Reviewed repair commit: `79b42bf9662dcfe4336401096e9bd4ae0ed924d3`, parent
`dab93b0a88543f21c5eb6e52c36d5fcc29c4e75e`, tree
`10124708f15ba80ccd8a964d6692a09d26104d5b`, relative to exact accepted S02 commit
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b` and the two immutable S03 FAIL artifacts.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the accepted S02 state, the S03 session/plan/validation records, the exact cumulative S03 diff,
every changed Lean declaration and helper, both prior S03 FAIL artifacts, the pinned primary FIPS
source and source ledger, matrices, tests, generated inventory, compiled policy, report, and
successor bootstrap. I did not implement or repair the candidate. Reviewer probes and rendered
report output were confined to `/tmp`. This r2 PASS artifact is my only repository edit from the
reviewed clean state.

## Decision summary

The exact candidate repairs S03-R1-001: the active S03 session now states the proved value-first
law `toInt (toByte x len) = x % 256 ^ len`, matching the Lean definition, compiled theorem,
declaration matrix, specification, report, tests, and FIPS 205 Algorithm 3. The two naturals are no
longer reversed in active evidence.

I independently replayed the complete cumulative S03 review, not just that one-line repair. All
five initial findings remain substantively fixed. Family-aware parameter lookup recovers all twelve
constructors exactly. Big-endian integer conversion proves the total modulo law, its in-range
corollary, and checked-encoder reconstruction. ADRS serialization reconstructs the six structured
fields under their exact widths and connects canonical structured values, checked bytes, rejecting
decoding, and semantic wire values. Declaration rows and the permanent compiled probe agree on
exact spans and axiom footprints. Fixed-width key and signature carriers are consistently described
as transparent exact-width aliases.

Direct primary-source inspection confirms the Table 2 parameters and derived sizes, Algorithms
2--4 byte/bit order, the full and compressed ADRS widths, all seven type layouts and zero padding,
and the clear-on-type-change rule. Focused builds and probes, reviewer-specific edge and maximum
width probes, the authoritative policy audit, runtime tests, both inherited regression KATs, full
repository validation, documentation/provenance checks, isolation checks, and the rendered report
all pass. No source, proof, test, traceability, documentation, or claim-accuracy issue remains in
S03. S03 is accepted at the exact reviewed commit above and may serve as the predecessor for S04.

## Exact reviewed state, history, and scope

Before reviewer authorship:

```text
HEAD    79b42bf9662dcfe4336401096e9bd4ae0ed924d3
parent  dab93b0a88543f21c5eb6e52c36d5fcc29c4e75e
subject fix(slhdsa): address S03 r1 review blocker
tree    10124708f15ba80ccd8a964d6692a09d26104d5b
status  clean
```

The final repair changes active S03 documentation and routing only. Both the final repair and the
complete cumulative diff from accepted S02 pass `git diff --check`. The cumulative diff is confined
to the S03 data/codec source and tests, umbrella/Lake/wrapper routing, documentation and matrices,
the two immutable review artifacts, and the documentation-only S04 bootstrap. It does not edit the
frozen legacy security theorem, accepted S02 security sources, primitive implementations,
WOTS/XMSS/FORS/hypertree or construction algorithms, external API, ACVP parser, or vector fixtures.

The immutable S03 FAIL artifacts reproduce byte-for-byte from their introducing revisions:

```text
8a21aa42caec8659ed4cafc8e56ddb1dfcc0ec0559f6bc9b678ad3e65a07586b  S03-data-codec-review.md
0d728bf15cca3ebc2c9402b777b30a0c6de41b35f44eb2309c6b828812e4b6ba  S03-data-codec-review-r1.md
```

The reviewed history consists of the S03 payload commits `9331fa65` and `caefbda5`, the S04
documentation bootstrap `963a3e7d`, the substantive S03 repair `dab93b0a`, and the final prose
repair `79b42bf9`. Direct and reverse use searches covered every changed public declaration/helper
under `HashSig/**`, `HashSigTest/**`, and `scripts/slhdsa/**`.

Source and compiled scans found no new or moved `sorry`/`admit`, source or generated axiom,
explicit `unsafe`, `extern`, source `partial`/`partial_fixpoint`, initializer, runtime override,
noncomputable declaration, linter suppression, Extern import, or Interop import in the S03 changes.
The exact seven reviewed compiler helpers remain unchanged.

## Prior finding replay

### S03-001 / F-087 — fixed and independently verified

`ParameterSet.ofParams` takes both `HashFamily` and `Params`; it searches on their conjunction, and
`ParameterSet.ofParams_profile` proves exact recovery for every constructor. Independent evaluation
returned the original constructor for all twelve named profiles, correctly distinguished each
SHA2/SHAKE pair, rejected malformed input, and kept the legacy reduced record outside the approved
family. The runtime test compares constructors rather than only their shared numeric parameters.

### S03-002 / F-088 — fixed and independently verified

`toByte` produces a fixed-length big-endian base-256 representation. `toInt_eq_ofDigits` connects
the fold to `Nat.ofDigits`; `toInt_toByte_mod` proves
`toInt (toByte x len) = x % 256 ^ len`; `toInt_toByte` proves exact reconstruction under
`x < 256 ^ len`; and `toByteChecked_toInt` connects successful checked encoding to that identity.
Reviewer execution on `0x123456` produced `[]`, `[0x56]`, and `[0x12, 0x34, 0x56]` at widths zero,
one, and three, with decoded values `0`, `86`, and `1193046`; width one accepts 255 and rejects 256.

### S03-003 / F-089 — fixed and independently verified

`Adrs.toVector` contains the complete 32-byte structured serialization. `fromVector_toVector`
reconstructs all six fields under exact 4/12/4/4/4/4-byte bounds, and
`fromVector_toVector_of_isCanonical` obtains those bounds from canonicality. `toWire`,
`decode_toBytes`, and `toWire_value` connect canonical structured values to checked encoding,
rejecting decoding, and the semantic wire value. Independent execution covered every canonical
type at maximum field widths, all seven roundtrips, unknown tags, every required padding mutation,
short/long input, setter range, and compressed-address behavior.

### S03-004 / F-090 — fixed and independently verified

DECL-040 through DECL-042 and DECL-044 through DECL-046 record `[propext]`, matching compiled
output. All 23 S03 declaration rows have exact full source spans and exact declared axiom
footprints. The permanent `S03InventoryProbe.lean` checks those roots plus three load-bearing
supporting theorems, for 26 exact roots; the full wrapper invokes it before the aggregate audit.
Both the permanent probe and a broader reviewer-specific print replay pass.

### S03-005 / F-091 — fixed and independently verified

`PublicKeyBytes`, `SecretKeyBytes`, and `SignatureBytes` are transparent exact-width aliases. The
source comments, specification, session, report, matrices, and active evidence use that accurate
description; none claims nominal or definitional opacity. Historical wording occurs only where the
immutable initial FAIL artifact and findings history accurately record the former defect.

### S03-R1-001 / F-092 — fixed and independently verified

The active S03 session now records `toInt (toByte x len) = x % 256^len`. This matches the public
definition `toByte (x len : Nat)`, theorem `toInt_toByte_mod`, FIPS 205 Algorithm 3 notation
`toByte(x, n)`, the declaration inventory, specification, report, and tests. The reversed
`toByte len x` remains only where the immutable r1 FAIL artifact and active finding/report history
quote the former defect; no active mathematical claim uses it. The repaired session statement
therefore no longer contradicts the compiled evidence.

## Primary-source and quantitative correspondence

The primary source pin reproduces as:

```text
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d  NIST.FIPS.205.pdf
size: 1055752 bytes
title: Stateless Hash-Based Digital Signature Standard
pages: 61
status/date: final, 2024-08-13
```

Direct inspection of FIPS 205 Sections 4, 5, and 11 reconfirmed:

- full ADRS uses 4-byte layer, 12-byte tree, 4-byte type, and three final 4-byte words; changing
  type clears the final 12 bytes;
- type tags are exactly 0 through 6, and all implemented type-specific zero-padding positions
  match the standard's seven layouts;
- SHA2 compression selects 1/8/1/12 bytes for a total of 22;
- Algorithms 2 and 3 are big-endian base 256, Algorithm 3 takes value then width, and Algorithm 4
  consumes the leading bit string in big-endian order; and
- Table 2 has the six numeric rows below, each paired with SHA2 and SHAKE.

| pair | `(n,h,d,h',a,k,lgw)` | `(len1,len2)` | digest parts | `m` | `(pk,sk,sig)` |
| --- | --- | --- | --- | --- | --- |
| 128s | `(16,63,7,9,12,14,4)` | `(32,3)` | `(21,7,2)` | 30 | `(32,64,7856)` |
| 128f | `(16,66,22,3,6,33,4)` | `(32,3)` | `(25,8,1)` | 34 | `(32,64,17088)` |
| 192s | `(24,63,7,9,14,17,4)` | `(48,3)` | `(30,7,2)` | 39 | `(48,96,16224)` |
| 192f | `(24,66,22,3,8,33,4)` | `(48,3)` | `(33,8,1)` | 42 | `(48,96,35664)` |
| 256s | `(32,64,8,8,14,22,4)` | `(64,3)` | `(39,7,1)` | 47 | `(64,128,29792)` |
| 256f | `(32,68,17,4,9,35,4)` | `(64,3)` | `(40,8,1)` | 49 | `(64,128,49856)` |

Every approved denominator is positive, `h = h' * d`, each digest partition sums to `m`, and the
public-key, secret-key, and signature formulas equal the recorded widths. All twelve exact tuples
were evaluated independently; the SHA2 and SHAKE rows agree numerically but remain distinct named
profiles.

`base2b` was independently compared with the retained iterative `base2bGo` computation at 4-, 12-,
and 14-bit digit widths, including byte-crossing cases. Zero digit width and insufficient input are
rejected. Exact-width public-key, secret-key, and signature decoding rejects both short and long
inputs for every one of the twelve profiles.

## Load-bearing declarations and axiom replay

I inspected every declaration and proof in `Params.lean`, `Encoding.lean`, `Address.lean`, and
`Codec.lean`, all focused runtime cases, and all direct/reverse uses. Side conditions have the
correct scope: approved profiles discharge positive denominators and exact factorization; integer
exactness requires the correct power-of-256 bound; `base2bChecked` requires nonzero digit width and
sufficient bits; structured ADRS recovery carries the exact field-width bounds or canonicality;
and codecs quantify over exact-width vectors. No helper chain uses `False`, an empty target,
impossible hypotheses, arbitrary distributions, or quantitative slack to establish its claim.

The exact permanent 26-root `#print axioms` replay was:

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

The reviewer-specific replay additionally printed supporting length, cardinality, append,
setter, encoding, and canonicality roots. Every completed S03 root used a subset of exactly
`[propext, Classical.choice, Quot.sound]`; none reported `sorryAx` or another nonstandard axiom.

## Tests, traceability, documents, and report

`DataCodecTests.lean` exercises all twelve profiles and derived widths, family-aware recovery,
malformed and legacy rejection, integer and digit endian boundaries, seven canonical ADRS layouts
at maximum widths, padding/tag/length/range/compression failures, and exact key/signature codec
length rejection. The runtime executable reports:

```text
SLH-DSA S03 data/codec tests: PASS (12 profiles; endian, ADRS, rejection)
```

S03 adds no conformance vector and does not use the inherited KATs as acceptance evidence. The two
inherited regression sources are byte-identical to the accepted S02 boundary:

```text
bdceaf058dd8eded7c24165f5527a24be3628a262a991de4eaa55fd132dda0ce  Sha2KAT.lean
cdff5815a1a156578749ac2c268527f43d1f1ad4e489d6eda6e21dbca985d01f  C13KAT.lean
```

Their Apache-licensed source comments identify the C-reference interfaces, modes, fixed inputs,
expected valid acceptance, and tamper rejection. Their generator revision and vector hashes remain
explicitly unpinned under the inherited open provenance finding F-015 / assumption ASM-007 and
provisional TCB-005; S03 neither closes nor overclaims that later-phase work. Both regressions run
and print valid-accepted/tampered-rejected PASS.

All 23 declaration rows, proof obligations, findings dispositions, TCB entries, source-ledger and
reference pins, session/plan/specification/blueprint text, review routing, validation record, and
report were checked against the actual Lean sources and exact candidate state. Active evidence
consistently describes the implemented theorem strength, transparent codec aliases, inherited KAT
limits, and S03/S04 boundary. The report renders to seven pages; box-layout warnings are cosmetic.

## Reproduced commands and gates

Commands are classified as static audit, elaboration, runtime, build, or report rendering.

```text
git show -s --format='%H%n%P%n%s%n%T' 79b42bf9
git diff --name-status a80e4d33..79b42bf9
git diff --name-status dab93b0a..79b42bf9
git diff --check a80e4d33..79b42bf9
git diff --check dab93b0a..79b42bf9
git status --short
  PASS (static exact identity, cumulative/final scope, whitespace, and clean prestate).

sha256sum ../NIST.FIPS.205.pdf
pdfinfo ../NIST.FIPS.205.pdf
pdftotext -layout ../NIST.FIPS.205.pdf /tmp/s03-r2-fips205.txt
  PASS (static primary-source identity and direct Sections 4/5/11 inspection).

lake build HashSig.SLHDSA.Address HashSig.SLHDSA.Codec
  PASS (focused build; 2,690 jobs).

lake env lean scripts/slhdsa/S03InventoryProbe.lean
  PASS (elaboration): all 26 exact load-bearing roots and axiom footprints.

lake env lean /tmp/S03R2IndependentProbe.lean
  PASS (reviewer-specific elaboration/execution): all twelve profiles and family inverses; exact
  formulas and widths; integer boundaries; bit/byte-crossing base2b comparisons; all seven maximum
  ADRS layouts and negative mutations; all codec length boundaries; theorem types and expanded
  axiom prints.

lake env lean scripts/slhdsa/PolicyAudit.lean
  PASS (authoritative compiled audit): 28 modules, 2,010 owned constants, exact seven permitted
  compiler helpers, and aggregate union `[propext, Classical.choice, Quot.sound, sorryAx]`, with
  `sorryAx` confined to the frozen legacy security placeholder.

lake exe slhdsa_data_codec_tests
  PASS (runtime): 12 profiles; endian, ADRS, and rejection behavior.

lake exe slhdsa_kat
lake exe slhdsa_c13_kat
  PASS (runtime regressions): valid signatures accepted and tampered signatures rejected.

lake exe mk_all --lib HashSig --module --check
  PASS (generated umbrella current; no update necessary).

bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh
  PASS (source isolation).

lake build HashSig
  PASS (full library build; 2,749 jobs; only the frozen legacy Security warning).

lake build HashSigTest
  PASS (full test-library build; 2,755 jobs; only the frozen legacy Security warning).

./scripts/slhdsa/validate.sh --docs-only
  PASS (documentation, schema, provenance, source mutation, declaration facts, and harness routing).

./scripts/slhdsa/validate.sh
  PASS (complete wrapper): 3,007-job repository build; 2,749-job HashSig build; 2,755-job
  HashSigTest build; exact fresh 16-positive/52-negative parser runtime; S02/S03 probes;
  authoritative policy and ordinary/IR fixture; umbrella and isolation checks; both KAT
  regressions; S03 runtime; final `SLH-DSA full baseline validation: PASS`.

latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/slhdsa-s03-r2-tex slhdsa-formalization-audit.tex
  PASS (report rendering): seven pages, 326,492 bytes; box-layout warnings only.
```

## Final decision

Final result: **PASS with zero blocking and zero nonblocking findings**. All six prior findings are
fixed, the exact declarations and proofs match FIPS 205 and their stated evidence, the complete
required gate set passes, and no new issue was found. S03 is accepted at
`79b42bf9662dcfe4336401096e9bd4ae0ed924d3`; S04 may begin only from this exact accepted
predecessor and under its separately documented scope and gates.
