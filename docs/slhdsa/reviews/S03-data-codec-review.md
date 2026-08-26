# S03 independent data and codec review

Verdict: **FAIL**

Blocking findings: **5**
Nonblocking findings: **0**

Reviewer: fresh independent S03 reviewer; not the S03 implementer.
Review date: 2026-08-26.
Reviewed commit: `963a3e7dd425b8a8c9bb9e2e91b73868f6918768`, parent
`caefbda5e7ed7cd7a6efb80191307de7a39eea43`, relative to exact accepted S02 commit
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the accepted S02 artifact and commit, the exact cumulative S03 diff, every changed Lean declaration,
the primary FIPS source, the pinned profile, matrices, generated inventory, tests, and compiled
policy. I did not implement the candidate. Temporary Lean probes were removed after execution. This
FAIL artifact is the first repository edit made from the reviewed clean state.

## Decision summary

The candidate gets the normative table, formulas, byte order, address layout, rejecting length
checks, and runtime fixtures substantially right. The exact local FIPS PDF pin reproduces, all twelve
profile rows and derived sizes evaluate correctly, the seven address tags and type-specific padding
match the standard, and the full frozen validation wrapper passes. No primitive, construction,
external-API, implementation-conformance, or security claim is improperly activated.

Those successes are insufficient under the zero-finding review protocol. The public parameter
lookup maps every SHAKE profile to its paired SHA2 profile because it discards the hash family. The
claimed integer and ADRS roundtrip proof surfaces are absent: the integer theorem merely restates
the serialization definition, while the ADRS theorem starts from an already encoded wire and proves
only byte-carrier identity. Six declaration-inventory rows record an empty axiom footprint even
though the exact compiled roots use `propext`. Finally, the fixed-width key/signature aliases are
transparent `abbrev`s but are repeatedly described as opaque.

Any one issue requires FAIL. S03 remains unaccepted, and S04 remains blocked pending repair and a
fresh `S03-data-codec-review-r1.md` review of the complete fixed successor-routing tree.

## Exact reviewed state and scope

Before reviewer authorship:

```text
HEAD    963a3e7dd425b8a8c9bb9e2e91b73868f6918768
parent  caefbda5e7ed7cd7a6efb80191307de7a39eea43
subject docs(slhdsa): bootstrap S04 primitives
status  clean
```

The S03 implementation payload is exact commit
`caefbda5e7ed7cd7a6efb80191307de7a39eea43`; the reviewed descendant adds only the required
documentation-only S04 bootstrap. The cumulative diff from accepted S02 is confined to the S03
source/test allowlist, umbrella/Lake/wrapper routing, documentation and matrices, the immutable S02
r8 acceptance artifact, and its narrow pins. It does not edit the rejected legacy security theorem,
the accepted S02 security modules, primitive implementations, construction algorithms, ACVP parser,
or vector fixtures. Both cumulative and payload diffs pass `git diff --check`.

The source scan and compiled policy found no new `sorry`/`admit`, source or generated axiom,
explicit `unsafe`, `extern`, source `partial`/`partial_fixpoint`, initializer, runtime override,
noncomputable declaration, linter suppression, Extern import, or Interop import in the S03 changes.
The two retained recursive encoding helpers account for the same exact reviewed compiler helpers;
the aggregate HashSig boundary remains exactly seven.

## Primary-source and quantitative correspondence

The local primary source reproduced as:

```text
8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d  NIST.FIPS.205.pdf
size: 1055752 bytes
status/date: final, 2024-08-13
```

Direct inspection of FIPS 205 Sections 4, 5, 9, and 11 confirmed:

- Table 1 uses a four-byte layer, twelve-byte tree, four-byte type, and three four-byte
  type-dependent words; a type change clears the final twelve bytes;
- the seven type codes are exactly 0 through 6, and the zero-padding cases implemented by
  `Adrs.isCanonical` match the address-layout figures;
- the SHA2 compressed address selects one layer byte, eight tree bytes, one type byte, and the
  final twelve bytes, totaling 22 bytes;
- Algorithms 2 and 3 use big-endian base 256, and Algorithm 4 consumes the leading bit string in
  big-endian bit order; and
- Table 2 contains the six primary rows below, each instantiated once by SHA2 and once by SHAKE.

Independent evaluation of the code produced the following tuples. `parts` is
`(digestBytes, treeIdxBytes, leafIdxBytes)`, and `sizes` is `(pk, sk, sig)` in bytes.

| pair | `(n,h,d,h',a,k,lgw)` | `(len1,len2)` | parts | `m` | sizes |
| --- | --- | --- | --- | --- | --- |
| 128s | `(16,63,7,9,12,14,4)` | `(32,3)` | `(21,7,2)` | 30 | `(32,64,7856)` |
| 128f | `(16,66,22,3,6,33,4)` | `(32,3)` | `(25,8,1)` | 34 | `(32,64,17088)` |
| 192s | `(24,63,7,9,14,17,4)` | `(48,3)` | `(30,7,2)` | 39 | `(48,96,16224)` |
| 192f | `(24,66,22,3,8,33,4)` | `(48,3)` | `(33,8,1)` | 42 | `(48,96,35664)` |
| 256s | `(32,64,8,8,14,22,4)` | `(64,3)` | `(39,7,1)` | 47 | `(64,128,29792)` |
| 256f | `(32,68,17,4,9,35,4)` | `(64,3)` | `(40,8,1)` | 49 | `(64,128,49856)` |

The values agree with the pinned profile and FIPS table/formulas. Every denominator used by an
approved row is positive, `h = h' * d` holds, every digest partition sums to `m`, the public and
secret key sizes are `2n` and `4n`, and the signature formula evaluates to the table size. The
legacy reduced record remains outside the closed approved family. No S03 vector was added; the two
inherited C-reference KATs retain their previously documented legacy-regression scope and both pass.

## Load-bearing declaration and axiom review

I inspected in full the structure/profile definitions, formulas, approval predicate and witnesses,
integer and digit encodings, all ADRS fields/setters/canonicality/serializers/decoders, fixed-width
codecs, their proofs, every runtime test, and direct/reverse usages under `HashSig/**`. Quantifier
order and side conditions are appropriate where present: `toInt_lt_pow` is unconditional,
`base2bChecked_eq` requires nonzero digit width and sufficient bits, and codec roundtrips quantify
over exact-width vectors.

The exact `#print axioms` replay for the declared S03 load-bearing roots was:

```text
SLHDSA.ParameterSet.profile: []
SLHDSA.ParameterSet.profile_sizes: [propext]
SLHDSA.ParameterSet.wots_widths: [propext]
SLHDSA.ParameterSet.valid: [propext, Classical.choice, Quot.sound]
SLHDSA.toInt_lt_pow: [propext, Classical.choice, Quot.sound]
SLHDSA.decodeExact_encode: [propext]
SLHDSA.base2b_bigEndian: [propext]
SLHDSA.base2bChecked: [propext]
SLHDSA.Adrs.isCanonical: [propext]
SLHDSA.Adrs.decode: [propext]
SLHDSA.Adrs.decode_encode: [propext]
SLHDSA.decodePublicKey: [propext]
SLHDSA.decodeSecretKey: [propext]
SLHDSA.decodeSignature: [propext]
SLHDSA.decodePublicKey_encode: [propext]
SLHDSA.decodeSecretKey_encode: [propext]
SLHDSA.decodeSignature_encode: [propext]
```

No completed root reports `sorryAx` or a nonstandard axiom. Finding S03-004 concerns the false
manual inventory, not an unacceptable logical dependency.

Dependency inspection found no `False` premise, empty target used to prove a positive claim,
impossible hypothesis, arbitrary distribution, or unbounded quantitative slack in the S03 roots.
The generic unchecked `Params` and plain ADRS setters remain available for existing construction
code, but the session documentation correctly requires future approved APIs to carry a named set or
validity witness and checked external boundaries.

## Findings

### S03-001 — parameter lookup discards the hash family

Severity: **HIGH**.

`ParameterSet.ofParams : Params -> Option ParameterSet` searches only `s.params`. Each SHA2/SHAKE
pair has identical primary parameters, and `ParameterSet.all` places SHA2 first. Consequently the
public function returns the SHA2 constructor for every SHAKE input. Independent evaluation gave:

```text
ofParams SHAKE-128s.params = some SHA2-128s
ofParams SHAKE-192f.params = some SHA2-192f
ofParams SHAKE-256f.params = some SHA2-256f
```

`DataCodecTests.testParameters` masks the defect by checking only
`found.params == s.params`, never `found == s`. This is unsafe successor input for S04, where the
family selects incompatible primitive grammars.

Required repair: include `HashFamily` in the lookup key (or return every matching profile), prove
the exact named-profile inverse for all twelve constructors, and make the runtime test compare the
constructor itself.

### S03-002 — Algorithm 3 has no semantic roundtrip theorem

Severity: **HIGH**.

`toByte_bigEndian` is reflexivity over the definition. `toByte_length` proves only length, and
`toInt_lt_pow` proves only the range of decoding. There is no theorem that decoding the `len`-byte
serialization returns `x` under `x < 256^len`, nor the total truncation law returning
`x % 256^len`. The single `0x123456` runtime example cannot discharge the general FIPS encoding
law. Nevertheless PO-011, the blueprint, report, and S03 record classify the roundtrip/law surface
as implemented or discharged.

Required repair: prove the total modulo law and its in-range corollary, connect the checked encoder
to that theorem, and add boundary runtime cases including zero width, maximum accepted value, and
overflow rejection.

### S03-003 — the ADRS theorem proves carrier identity, not structured encode/decode

Severity: **HIGH**.

`Adrs.decode_encode` starts from `wire : Adrs.Wire`, whose field is already the exact 32-byte
carrier plus a proof that parsing those bytes is canonical. `Wire.encode` simply returns those same
bytes. The theorem therefore proves decoder identity on a prevalidated byte wrapper. It does not
show that `fromVector` applied to `Adrs.toBytes` reconstructs the original fields, that
`encodeChecked` produces a decodable wire, or that a structured canonical `Adrs` survives an
encode/decode cycle. Only one concrete address exercises that missing direction at runtime.

This is weaker than the ADRS roundtrip claim in `specification.md`, `lean-blueprint.md`, PO-011, and
the session handoff.

Required repair: add the semantic parser view and prove full-width serialization/parsing identity
under exact field-width hypotheses, derive it from canonicality, and prove checked canonical ADRS
encode/decode. Exercise maximum-width fields and each canonical type layout at runtime.

### S03-004 — six declaration rows have false axiom footprints

Severity: **HIGH**.

DECL-040 through DECL-042 and DECL-044 through DECL-046 record
`transitive_axioms: []`. Exact compiled `#print axioms` reports `[propext]` for all six. The
dependencies are allowed by policy, but false mandatory traceability is a review failure. The
current harness validates schema and S02 exact facts but does not semantically compare these S03
rows, so the full wrapper does not catch the mismatch.

Required repair: correct all six rows, add or extend an elaborated S03 inventory probe that checks
every S03 root and exact axiom footprint, and update the reviewed matrix pin deliberately.

### S03-005 — transparent aliases are described as opaque carriers

Severity: **MEDIUM**.

`PublicKeyBytes`, `SecretKeyBytes`, and `SignatureBytes` are public exposed `abbrev`s of `Bytes`.
They are definitionally transparent and provide width indexing, but no opacity or nominal
separation. `Codec.lean`, the S03 session, and the report call them opaque.

Required repair: either introduce genuinely opaque/nominal carrier structures with the required
encode/decode theorems, or correct every claim to say exact-width transparent carrier aliases.

## Reproduced commands and gates

Commands are classified rather than treating elaboration as execution.

```text
git diff --check a80e4d33..963a3e7d
git status --short
  PASS (static scope/whitespace; clean before reviewer authorship).

sha256sum ../NIST.FIPS.205.pdf
pdfinfo ../NIST.FIPS.205.pdf
pdftotext -layout ../NIST.FIPS.205.pdf /tmp/fips205-s03.txt
  PASS (static primary-source identity and inspection).

lake env lean <temporary S03 declaration/axiom probe>
  PASS (elaboration; exact types and axiom output recorded above).

lake env lean <temporary all-set evaluation probe>
  PASS (execution during elaboration; exact values recorded above, and family-loss defect exposed).

./scripts/slhdsa/validate.sh
  PASS (complete frozen wrapper).
```

The full wrapper reproduced the documentation/schema/provenance harness, full 3007-job repository
build, HashSig and HashSigTest builds, fresh 68-case parser runtime, compiled policy fixtures,
generated umbrella check, isolation checks, inherited SHA2 and C13 KAT execution, and S03 runtime
execution. The policy observed 28 HashSig modules, 1,975 owned constants, exactly seven reviewed
compiler helpers, and the exact aggregate axiom union
`[propext, Classical.choice, Quot.sound, sorryAx]`, with `sorryAx` confined to the frozen legacy
placeholder. The S03 executable printed:

```text
SLH-DSA S03 data/codec tests: PASS (12 profiles; endian, ADRS, rejection)
```

That output is valid regression evidence, but the five findings demonstrate why passing the frozen
wrapper does not self-certify the session.

## Verdict rationale

The primary table and executable definitions are largely correct, and no policy or conformance
boundary regressed. S03 nevertheless overclaims discharged semantic laws, exposes a family-confusing
lookup exactly where S04 needs the distinction, and contains false mandatory inventory data. Under
the independent-review stop rule S03 fails, no acceptance verdict exists, and S04 implementation
must not begin until a repaired exact commit receives a fresh zero-finding review.
