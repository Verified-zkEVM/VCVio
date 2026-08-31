# S04 independent primitive review r1

Verdict: **PASS**

Blocking findings: **0**
Nonblocking findings: **0**

Reviewer: fresh independent S04 r1 reviewer; not the S04 implementer, S04-001 repair implementer,
or initial S04 reviewer.
Review date: 2026-08-31.
Reviewed repair commit: `00f1416ea9b8e0eb4cabd1fe28c7029beef56c34`, parent and immutable
initial-review commit `69cdabd443bf9c6bf203f8f5bb36dd54cdc86803`, tree
`b85a637dcd0c6b0b2c815ef935191193a32f3290`.

Independence and write-scope statement: I began read-only from `AGENTS.md`, the review protocol,
the S04 session/plan/validation records, accepted S03 r2 review, immutable initial S04 FAIL, exact
launch-to-initial-candidate diff, exact S04-001 repair diff, pinned primary standards and vector
sources, every changed Lean declaration/helper, focused tests, documentation, matrices, compiled
policy, and report. I did not implement or repair the candidate. Reviewer-only probes, downloaded
primary-source copies, differentials, and report output were confined to `/tmp`. This r1 PASS
artifact is my only repository edit from the reviewed clean state.

## Decision summary

S04-001 is fixed. The 11,867-byte primitive projection now contains the exact four previously
missing active SHAKE256 records: the leading 272 bytes of NIST's official empty-message 4096-bit
example, and independently derived 32-byte outputs for `0x61` repeated 135, 136, and 137 times.
The official record has its exact example locator, projection method, classification, license
boundary, input/output lengths, and bytes. The derived records name FIPS 202 as algorithm authority
without misclassifying the outputs as NIST vectors, and record the exact Python 3.12.3 derivation
and independent OpenSSL 3.0.13 corroboration. Direct extraction from the pinned NIST PDF and fresh
Python/OpenSSL execution reproduce every byte.

`PrimitiveTests` SHA-256-pins and parses the committed JSON, resolves the four exact identifiers,
and requires each projected output to equal the same constant used by the SHAKE runtime check. The
projection hash, reference manifest, source ledger, notice, validation record, findings, session,
plan, review routing, and report all agree. The documentation gate additionally checks the exact
records, classifications, and provenance. The repair changes no `HashSig` source or primitive
algorithm.

I independently replayed the complete S04 review rather than only S04-001. The pure Lean SHA-2,
HMAC, MGF1, Keccak, and SHAKE algorithms match their pinned primary standards; all six SHA2 and six
SHAKE FIPS 205 grammars, family choices, address encodings, truncations, and widths are correct for
all twelve approved profiles. Checked SHA2 addresses enforce canonicality and the one-byte layer
and eight-byte tree limits, agree with the exact 22-byte serialization, and fail closed outside the
normative domain. The separate byte law is exactly injectivity and introduces no cryptographic
assumption.

Focused builds and runtime tests, an independent 234-record differential, independently generated
all-profile fingerprints, maximum-address probes, exact and broad axiom prints, the compiled policy
audit, documentation/provenance checks, full frozen validation, hygiene checks, source pins, and
report rendering all pass. No source, specification, evidence, matrix, report, or active-claim
issue remains. S04 is accepted at the exact reviewed commit.

## Exact reviewed state, history, and scope

Before reviewer authorship:

```text
HEAD    00f1416ea9b8e0eb4cabd1fe28c7029beef56c34
parent  69cdabd443bf9c6bf203f8f5bb36dd54cdc86803
subject fix(slhdsa): bind SHAKE boundary vectors
tree    b85a637dcd0c6b0b2c815ef935191193a32f3290
status  clean
```

The accepted S03 r2 artifact is in exact S04 launch commit
`4ce439ae38aea4f97189db8cd8781a62faaf8459`, whose parent is the accepted S03 repair
`79b42bf9662dcfe4336401096e9bd4ae0ed924d3`. Initial S04 candidate
`7f115c0ed5e6342d20db902c163b319b6b0df43d` descends directly from that launch. Its immutable
FAIL artifact is committed at `69cdabd443bf9c6bf203f8f5bb36dd54cdc86803` and reproduces as:

```text
75f47fd176cf360a86b0b25a1d7e674e1b11c664fbf86fa1279165f62ecf3229  S04-primitives-review.md
```

The launch-to-initial-candidate diff changes the permitted 29 files: the primitive abstraction,
SHA2 and Keccak foundations, new FIPS concrete module, umbrella/Lake/wrapper routing, focused tests
and projection, S04 inventory probe, and evidence-backed documentation/matrices/report. It does not
edit security, WOTS, XMSS, FORS, hypertree, scheme construction, external APIs, the ACVP
parser/runner, or inherited KAT fixtures.

The S04-001 repair changes 13 expected evidence/test/documentation files. Its executable changes
are confined to `PrimitiveTests.lean` and the documentation harness; it changes no `HashSig/**`
source. Both the cumulative launch-to-repair diff and repair-only diff pass `git diff --check`.
Source and diff scans found no new or moved `sorry`/`admit`, source or generated axiom, explicit
`unsafe`, `extern`, source `partial`/`partial_fixpoint`, initializer, runtime override,
`noncomputable`, linter suppression, `native_decide`, Extern import, or Interop import. The one
frozen security placeholder and exact seven compiler recursion helpers are unchanged.

## S04-001 and vector-provenance replay

The repaired projection reproduces exactly:

```text
11867  HashSigTest/SLHDSA/PrimitiveVectors/vectors.json
44971f8a7ab00e1a6af499dcf7cb5c1b34d96b4190f6e41108691beb0f7f4b40  vectors.json
```

The four load-bearing records are:

| identifier | input | output | classification and provenance |
| --- | ---: | ---: | --- |
| `shake256-empty-out272` | empty | 272 bytes | official NIST example prefix; exact `SHAKE256_Msg0.pdf` 4096-bit-output locator and leading-byte transformation |
| `shake256-a61-in135-out32` | `0x61` x 135 | 32 bytes | derived regression only; Python 3.12.3 `hashlib.shake_256`, OpenSSL 3.0.13 corroboration |
| `shake256-a61-in136-out32` | `0x61` x 136 | 32 bytes | derived regression only; same recorded method and corroboration |
| `shake256-a61-in137-out32` | `0x61` x 137 | 32 bytes | derived regression only; same recorded method and corroboration |

Direct `pdftotext -layout` extraction of the first seventeen 16-byte lines after `Output val is` in
the exact NIST empty-message example yielded 544 hexadecimal characters, exactly equal to the
projected 272 bytes. Both strings had SHA-256
`725c163ef3cbdd8ef57da87e7e379ca0e73104324285d290b5942ceae54da4a9`.

Independent Python 3.12.3 and OpenSSL 3.0.13 execution returned, respectively:

```text
0x61 x 135 -> 55b991ece1e567b6e7c2c714444dd201cd51f4f3832d08e1d26bebc63e07a3d7
0x61 x 136 -> 8fcc5a08f0a1f6827c9cf64ee8d16e0443106359ca6c8efd230759256f44996a
0x61 x 137 -> a44e1a438dad6273d540be65ee26386c59588efb09139dc086385d2db0c25782
```

These are exactly the three derived records and the three runtime constants. The notice accurately
separates NIST material, IETF/RFC material, and locally derived facts, and makes no validation or
endorsement claim. `testProjection` hashes the entire JSON before parsing it, finds all four IDs,
and compares their outputs with `shakeEmpty272Expected` and the three `shakeA61In*Expected`
constants. `testShake` then parses those same constants as bytes and compares them with actual Lean
SHAKE256 execution. The initial completeness defect and its active prose overclaims are therefore
closed.

## Primary-source and pin review

Fresh downloads of the remote primitive sources, together with the local pinned FIPS 205 file,
reproduced every manifest byte count and SHA-256:

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

The SHA-256/SHA-512 response members reproduce as `75e1cb83...` and `e53a36c0...`; the SHAKE
short-message and variable-output members reproduce as `a21dd918...` and `90fb7233...`. The exact
28-file source-tree composite is
`39990d89588702c566869e8262b145cc83b56ef125988ff842e0eb5c744aff59`, matching the manifest.

Direct standard inspection confirms:

- FIPS 180-4 uses 512-/1024-bit blocks, big-endian 32-/64-bit words, 64-/128-bit big-endian length
  fields, and padding to 448 modulo 512 or 896 modulo 1024. The code's IVs, constants, schedules,
  rotations, Boolean functions, rounds, feed-forward, and checked byte domains `< 2^61` and
  `< 2^125` match.
- FIPS 198-1 hashes a key longer than the selected hash block, pads the result to 64 or 128 bytes,
  and applies `0x36`/`0x5c`. Both implementations and long-key vectors match.
- RFC 8017 B.2.1 permits `maskLen <= 2^32 hLen`, encodes counters as four-byte big-endian values,
  concatenates hashes, and returns the leading requested bytes. The exact maxima are
  137,438,953,472 bytes for SHA-256 and 274,877,906,944 bytes for SHA-512; the first larger values
  are rejected.
- FIPS 202 defines SHAKE256 as Keccak-f[1600] with capacity 512, rate 1088 bits/136 bytes, SHAKE
  suffix `1111` represented by `0x1f` for byte input, and arbitrary output. The implementation
  absorbs a separate padded block for aligned input and permutes before each later squeeze block.
  SHA3 `0x06` and Ethereum Keccak `0x01` remain separate.
- FIPS 205 Section 11 uses full 32-byte addresses for SHAKE and the exact 22-byte
  `layer[1] || tree[8] || type[1] || words[12]` compression for SHA2. Its family-specific
  `Hmsg`, `PRF`, `PRFmsg`, `F`, `H`, and `Tl` concatenations and digest choices match the Lean code.

## Lean declarations, boundaries, and quantitative replay

I inspected every declaration and helper in `Primitives.lean`, `Concrete/Sha2.lean`,
`Concrete/Keccak.lean`, and `Concrete/FIPS.lean`, plus every focused runtime case and direct/reverse
use. No helper proves a positive claim via `False`, an empty target, an impossible hypothesis,
arbitrary distributions, or unbounded slack.

`Primitives.ByteLaws` states only injectivity of `yToBytes`. `yToBytes_eq_iff` uses that field in
one direction and `congrArg` in the other. Both concrete node carriers are fixed-width byte vectors
with identity encoding, so the three concrete witnesses are valid.

SHA-256/SHA-512 parsing, serialization, modular word arithmetic, padding, schedules, compression,
and output order are correct. HMAC key normalization and both block widths are correct. MGF1 uses
exact big-endian 32-bit counters and leading truncation; checked wrappers accept the inclusive RFC
maximum and reject maximum plus one.

Keccak's lane order, rho/pi tables, 24 round constants, theta/rho/pi/chi/iota mappings,
little-endian lane absorb/squeeze, `0x1f` domain, and repeated-rate squeeze are correct. The
independent Lean/Python differential compared 234 output records across SHA input lengths
0--255 around both padding boundaries, HMAC key lengths around 64/128, MGF lengths around
32/64/136/272, and SHAKE absorb/squeeze lengths around 136/272. `diff -u` was empty.

The proof-carrying SHA2-address probe accepted the maximum permitted compressed values: layer 255,
tree 18,446,744,073,709,551,615, and all three final words 4,294,967,295. It confirmed exact checked
serialization and successful checked `F/H/Tl/PRF`; rejected layer 256, tree `2^64`, a `2^32` final
word, unknown type, and noncanonical type padding; confirmed invalid total `F` returns exactly the
all-zero node; and confirmed short digest projection rejects while its explicitly total counterpart
returns exactly the requested zero width.

An independent Python implementation of the exact FIPS 205 Section 11 concatenations regenerated
all twelve composition fingerprints. The concatenated runtime widths are:

| profile pair | `n` | `m` | `5n + m` bytes |
| --- | ---: | ---: | ---: |
| 128s | 16 | 30 | 110 |
| 128f | 16 | 34 | 114 |
| 192s | 24 | 39 | 159 |
| 192f | 24 | 42 | 162 |
| 256s | 32 | 47 | 207 |
| 256f | 32 | 49 | 209 |

Each SHA2/SHAKE pair has the same widths but a distinct family fingerprint. All twelve values match
the committed projection and the Lean runtime exactly.

## Axiom and policy replay

The permanent exact eleven-root probe and explicit `#print axioms` replay produced:

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

A broader explicit replay printed all twelve grammar helpers, checked address/conversion helpers,
both MGF checked wrappers, and fail-closed projection helpers. Every root uses a subset of exactly
`[propext, Classical.choice, Quot.sound]`; none uses `sorryAx` or another nonstandard axiom.

The authoritative compiled audit observes 29 HashSig modules and 2,139 owned constants, retains
the exact seven permitted `._unsafe_rec` compiler auxiliaries, and retains the exact aggregate
union `[propext, Classical.choice, Quot.sound, sorryAx]`, with `sorryAx` confined to the frozen
`SLHDSA.slhdsa_euf_cma_security` placeholder. Persistent-extension fixtures reject both ordinary
and IR initializer surfaces without executing the sentinel. No TCB or admission boundary changed.

## Documentation, matrices, and report

The session, plan, validation record, source ledger, reference manifest, specification, blueprint,
findings and dispositions, review/session routing, declaration inventory, proof-obligation,
coverage, assumption, and TCB matrices all agree with the code and reviewed evidence. F-007 and
F-093 through F-096 accurately remain remediated pending this review in the candidate tree.
COV-015 and PO-017 describe primitive executable evidence without claiming construction
correctness, ACVP certification, or a general mathematical refinement. COV-005 and
F-015/F-016/F-018 remain deferred/open. No successor construction or security claim is activated.

The report's statements about exact vector classifications, the four repaired SHAKE records,
projection/runtime binding, primitive grammars, policy counts, pending review state, and residual
limits are true. It renders to eight pages and 329,059 bytes. Box-layout warnings are cosmetic.

## Reproduced commands and gates

Commands are classified as static audit, build/elaboration, runtime, differential, or report
rendering.

```text
# Static history, scope, pins, and hygiene
git show -s --format='%H%n%P%n%s%n%T' 00f1416e
git diff --name-status 4ce439ae..7f115c0e
git diff --name-status 69cdabd..00f1416e
git diff --check 4ce439ae..00f1416e
git status --short --untracked-files=all
sha256sum <all pinned sources, archive members, FAIL artifact, and vectors.json>
LC_ALL=C sha256sum HashSig/SLHDSA/*.lean HashSig/SLHDSA/C13/*.lean \
  HashSig/SLHDSA/Concrete/*.lean HashSig/SLHDSA/Security/*.lean | sha256sum
PASS: exact identity/scope, clean state, all pins, immutable FAIL, and source composite.

# Focused build/elaboration and runtime
lake build HashSig.SLHDSA.Concrete.FIPS
lake build HashSigTest.SLHDSA.PrimitiveTests
lake exe slhdsa_primitive_tests
PASS: builds; runtime prints
SLH-DSA S04 primitive tests: PASS (SHA2/SHAKE vectors; 12 profile grammars)

# Exact and broad axiom elaboration
lake env lean scripts/slhdsa/S04InventoryProbe.lean
lake env lean /tmp/S04R1ReviewerProbe.lean
PASS: exact eleven roots and broader helpers; standard allowlist only; no sorryAx.

# Independent runtime/differential probes
lake env lean --run /tmp/S04R1Differential.lean
python3 /tmp/S04R1Differential.py
diff -u /tmp/S04R1Differential.py.out /tmp/S04R1Differential.lean.out
python3 /tmp/S04R1Profiles.py
lake env lean --run /tmp/S04R1AddressProbe.lean
PASS: 234 differential records with empty diff; all twelve grammar fingerprints; maximum and
negative SHA2-address, exact serialization, and fail-closed boundaries.

# Authoritative policy and documentation gates
lake env lean scripts/slhdsa/PolicyAudit.lean
./scripts/slhdsa/validate.sh --docs-only
PASS: 29 modules, 2,139 constants, exact seven helpers, exact axiom union; documentation,
projection, provenance, schema, source mutation, declaration facts, and routing.

# Full frozen wrapper
./scripts/slhdsa/validate.sh
PASS: 3,007-job repository build; HashSig and HashSigTest builds; fresh parser positive/negative and
mutation fixtures; S02/S03/S04 declaration probes; compiled policy ordinary/IR fixture; generated
umbrella; extern/interop isolation; both inherited KAT regressions; S03 data/codec runtime; S04
primitive runtime; final SLH-DSA full baseline validation: PASS.

# Report rendering
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/s04-r1-report slhdsa-formalization-audit.tex
PASS: eight pages, 329,059 bytes; cosmetic box-layout warnings only.
```

Build commands are elaboration evidence; vector and differential commands are runtime evidence.
The inherited SHA2-128-24 and C13 KATs remain C-reference regressions, not FIPS/ACVP conformance.

## Findings and dispositions

- S04-001 / F-096: **fixed and independently verified**. The four exact records, classifications,
  provenance, whole-file pin, parsed executable binding, and active prose now agree.
- New blocking findings: **none**.
- New nonblocking findings: **none**.

## Final decision

Final result: **PASS with zero blocking and zero nonblocking findings**. The exact repair closes the
only initial S04 finding; the full primitive implementation, primary-source correspondence,
boundary behavior, evidence, declarations, tests, matrices, report, and frozen validation gates
all pass. S04 is accepted at `00f1416ea9b8e0eb4cabd1fe28c7029beef56c34`.
