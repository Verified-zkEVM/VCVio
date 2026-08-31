# S04 primitive interfaces and SHA2/SHAKE instantiations candidate

Status: implementation complete; independent S04 review pending.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: exact S03 repair commit
`79b42bf9662dcfe4336401096e9bd4ae0ed924d3`, independently accepted with zero findings by
`docs/slhdsa/reviews/S03-data-codec-review-r2.md`; the review artifact is committed in exact S04
launch commit `4ce439ae38aea4f97189db8cd8781a62faaf8459`. The immutable initial and r1 FAIL reviews remain
part of the reviewed history, and the r2 review explicitly replayed their complete finding set.

## Objective

Establish the width-indexed primitive layer for every approved SLH-DSA parameter set: the abstract
byte-coherence boundary, pure Lean SHA-256/SHA-512/HMAC/MGF1/SHAKE256 foundations, and exact SHA2
and SHAKE realizations of `F`, `H`, `T_l`, `PRF`, `PRF_msg`, and `H_msg`. S04 supplies primitive
definitions and evidence only; construction correctness, external APIs, implementation
conformance, and security reductions remain successor work.

## Eligibility and authority preflight

Before any S04 Lean source changes:

1. a fresh reviewer must accept an exact commit containing S03 implementation payload
   `caefbda5e7ed7cd7a6efb80191307de7a39eea43`, this S04 bootstrap, immutable failed review
   `reviews/S03-data-codec-review.md`, immutable r1 failed review
   `reviews/S03-data-codec-review-r1.md`, and all six S03 repairs/dispositions;
2. this record must replace `Accepted predecessor: none` with that exact accepted commit and review;
3. the exact editions and bytes of the SHA-2, SHAKE, HMAC, and MGF authorities used by the
   implementation must be added to the source ledger/reference manifest; and
4. every primitive-vector corpus must have an exact source, revision or document locator, license,
   byte hash, algorithm/mode label, and expected result before it supports a claim.

The preflight is complete. The accepted predecessor is recorded above. Exact FIPS 180-4, FIPS 202,
FIPS 198-1, RFC 8017, CAVP archive, NIST example, and repository projection byte pins now live in
`reference-manifest.json` and `source-ledger.md`. FIPS 205 final and
`matrices/fips205-profile.json` control the SLH-DSA composition grammars. The committed projection
preserves source locators, member hashes, classifications, and notices; derived MGF1 and profile
fingerprints are explicitly regression/composition evidence rather than NIST vectors.

## Allowed scope

After eligibility, implementation may change `HashSig/SLHDSA/Primitives.lean`,
`Concrete/Sha2.lean`, and `Concrete/Keccak.lean`, or introduce narrowly focused SHA-512, SHAKE, and
approved-profile concrete modules. It may add generated umbrella imports, focused tests under
`HashSigTest/SLHDSA`, Lake executable targets, and evidence-backed documentation/matrix updates.

The descriptor/AST harness remains frozen absent a concrete regression. S04 does not change WOTS,
XMSS, FORS, hypertree, internal/external scheme, ACVP parser/runner, security, or deployment code.
It does not add native bindings or an `extern`, `unsafe`, initializer, runtime override, admission,
or `native_decide` dependency. The C13 Ethereum-keccak variant remains separate and receives only
regression testing if shared sponge code changes.

COV-005 remains owned by S10. F-015/F-016/F-018 remain open, and the existing ACVP artifacts remain
schema/provenance evidence rather than primitive or implementation-conformance vectors.

## Starting inventory

- `Primitives.lean` exposes abstract carrier types and an arbitrary `yToBytes`; it has no separate
  coherence/injectivity law. F-007 and PO-007 therefore remain open.
- `Concrete/Sha2.lean` supplies executable SHA-256, MGF1-SHA-256, and HMAC-SHA-256 only. It has no
  SHA-512, HMAC-SHA-512, or MGF1-SHA-512 implementation.
- `Concrete/Keccak.lean` supplies Ethereum `keccak256` and SHA3-256 with a one-block squeeze. It is
  not a FIPS SHAKE256 XOF and cannot establish the SHAKE-family primitive grammar.
- `Concrete/Instance.lean` wires only the non-FIPS reduced SHA2 profile. Its embedded KAT is legacy
  regression evidence, not evidence for any of the twelve approved profiles.
- SHA2 compression currently consumes unchecked `Adrs.compressSha2`. S04 must state and enforce the
  canonical/narrow-address precondition rather than claim correct behavior for arbitrary `Nat`
  fields that truncate during compression.
- TCB-004 and ASM-006 remain provisional/pending. No current test corpus establishes all-12
  primitive behavior or concrete equivalence with the pinned FIPS grammars.

## Initial work packages

1. Complete the authority/vector preflight and record licenses, exact hashes, algorithms, input and
   output lengths, and provenance without treating generated or legacy vectors as NIST validation.
2. Add only the abstract byte law actually required downstream, likely as a separate law bundle so
   generic structural correctness does not acquire irrelevant cryptographic assumptions. Prove the
   law for every concrete byte-vector instance and discharge F-007/PO-007 only after review.
3. Generalize the pure SHA2 foundation with SHA-512, HMAC-SHA-512, and MGF1-SHA-512 while retaining
   exact big-endian padding/counter behavior and width-indexed truncation results.
4. Implement a distinct FIPS SHAKE256 XOF with the correct domain separation and multi-block
   squeezing. Keep Ethereum keccak and SHA3 names/domains separate and test output crossing the
   sponge rate boundary.
5. Define all six SHA2 and six SHAKE primitive bundles over `Bytes n`. Select the exact FIPS grammar
   by family and `n`: SHA2 category-1 functions use SHA-256; SHA2 `n=24/32` use SHA-512 for
   `H`/`T_l`/`H_msg` and HMAC-SHA-512 for `PRF_msg` while retaining SHA-256 for `F`/`PRF`; every
   SHAKE primitive uses SHAKE256. Make output lengths type-correct at `n` or `m`.
6. Introduce an explicit canonical/SHA2-compressible address precondition or proof-carrying adapter.
   Prove the checked and concrete encodings agree on that domain; do not silently broaden this into
   a theorem for arbitrary in-memory addresses.
7. Add standard hash/HMAC/MGF/XOF vectors, padding and output-boundary cases, and profile-indexed
   grammar fixtures for all twelve sets. Preserve both legacy KATs and the S03 data/codec suite as
   nonconformance regressions.
8. Update declarations, coverage, proof obligations, assumptions, TCB, findings, report, and this
   record from compiled evidence, then request a fresh independent S04 review.

## Gates

- the exact accepted S03 predecessor and its review are recorded before source work;
- all supporting standards and vector bytes satisfy the authority preflight;
- `lake build HashSig` and the focused primitive/test targets pass without a new admission or
  runtime trust surface;
- standard SHA-256, SHA-512, HMAC-SHA-256/512, MGF1-SHA-256/512, and SHAKE256 vectors pass,
  including padding, empty-input, multi-block, truncation, and XOF rate-crossing cases;
- all twelve approved profiles evaluate the exact six primitive grammars and exact `n`/`m` output
  widths, with SHA2 address preconditions tested positively and negatively;
- changed load-bearing roots have saved `#print axioms` output without `sorryAx`; the full compiled
  policy audit retains the exact permitted axiom union and exact seven compiler helpers;
- the S03 data/codec executable, both legacy KATs, generated umbrella, extern/interop isolation,
  `git diff --check`, documentation/provenance gate, and full frozen wrapper pass; and
- a fresh reviewer authors `reviews/S04-primitives-review.md`. The implementer does not create,
  template, or pre-fill that review or verdict.

## Candidate implementation and evidence

- `Primitives.ByteLaws` isolates node-byte injectivity from the structural primitive bundle and
  supplies `yToBytes_eq_iff`; both concrete families and all approved profiles have witnesses.
- `Concrete.Sha2` retains the SHA-256 paths and adds pure Lean SHA-512, HMAC-SHA-512,
  MGF1-SHA-512, explicit SHA input-domain predicates, and checked RFC 8017 MGF1 limits.
- `Concrete.Keccak` retains Ethereum Keccak `0x01` and SHA3 `0x06`; SHAKE256 uses FIPS domain
  `0x1f`, rate 136, and repeats the permutation across arbitrary output blocks.
- `Concrete.FIPS` defines all six exact SHA2 and SHAKE grammars, selects them over the closed twelve
  `ParameterSet` constructors, and exposes checked SHA2 operations over `Sha2Address`. That adapter
  verifies canonicality, the one-byte layer, and eight-byte tree before compression. The existing
  total interface fails closed to an all-zero result outside this domain and makes no normative
  claim there. Fixed-width digest projection rejects a short source instead of padding partial
  digest bytes; the total bundle's explicitly named conversion likewise fails closed.
- `PrimitiveTests` checks official SHA-256/SHA-512/HMAC/SHAKE examples, padding neighbors,
  multi-block input, long HMAC keys, derived MGF1 second-block/truncation cases, MGF1 bound
  rejection, SHAKE 135/136/137/272-byte outputs, 135/136/137-byte and 200-byte inputs, domain
  separation, positive/negative SHA2 addresses, all output widths, and independently derived exact
  grammar fingerprints for all twelve approved profiles.

Focused execution reports:

```text
lake build HashSig.SLHDSA.Concrete.FIPS
Build completed successfully

lake exe slhdsa_primitive_tests
SLH-DSA S04 primitive tests: PASS (SHA2/SHAKE vectors; 12 profile grammars)

lake env lean scripts/slhdsa/S04InventoryProbe.lean
S04 declaration/axiom probe: PASS (11 exact load-bearing roots)

./scripts/slhdsa/validate.sh --docs-only
SLH-DSA docs-only validation: PASS

./scripts/slhdsa/validate.sh
SLH-DSA full baseline validation: PASS
```

The 11-root probe records one axiom-free byte-coherence theorem; the SHA2 roots use only
`propext`, `Classical.choice`, and `Quot.sound`; SHAKE256 uses only `propext` and `Quot.sound`.
No root introduces `sorryAx`. The full audit observes 29 HashSig modules, 2,139 owned constants,
the exact inherited seven compiler helpers, and the unchanged exact axiom union. The exact
candidate commit is recorded at handoff.

## Handoff

S03 r2 accepted the exact predecessor with zero findings, so S04 launched from commit
`4ce439ae38aea4f97189db8cd8781a62faaf8459`. Review the exact candidate produced from this record,
including the source/vector pins, focused executable, all-profile grammars, checked address domain,
axiom inventory, and inherited regressions. Do not move COV-005 or F-015/F-016/F-018.
