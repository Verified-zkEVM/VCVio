# S04 primitive interfaces and SHA2/SHAKE instantiations bootstrap

Status: bootstrap initialized; implementation blocked pending independent S03 acceptance.

Date: 2026-08-26
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: none. The S03 implementation payload is exact commit
`caefbda5e7ed7cd7a6efb80191307de7a39eea43`; its full frozen gates pass, but this documentation-only
bootstrap is a later descendant. A fresh independent S03 reviewer must review the complete exact
tree containing both that payload and this successor record. The reviewer, rather than this
self-referential bootstrap, records the exact reviewed commit. This bootstrap does not authorize
source changes from a provisional candidate.

## Objective

Establish the width-indexed primitive layer for every approved SLH-DSA parameter set: the abstract
byte-coherence boundary, pure Lean SHA-256/SHA-512/HMAC/MGF1/SHAKE256 foundations, and exact SHA2
and SHAKE realizations of `F`, `H`, `T_l`, `PRF`, `PRF_msg`, and `H_msg`. S04 supplies primitive
definitions and evidence only; construction correctness, external APIs, implementation
conformance, and security reductions remain successor work.

## Eligibility and authority preflight

Before any S04 Lean source changes:

1. a fresh reviewer must accept an exact commit containing S03 implementation payload
   `caefbda5e7ed7cd7a6efb80191307de7a39eea43`, this S04 bootstrap, and any later S03 repairs;
2. this record must replace `Accepted predecessor: none` with that exact accepted commit and review;
3. the exact editions and bytes of the SHA-2, SHAKE, HMAC, and MGF authorities used by the
   implementation must be added to the source ledger/reference manifest; and
4. every primitive-vector corpus must have an exact source, revision or document locator, license,
   byte hash, algorithm/mode label, and expected result before it supports a claim.

The currently pinned FIPS 205 final publication and
`docs/slhdsa/matrices/fips205-profile.json` control the SLH-DSA composition grammars. Existing
source comments cite supporting hash standards, but those comments are not a substitute for the
missing S04 authority and vector pins.

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

## Handoff

The next action is independent review of S03, not S04 implementation. If S03 fails, reopen S03,
dispose every finding, rerun its complete gates, and leave S04 blocked until a later exact S03
candidate passes review. After S03 acceptance, update this record with the exact accepted boundary,
complete the authority preflight, and only then begin S04 source work. Preserve the primitive-only
scope and do not move COV-005 or F-015/F-016/F-018.
