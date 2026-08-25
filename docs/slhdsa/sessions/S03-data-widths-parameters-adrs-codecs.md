# S03 data, widths, parameters, ADRS, and codecs bootstrap

Status: bootstrap retained; temporarily blocked by S02 r5 pending repaired r6 review.

Date: 2026-08-25
Branch: `codex/sphincsplus-formalization`
Former predecessor: S02 commit `7b77e700b3d24a6ab94ed741a650954bbd90859a`; r4 acceptance was
invalidated by `reviews/S02-security-architecture-review-r5.md`. This record will name the repaired
accepted predecessor after r6.

## Objective

Establish the width-safe data layer used by every later construction: the complete FIPS-approved
parameter family, exact address operations and serialization, big-endian integer and digit
extraction, and total encoders paired with rejecting decoders. S03 begins from accepted S00/S01
infrastructure and the accepted S02 interfaces; neither is a new review target.

## Authoritative inputs

- FIPS 205 Sections 3--5 and 11, including Table 1 address operations, Algorithms 2--4, and the
  twelve approved parameter sets in Table 2;
- the pinned FIPS profile in `docs/slhdsa/matrices/fips205-profile.json`, the S01 coverage and proof
  obligation matrices, and the reference pins in `docs/slhdsa/reference-manifest.json`;
- the accepted S02 types imported through `HashSig.lean`, with no claim that the rejected legacy
  security theorem has been repaired; and
- existing ACVP schema-format fixtures as test inputs only, under their documented S01 assurance
  boundary.

## Allowed scope

Implementation may change `HashSig/SLHDSA/Params.lean`, `Address.lean`, `Encoding.lean`, introduce
focused byte or codec modules, add generated umbrella imports, and add focused tests under
`HashSigTest/SLHDSA`. Documentation and matrices may be updated when backed by compiled evidence.

The descriptor/AST harness is frozen and must not be reopened absent a concrete regression. S03
does not edit the rejected `HashSig/SLHDSA/Security.lean`, accepted S02 security modules, primitive
instantiations, construction algorithms, or the ACVP runner. It does not claim implementation
conformance. COV-005 remains owned by S10, and F-015/F-016/F-018 remain open.

## Starting inventory

- `Params.lean` uses unrestricted natural-number fields and names only the reduced SHA2 profile.
- `Address.lean` stores address words as unrestricted naturals; serialization truncates but the
  representable ranges are not captured by the types.
- `Encoding.lean` implements the core big-endian helpers and proves only basic output length and
  digit bounds. Its missing-input behavior is total zero-fill rather than a rejecting codec.
- Existing ACVP artifacts validate parser and schema format, not SLH-DSA execution.

## Initial work packages

1. Define a valid parameter representation and enumerate all twelve approved FIPS parameter sets,
   keeping the SP 800-230 reduced profile explicitly non-FIPS and separate.
2. Derive byte widths, WOTS/FORS lengths, digest partitions, and key/signature sizes, then prove
   range, divisibility, positivity, and all-set evaluation laws needed downstream.
3. Make ADRS field widths and type-dependent operations exact, including clear-on-type-change,
   canonical full serialization, and SHA2 compression behavior.
4. characterize `toInt`, `toByte`, and `base2b` as big-endian operations; separate WOTS digits,
   checksum digits, FORS indices, and message-digest partitioning.
5. Add encoders and decoders whose types or results distinguish malformed lengths, values, and
   trailing data from valid inputs, with positive and negative fixtures.
6. Record compiled evidence and request a fresh independent review only after all gates pass.

## Gates

- `lake build HashSig` and focused test targets pass without new admissions;
- all approved parameter sets evaluate to their authoritative widths and sizes;
- roundtrip, rejection, range, endian, and address-clearing properties have executable fixtures and
  load-bearing proofs;
- existing ACVP fixtures are used only within their pinned provenance and schema-format scope;
- `git diff --check`, admission/source scans, and the frozen documentation harness pass; and
- a fresh reviewer authors `reviews/S03-data-codec-review.md`; this bootstrap does not create or
  pre-fill that verdict.

## Handoff

Begin implementation with a fresh orchestration agent at the accepted predecessor above. Preserve
the S02 architecture boundary and treat later primitive, construction, conformance, and security
proof work as successor sessions. The first implementation record should list every changed
declaration and map its evidence to COV-001/COV-002 and PO-010/PO-011 without changing their status
until the corresponding gates are satisfied.
