# S03 data, widths, parameters, ADRS, and codecs session

Status: implementation candidate; full frozen gates pass; independent review pending.

Date: 2026-08-26
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: exact S02 commit
`a80e4d336276cd86fb80be64e82d9d57e7dfc8b3`, accepted with zero findings by
`reviews/S02-security-architecture-review-r8.md`. Historical `7b77e700` remains invalidated repair
evidence only and is not an S03 predecessor.

## Objective

Establish the width-safe data layer used by every later construction: the complete FIPS-approved
parameter family, exact address operations and serialization, big-endian integer and digit
extraction, and total encoders paired with rejecting decoders. S03 begins from accepted S00/S01
infrastructure and the exact independently accepted S02 interfaces; neither is a new review target.

## Authoritative inputs

- FIPS 205 Sections 3--5 and 11, including Table 1 address operations, Algorithms 2--4, and the
  twelve approved parameter sets in Table 2;
- the pinned FIPS profile in `docs/slhdsa/matrices/fips205-profile.json`, the S01 coverage and proof
  obligation matrices, and the reference pins in `docs/slhdsa/reference-manifest.json`;
- the accepted S02 candidate types imported through `HashSig.lean`, with no claim that the rejected
  legacy security theorem has been repaired; and
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

## Implementation inventory

- `ParameterSet` is a closed twelve-constructor FIPS family. `ParameterSet.profile` records the
  exact SHA2/SHAKE name, seven primary parameters, category, digest partitions, `m`, and public,
  secret, and signature widths. `profile_sizes`, `wots_widths`, and `ParameterSet.valid` evaluate by
  cases for all twelve rows. `LegacyParameterSet` separately owns SHA2-128-24, and
  `legacy_not_approved` excludes it from FIPS approval.
- `Encoding.lean` proves the radix-256 append law and `toInt` range, exposes the exact pointwise
  MSB-first `toByte` and `base2b` rules, and retains the two historical recursive helpers solely to
  preserve the reviewed exact-seven compiler-helper boundary. Checked conversion rejects overflow,
  zero digit width, insufficient input, and wrong fixed lengths; vector encode/decode roundtrip is
  proved.
- `Address.lean` retains plain setters for construction code under algorithmic preconditions and
  adds checked 32-bit/96-bit setters for external values. It proves type-and-clear fields, exact
  32/22-byte lengths, parses exact 32-byte carriers, rejects unknown types and noncanonical
  type-specific padding, and proves canonical wire decode/encode identity. SHA2 compression rejects
  values that do not fit its narrower one-byte layer and eight-byte tree fields.
- New `Codec.lean` gives opaque exact-width public-key, secret-key, and signature carriers for every
  approved profile. Each decoder rejects short and long inputs; each encoder/decoder roundtrip is
  proved. Semantic key/signature parsing remains later construction work.
- `DataCodecTests.lean` compares all twelve exact rows and derived partitions/sizes, exercises
  endian cases that cross byte boundaries, checks range/length/digit rejection, checks ADRS
  clear/serialization/compression/canonicality, and runs exact/short/long key and signature cases
  for every profile.

No construction, primitive instantiation, ACVP execution, external API, or security module changed.
COV-005 and F-015/F-016/F-018 remain explicitly deferred/open. The frozen descriptor/AST subsystem
was not changed; `validate.sh` only invokes the new independent S03 runtime executable.

## Gates

- `lake build HashSig` and focused test targets pass without new admissions;
- all approved parameter sets evaluate to their authoritative widths and sizes;
- roundtrip, rejection, range, endian, and address-clearing properties have executable fixtures and
  load-bearing proofs;
- existing ACVP fixtures are used only within their pinned provenance and schema-format scope;
- `git diff --check`, admission/source scans, and the frozen documentation harness pass; and
- a fresh reviewer authors `reviews/S03-data-codec-review.md`; this bootstrap does not create or
  pre-fill that verdict.

Focused evidence before the full handoff:

```text
lake build HashSig.SLHDSA.Address HashSig.SLHDSA.Codec
lake env lean scripts/slhdsa/PolicyAudit.lean
lake exe slhdsa_data_codec_tests
lake exe slhdsa_kat
lake exe slhdsa_c13_kat
lake exe mk_all --lib HashSig --module --check
bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh
```

All pass. The static audit observes 28 HashSig modules, 1,975 owned constants, exactly seven
reviewed compiler helpers, and the unchanged exact transitive-axiom union. The S03 executable
reports 12 exact profiles plus endian, ADRS, and rejection coverage; both inherited KATs still
accept the valid vector and reject the tampered input. These KATs remain legacy regression evidence
and are not FIPS/ACVP conformance evidence.

The complete `./scripts/slhdsa/validate.sh` wrapper also passes after these focused checks,
including the full repository build, frozen documentation/provenance checks, compiled policy
fixtures, generated umbrella check, and extern/interop isolation.

## Handoff

Commit the exact S03 candidate and request a fresh reviewer to author
`reviews/S03-data-codec-review.md`; do not pre-create that artifact or verdict. Preserve the
accepted S02 architecture boundary and treat primitive, construction, conformance, external-API,
and security proof work as successor sessions. COV-001/COV-002 and PO-010/PO-011 are implemented or
discharged pending independent S03 review, while COV-005 and F-015/F-016/F-018 do not move.

The S03 implementation payload is exact commit
`caefbda5e7ed7cd7a6efb80191307de7a39eea43`. The later documentation-only S04 bootstrap is part of
the successor-routing state, so independent S03 review must name and inspect the complete exact
descendant containing both the payload and that bootstrap. Accepting the payload commit alone would
leave the successor record outside the reviewed tree.
