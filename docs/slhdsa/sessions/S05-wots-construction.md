# S05 WOTS+ construction

Status: accepted by independent r0 review with zero findings; candidate and review head pushed.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: exact pushed B01 acceptance head
`4161910f57d3634d667a9072bf5a7731b49e4467`; its parent contains independent B01 r1 review
`docs/slhdsa/reviews/B01-main-pr593-integration-review-r1.md`, which accepted the exact integration
repair with zero findings.

The S05 candidate normalizes only Markdown hard-break trailing spaces in that PASS artifact because
the already-active comprehensive whitespace gate otherwise rejects accepted head `4161910f...`.
Its historical review bytes remain recoverable unchanged as blob
`28896bd808150a24da4256297b004e5be517c95d` in the acceptance
commit; the r0 FAIL artifact remains untouched.

Independent review `docs/slhdsa/reviews/S05-wots-review-r0.md` accepted exact candidate
`33770467d9209d0e270db5edd7a88958641db2b2` (tree
`9c1f8a3239c85e31fa6eb37bc82f8b8dec44ce78`) with zero findings. The review artifact is committed
and pushed at exact head `7e029e660b9353f70e9de03ab4e6cc71f54e27da`.

## Scope and ownership

S05 supplies the missing FIPS 205 §5 WOTS+ checksum byte pipeline, connects it to the existing
oracle-parametric WOTS implementation, and retains the existing chain and correctness architecture.
It does not rewrite `chain_compose`, signature indexing, naturality/query-bound theorems,
`wotsPkFromSig_wotsSign`, checksum incomparability, generic security games, XMSS/FORS/hypertree
construction, or external APIs.

Concurrent PRs remain absent and reserved exactly as at B01: PR #595 exact inspected head
`be823fbb6745e95412efe2bf49e0e46055953413` owns `DigestParts` and typed `Position` across
S07--S09 (S07 digest splitting/FORS addressing; S08/S09 typed hypertree positions); PR #594 exact
head `c0930e49f74580fc8c0c22fbbffd8496df38972a` owns final-validity tweakable-hash games for S11+;
and PR #596 exact head `7068fd993e35748822d07bba922fe70fe2953cd9` owns DSPR, OpenPRE,
UD-C, and ITSR games for S11--S16. None is merged, imported, or duplicated by S05.

## Implementation

`HashSig/SLHDSA/WotsEncoding.lean` defines the normative Algorithms 7/8 line-6 pipeline:

- checksum bit width `len2 * lg_w`, ceiling byte width, and the exact FIPS padding shift
  `(8 - ((len2 * lg_w) mod 8)) mod 8`;
- shifted-value capacity, fixed-width big-endian `toByte` serialization, `base2b` checksum digits,
  exact lengths, and pointwise base-`w` bounds; and
- a kernel-checked theorem proving that the byte-derived checksum digits equal the existing
  mathematical `digitsOfBaseW` view under `Params.Valid`, message width, and digit-bound
  assumptions, followed by equality of the complete digit vectors.

`chainLengthsCore` now uses that FIPS byte pipeline operationally. Its old mathematical view,
intrinsic `len` width, element bounds, and all downstream WOTS definitions/correctness proofs are
preserved by new theorems rather than by a parallel implementation.

The WOTS address constructors now prove canonicality for four-byte chain/hash indices.
`HashSig/SLHDSA/Concrete/Wots.lean` carries those facts through `Sha2Address.ofAdrs`, showing that
WOTS PRF, every hash step, and public-key compression are accepted by the checked SHA2 boundary
when starting from a proof-carrying narrow base address.

## Discriminating and executable evidence

`HashSigTest/SLHDSA/WotsEncoding.lean` uses the existing limited `lg_w = 2`, `len1 = 64`,
`len2 = 4` profile. For 64 zero message digits it checks checksum `192`, shift `0`, one-byte
big-endian encoding `[0xc0]`, and checksum digits `[3,0,0,0]`. It separately evaluates the
historical shift-by-eight interpretation to truncated byte `[0]` and digits `[0,0,0,0]`, then
proves the two results unequal. Approved profiles are pinned to `lg_w = 4`, three checksum digits,
12 checksum bits, shift 4, and two bytes. No `native_decide`, admission, or widened trust is used.

`slhdsa_wots_tests` exercises `Concrete.approvedPrimitives` on deterministic fixed-width seeds,
message, and a canonical narrow address for all twelve approved SHA2/SHAKE profiles. It compares
`wotsSign` followed by `wotsPkFromSig` with `wotsPkGen`. For every SHA2 profile, before relying on
the equality, it explicitly sends the base, all actual WOTS PRF addresses, every chain/hash address
for `i < len` and `j < w - 1`, and the WOTS public-key address through `Sha2Address.ofAdrs` and
requires success. This is construction regression evidence, not an authoritative WOTS KAT or ACVP
conformance claim.

## Validation evidence

Focused checks passed warning-free apart from the documented optional-native-submodule stubs:

```text
lake build HashSig.SLHDSA.WotsEncoding HashSig.SLHDSA.Wots
Build completed successfully

lake build HashSig.SLHDSA.Concrete.Wots
Build completed successfully

lake build HashSigTest.SLHDSA.WotsEncoding
Build completed successfully

lake build slhdsa_wots_tests
Build completed successfully

lake exe slhdsa_wots_tests
SLH-DSA S05 WOTS+ construction tests: PASS
(SHA2/SHAKE; 12 profiles; checked SHA2 addresses)

lake env lean scripts/slhdsa/S05InventoryProbe.lean
S05 declaration/axiom probe: PASS (14 exact load-bearing roots)

lake build HashSig HashSigTest
Build completed successfully

lake exe mk_all --lib HashSig --module --check
No update necessary

bash scripts/check-extern-isolation.sh
Extern isolation check: OK.

bash scripts/check-interop-isolation.sh
Interop TCB isolation check: OK.

./scripts/slhdsa/validate.sh --docs-only
SLH-DSA docs-only validation: PASS
```

The S05 probe includes the byte-capacity/equivalence roots, operational chain-length equivalence,
length/bounds, all generic and checked SHA2 address roots, and retained
`wotsPkFromSig_wotsSign`. Its exact observed axiom union is limited to the existing standard
`propext`, `Classical.choice`, and `Quot.sound`; no root depends on `sorryAx`.

The authoritative `./scripts/slhdsa/validate.sh` was run once after every focused gate passed and
ended with `SLH-DSA full baseline validation: PASS`. It replayed the S05 probe and all-profile
runtime, fresh parser evidence, inherited KATs and component suites, generated imports,
isolation/provenance/hygiene, and the compiled policy. That policy observed 34 HashSig modules and
2,630 owned constants, retained exactly five compiler helpers, and retained the exact standard
axiom union. Expected warnings were confined to absent optional native submodules, upstream
non-HashSig admissions, and the policy's deliberate rejection fixtures.

## Acceptance

Independent r0 replayed the checksum arithmetic and byte-fit proof, the byte-to-mathematical digit
theorem at both approved and non-`lg_w = 4` widths, the operational WOTS switch, every address
boundary, the all-profile executable, retained correctness footprint, aggregate gates, and
ownership/absence of PRs #594--#596. Its zero-finding verdict accepts only the candidate above;
S06 begins from the committed and pushed review head.
