# S05 WOTS+ construction review r0

Verdict: **PASS**

Date: 2026-08-31
Reviewer: fresh independent technical reviewer (not the S05 implementer)
Reviewed candidate: `33770467d9209d0e270db5edd7a88958641db2b2`
Candidate tree: `9c1f8a3239c85e31fa6eb37bc82f8b8dec44ce78`
Required accepted parent: `4161910f57d3634d667a9072bf5a7731b49e4467`

## Repository state and scope

The review began with a clean worktree at the exact candidate, whose sole parent was the required
accepted and pushed B01 boundary. The candidate has the expected tree. I read the current
`AGENTS.md`, S05 plan and session record, every candidate diff, and the complete load-bearing Lean
modules and tests. I made no implementation or documentation changes while reviewing. This file is
the only review output and the only file to be committed by the reviewer.

The candidate changes 24 files relative to B01. Its Lean payload is confined to the checksum
encoding, WOTS integration and address lemmas, concrete WOTS boundary corollaries, aggregate
imports, and focused tests. Lake and validation changes add the one S05 executable and probe.
The remaining changes are the S05 inventory, matrices, provenance, plan/session, and gate records.
There is no S06 payload and no new security-game or typed-position implementation.

The candidate deliberately removes Markdown hard-break trailing spaces from the accepted B01 r1
review. The historical r1 bytes remain blob `28896bd808150a24da4256297b004e5be517c95d`
at the accepted commit, while the candidate blob is
`5c737bad1f62ec1961145d88dec4b73d401d5dee`. The immutable B01 r0 FAIL artifact remains the exact
same blob, `4672c4a87d37f093c458264001542e13aad6e7e5`, at parent and candidate.

## Checksum semantics and kernel bridge

`WotsEncoding` implements the FIPS 205 Algorithms 7/8 line-6 pipeline directly:

- `checksumBitLength = len2 * lgw`;
- `checksumByteLength = (checksumBitLength + 7) / 8`;
- `checksumShift = (8 - checksumBitLength % 8) % 8`, including the essential outer modulus;
- the checksum is left-shifted by that padding, serialized by fixed-width big-endian `toByte`,
  and decoded by MSB-first `base2b` into exactly `len2` digits.

The arithmetic proof is not a width-only or executable surrogate. `ceil8_padding` proves the byte
capacity is exactly meaningful bits plus padding. `wotsChecksumValue_lt_pow` derives the
`w^len2` capacity from `Params.len2`, the valid positive Winternitz exponent, exact message-digit
length, and pointwise digit bounds. `shifted_fit` then proves the padded integer is below the exact
`256^checksumByteLength` bound, so `toInt_toByte` is used only in its non-truncating range.

The private byte-to-digit bridge compares equal `List.range len` maps. For every in-range output
index it aligns the big-endian extraction exponent with `b * (len - 1 - i)` plus the padding,
divides out the positive padding factor, and rewrites `(2^b)^k`. Thus its public consequence
`checksumDigits_eq_digitsOfBaseW` has the correct orientation and proves equality of actual byte
pipeline output with the pre-existing mathematical fixed-width digits. The assumptions are
non-vacuous at operational use: `base2b_length` supplies the exact `len1`, `base2b_lt` supplies the
digit bound, and `Params.Valid` supplies positive/aligned WOTS parameters. No overflow,
zero-filled-tail, or Algorithm 3 truncation loophole remains. `fullDigits_eq_wotsFullDigits` then
connects the complete message-plus-checksum vector.

The independent non-four-bit canary elaborated successfully for the limited valid profile
`lgw = 2`, `len1 = 64`, `len2 = 4`: 64 zero digits give checksum 192, eight checksum bits, shift
zero, byte `[0xc0]`, and digits `[3, 0, 0, 0]`. The separately evaluated historical shift-by-eight
path truncates to byte `[0]` and digits `[0, 0, 0, 0]`; the inequality is proved. The approved-set
pin exhaustively confirms all twelve profiles have `(lgw,len2,bits,shift,bytes) = (4,3,12,4,2)`.

## Operational WOTS and address boundary

`chainLengthsCore` now calls `WotsEncoding.fullDigits` itself; the FIPS pipeline is operational,
not merely related to a dead alternate definition. Its intrinsic length and element-bound theorems
follow directly from the operational list. For valid parameters,
`chainLengthsCore_eq_wotsFullDigits` supplies the exact mathematical view used by later security
reasoning.

The candidate does not modify `chainWith`, `chainM`, `chain_compose`, WOTS signature indexing,
public-hash naturality, query bounds, deterministic oracle interpretations, or the honest recovery
argument. The retained `wotsPkFromSig_wotsSign` still extends each signed chain by
`w - 1 - chainStepsCore` and invokes the unchanged assumption-free `chain_compose`; it has not been
reproved under an artificial validity or hash hypothesis. The oracle-parametric WOTS architecture
therefore remains intact.

The generic address theorems correctly follow the actual constructors: `WOTS_PRF` and `WOTS_HASH`
clear the type-dependent fields, restore the base key-pair field, and set the chain field;
hash steps then set the hash field; `WOTS_PK` clears fields and restores the key-pair field. A
canonical base plus four-byte chain/hash fits is sufficient for each derived address. The concrete
corollaries additionally preserve the checked base's one-byte layer and twelve-byte tree bounds,
then prove `Sha2Address.ofAdrs` success for secret derivation, each chain step, and public-key
compression.

The all-profile executable is substantive and exhaustive over `FipsParameterSet.all`. Its match
has an explicit branch for every SHA2/SHAKE width; fixed seeds, public seeds, and messages use
distinct salts and nonempty fixed-width vectors. Every branch runs sign, recovery, and generation
through the exact `Concrete.approvedPrimitives` bundle and compares the recovered/generated byte
values. Before each SHA2 comparison it rejects failure for the base, every PRF address with
`i < len`, every hash-step address with `i < len` and `j < w - 1`, and WOTS-PK compression. These
ranges cover the addresses actually reachable by generation and the signing/recovery partition,
so the total SHA2 adapter's zero fallback cannot mask the runtime result. SHAKE retains its full
32-byte address key and is exercised for every width.

## Trust, imports, ownership, and records

The candidate adds no `sorry`, axiom, `native_decide`, unsafe/native implementation bridge, or
trust shortcut. The focused probe checked 14 load-bearing roots: byte-width/capacity/equivalence,
operational equality/length/bounds, generic and concrete address theorems, and retained WOTS
correctness. The exact observed union is only `propext`, `Classical.choice`, and `Quot.sound`;
individual expected subsets match. The authoritative policy independently observed 34 HashSig
modules, 2,630 owned constants, the exact same standard axiom union, and exactly five justified
compiler-generated `_unsafe_rec` helpers.

Aggregate imports, Lake configuration, declaration inventory, coverage/proof-obligation matrices,
source ledger, reference manifest, validation record, S05 session, and review handoff consistently
describe construction correctness and executable regression evidence. They do not claim an
authoritative WOTS KAT, ACVP conformance, hash refinement theorem, or security reduction.

Exact PR #595 head `be823fbb6745e95412efe2bf49e0e46055953413`, PR #594 head
`c0930e49f74580fc8c0c22fbbffd8496df38972a`, and PR #596 head
`7068fd993e35748822d07bba922fe70fe2953cd9` are all non-ancestors of the candidate. No candidate
diff adds `DigestParts`, typed `Position`, or Security payload; `HashSig/SLHDSA/Position.lean`
remains absent. The active records reserve PR #595 across S07--S09, PR #594 for S11+, and PR #596
for S11--S16, with their exact division of ownership.

## Commands and independent evidence

All commands below were run from `/home/alh/SPHINCS/VCV-io` at the exact candidate unless the
command explicitly names another revision.

```text
git status --short
  PASS: empty at review start
git rev-parse HEAD HEAD^ HEAD^{tree}
  33770467d9209d0e270db5edd7a88958641db2b2
  4161910f57d3634d667a9072bf5a7731b49e4467
  9c1f8a3239c85e31fa6eb37bc82f8b8dec44ce78
git diff --check 4161910f...33770467...
  PASS

lake env lean HashSigTest/SLHDSA/WotsEncoding.lean
  PASS
lake build HashSig.SLHDSA.WotsEncoding HashSig.SLHDSA.Concrete.Wots \
  HashSig.SLHDSA.Wots HashSigTest.SLHDSA.WotsEncoding \
  HashSigTest.SLHDSA.WotsConstructionTests
  Build completed successfully (2685 jobs).
lake exe slhdsa_wots_tests
  SLH-DSA S05 WOTS+ construction tests: PASS
  (SHA2/SHAKE; 12 profiles; checked SHA2 addresses)
lake env lean scripts/slhdsa/S05InventoryProbe.lean
  S05 declaration/axiom probe: PASS (14 exact load-bearing roots)

lake exe mk_all --lib HashSig --module --check
  No update necessary
bash scripts/check-extern-isolation.sh
  Extern isolation check: OK.
bash scripts/check-interop-isolation.sh
  Interop TCB isolation check: OK.

git merge-base --is-ancestor be823fbb6745e95412efe2bf49e0e46055953413 HEAD
git merge-base --is-ancestor c0930e49f74580fc8c0c22fbbffd8496df38972a HEAD
git merge-base --is-ancestor 7068fd993e35748822d07bba922fe70fe2953cd9 HEAD
  PASS: all three exit 1 (non-ancestors)
git rev-parse 4161910f...:docs/slhdsa/reviews/B01-main-pr593-integration-review-r0.md \
  HEAD:docs/slhdsa/reviews/B01-main-pr593-integration-review-r0.md
  PASS: both 4672c4a87d37f093c458264001542e13aad6e7e5

./scripts/slhdsa/validate.sh
  SLH-DSA harness check: PASS
  SLH-DSA ACVP provenance: PASS
  fresh parser/runtime and mutation gates: PASS
  S03/S04/S05 declaration and axiom probes: PASS
  compiler-helper allowlist: PASS (5 exact `_unsafe_rec` auxiliaries)
  HashSig inventory: 2630 owned constants; exact axiom union
    [propext, Classical.choice, Quot.sound]
  HashSig elaborated policy audit and fixtures: PASS
  generated aggregate and isolation: PASS
  inherited KAT, C13, codec, primitive, and WOTS executables: PASS
  SLH-DSA full baseline validation: PASS
```

The wrapper warnings were expected and outside the reviewed trust boundary: absent optional native
submodules produce empty unused stubs, upstream non-HashSig modules contain known admissions, and
the policy fixture intentionally elaborates rejected `sorry` declarations. None changes the exact
HashSig policy result or the reviewed executable behavior.

## Findings and verdict

Blocking findings: **0**.

Nonblocking findings: **0**.

The exact S05 candidate passes. The FIPS checksum byte pipeline is operational and kernel-connected
to the mathematical WOTS view without truncation or orientation gaps; the non-four-bit canary is
discriminating; WOTS correctness and oracle structure remain intact; reachable SHA2 WOTS addresses
are checked rather than hidden by fallback behavior; all twelve concrete profiles run; trust and
ownership boundaries remain exact. This review accepts only candidate
`33770467d9209d0e270db5edd7a88958641db2b2` and does not implement S06 or authorize any unreviewed
descendant.
