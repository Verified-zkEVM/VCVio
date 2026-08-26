# Specification: current object and target object

## Fixed-width foundation

The target uses bytes and length-indexed byte strings, with explicit conversions and proved width
laws. `n,h,d,h',a,k,lgw` must satisfy positivity, `h=d*h'`, approved-set membership, digest-split
widths, and all index/address range constraints. Derived `w,len1,len2,len,m` and key/signature sizes
must be equal to FIPS formulas and evaluated for every approved set. Truncation, padding, modular
reduction, shifts, and big-endian `toInt`/`toByte` behavior require executable definitions and laws.

S03 keeps generic `Params` for existing constructions but adds a closed twelve-constructor
`ParameterSet`, exact `ParameterProfile` rows, executable approval/malformed-row rejection, and a
family-aware lookup with a proved exact constructor inverse, plus a proved `Params.Valid` witness
for every approved name. The SHA2-128-24 reduced profile is now a
separate `LegacyParameterSet` and evaluates as not FIPS-approved. Later construction APIs must carry
the approved name or its checked `Valid` witness rather than accept an arbitrary record silently.

## Parameters and representations

The normative profile has the following six tuples, each approved with both the `SHA2` and `SHAKE`
family, giving 12 simple instances. `h'` is per-layer height; public/signature sizes are FIPS Table 2
and secret-key size `4n` follows the key encoding. The checked copy is
`matrices/fips205-profile.json`.

| suffix | n | h | d | h' | a | k | lgw | m | category | pk | sk | signature |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 128s | 16 | 63 | 7 | 9 | 12 | 14 | 4 | 30 | 1 | 32 | 64 | 7,856 |
| 128f | 16 | 66 | 22 | 3 | 6 | 33 | 4 | 34 | 1 | 32 | 64 | 17,088 |
| 192s | 24 | 63 | 7 | 9 | 14 | 17 | 4 | 39 | 3 | 48 | 96 | 16,224 |
| 192f | 24 | 66 | 22 | 3 | 8 | 33 | 4 | 42 | 3 | 48 | 96 | 35,664 |
| 256s | 32 | 64 | 8 | 8 | 14 | 22 | 4 | 47 | 5 | 64 | 128 | 29,792 |
| 256f | 32 | 68 | 17 | 4 | 9 | 35 | 4 | 49 | 5 | 64 | 128 | 49,856 |

For example, `128s` denotes both `SLH-DSA-SHA2-128s` and `SLH-DSA-SHAKE-128s`; family is the
only difference within a paired row. The legacy 128-24 and C13 records remain distinct. Keys are
exactly
`SK.seed || SK.prf || PK.seed || PK.root` and `PK.seed || PK.root`; signatures are
`R || SIG_FORS || SIG_HT`. Decoders must reject wrong lengths and malformed fields rather than
silently pad/slice. Address fields, type tags, `setTypeAndClear`, the 32-byte encoding, and the
SHA2 compressed address require round-trip/noninterference/range lemmas. S03 provides the total
modulo and in-range reconstruction laws for big-endian `toByte`/`toInt`, checked 32-bit/96-bit
address setters, type-and-clear field laws, exact 32/22-byte length theorems, canonical type/padding
rejection, structured serialization/parser identity under exact field bounds, and checked-wire
decode semantics. Exact-width transparent key and signature carrier aliases reject every wrong
length for all twelve profiles; their semantic parsing remains construction work, not a claim of
conformance.

## Exact primitive instantiation grammars

All output lengths below are bytes unless the SHAKE call explicitly writes a bit length. `ADRS` is
32 bytes and `ADRS_c` is the FIPS 22-byte SHA2 compression.

For every SHAKE set:

```text
Hmsg(R,PK.seed,PK.root,M) = SHAKE256(R || PK.seed || PK.root || M, 8m)
PRF(PK.seed,SK.seed,ADRS) = SHAKE256(PK.seed || ADRS || SK.seed, 8n)
PRFmsg(SK.prf,opt_rand,M) = SHAKE256(SK.prf || opt_rand || M, 8n)
F(PK.seed,ADRS,M1)       = SHAKE256(PK.seed || ADRS || M1, 8n)
H(PK.seed,ADRS,M2)       = SHAKE256(PK.seed || ADRS || M2, 8n)
Tl(PK.seed,ADRS,Ml)      = SHAKE256(PK.seed || ADRS || Ml, 8n)
```

For SHA2 with `n=16`, `Hmsg` uses MGF1/SHA-256, `PRFmsg` uses HMAC-SHA-256, and every simple
tweakable hash uses SHA-256:

```text
Hmsg = MGF1-SHA-256(R || PK.seed || SHA-256(R || PK.seed || PK.root || M), m)
PRF  = Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || SK.seed))
PRFmsg = Trunc_n(HMAC-SHA-256(SK.prf, opt_rand || M))
F  = Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || M1))
H  = Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || M2))
Tl = Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || Ml))
```

For SHA2 with `n=24` or `32`, `Hmsg` changes to MGF1/SHA-512 and `PRFmsg` to HMAC-SHA-512;
`PRF` and `F` still use SHA-256/64-byte padding, while `H` and `Tl` use SHA-512/128-byte padding:

```text
Hmsg = MGF1-SHA-512(R || PK.seed || SHA-512(R || PK.seed || PK.root || M), m)
PRF  = Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || SK.seed))
PRFmsg = Trunc_n(HMAC-SHA-512(SK.prf, opt_rand || M))
F    = Trunc_n(SHA-256(PK.seed || toByte(0,64-n) || ADRS_c || M1))
H    = Trunc_n(SHA-512(PK.seed || toByte(0,128-n) || ADRS_c || M2))
Tl   = Trunc_n(SHA-512(PK.seed || toByte(0,128-n) || ADRS_c || Ml))
```

## Algorithm ladder

1. Common byte utilities and `base_2b`; WOTS checksum and chain.
2. ADRS and the `F,H,T_l,PRF,PRF_msg,H_msg` interface, with SHA2/SHAKE instantiations.
3. WOTS+ key generation, sign, and public-key recovery.
4. XMSS node/authentication path/sign/recovery.
5. FORS secret generation, node/sign/public-key recovery using FIPS big-endian `base_2b` indices.
6. A `d`-layer hypertree carrying exactly `d` XMSS signatures and the evolving tree/leaf indices.
7. Internal keygen/sign/verify with digest split `(md, idx_tree, idx_leaf)`.
8. External pure and pre-hash APIs with FIPS domain separation, context length checks, OID encoding,
   deterministic and hedged signing modes, and specified rejection behavior.

For each layer the target includes type/size equations, a deterministic correctness theorem, decoder
soundness, and executable evaluation. Structural correctness does not imply cryptographic security.

## Current implementation

The main tree is generic over opaque carriers and primitives but effectively implements only `d=1`:
`HtSig` is one XMSS signature; layer/tree are fixed to zero; `splitDigest` omits `idx_tree`. The
concrete SHA2-128-24 verifier uses fixed slices and an embedded C-reference regression vector. C13 is
a parallel WOTS+C/FORS+C construction with `d=2`, keccak, and conditional grind correctness. Neither
is the full FIPS205-12 external API.

## API contract

Target APIs distinguish:

- internal `keygen/sign/verify` on `M'`;
- external pure SLH-DSA constructs
  `M' = toByte(0,1) || toByte(|ctx|,1) || ctx || M`;
- external HashSLH-DSA constructs
  `M' = toByte(1,1) || toByte(|ctx|,1) || ctx || DER(OID(PH)) || PH(M)`;
- deterministic `opt_rand = PK.seed` and hedged/randomized input supplied by the caller/sampler;
- byte decoders returning an error/result, not total permissive slicing.

Both APIs reject `|ctx| > 255`. FIPS Algorithm 23 explicitly shows these DER encodings (tag and
length included): SHA-256 `0609608648016503040201` with 32-byte output, SHA-512
`0609608648016503040203` with 64-byte output, SHAKE128 `060960864801650304020B` with 32-byte
output, and SHAKE256 `060960864801650304020C` with 64-byte output. SHA-256 and SHAKE128 are only
appropriate for category 1. Other approved hashes/XOFs are allowed by FIPS if they provide at least
`8n` bits of classical collision and second-preimage strength (collision strength implies at least
`2n` digest bytes), and their signature identifier carries the function/OID and XOF output length.
The Lean API therefore must not incorrectly close the normative set at these four examples, but each
supported alternative needs an explicit checked OID/output/security-level record.

The pinned `FIPS205` protocol schema and current ACVP-Server v1.1.0.43 sample artifacts are parsed
with interface/pre-hash metadata; v1.1.0.38 is only the documented compatibility boundary. Positive
coverage is tracked per
parameter/hash cell because issue #469 prevents suite-wide PASS from establishing all bindings.
The parser accepts all twelve hash names advertised by that ACVP schema; it deliberately does not
apply FIPS pre-hash strength eligibility as an ACVP-schema filter. Normative FIPS eligibility and
OID/output-length obligations remain separate specification checks.

## Security surfaces

Security architecture precedes refactoring. It must expose the actual scheme public seed generated
inside the EUF-CMA game, not a theorem parameter disconnected from the key. S02 currently provides
an arbitrary signature-scheme experiment interface, which removes the direct call to the
transitional `d = 1` implementation but does not couple its fields to one general construction.
That construction/refinement witness remains open in S08/S09. Under proposed D-009,
formula-proved positive values are caps for the source-shaped
standalone component-game target oracles; actual traces may be shorter or empty, in which case a
selected-target event fails. They are not asserted to be an exact family extracted from the outer
EUF transcript. Adversary predicates enforce signing/hash-query bounds; transcripts record oracle
names, inputs, outputs, addresses, keys, message/context mode, and order. `Hmsg`/digest mapping gets
an ITSR game; `T_l` and the full tweakable-hash family are not omitted. `yToBytes`/encoding coherence
is a law when an abstract carrier is used.

Proposed D-006 selects the repaired tight EasyCrypt twelve-term theorem in classical `OracleComp`
semantics, and proposed D-009 selects its standalone component-game boundary. Neither proposal has
a named approver, so affected obligations remain pending and this prose does not treat either as an
accepted supersession. CCS 2019 Theorem 17 remains historical comparison authority, and no QROM
lifting or completed master proof is claimed. No invented `qS(qS+qH)/2^(8m)` loss is retained in
the candidate architecture.

## Computability

Normative algorithms, encoders, decoders, approved-set enumeration, and vector runners must evaluate
in Lean. Proof-only games may use noncomputable mathematics only behind an explicit abstraction
boundary paired with executable construction definitions. Every quantitative loss must be a finite
computable expression under checked side conditions and evaluated at all target sets. Elaboration
success is not runtime evidence; both are required.
