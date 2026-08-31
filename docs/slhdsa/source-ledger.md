# Source ledger and authority rules

## Authority rules

1. A final NIST standard controls normative algorithm/API behavior. ACVP controls only the vector
   protocol and test evidence; it does not redefine FIPS 205.
2. CCS/ePrint/security papers and EasyCrypt are security authorities/evidence, not normative wire
   specifications. Exact theorem hypotheses and coefficients must be read from the primary text.
3. SPHINCS+ submissions and SP 800-230 are legacy/profile authorities only. Conflicts with FIPS 205
   are preserved as profile differences, never silently normalized.
4. Reference implementations and vectors are evidence. They can expose ambiguity or regression but
   cannot override the standard without an explicit standards erratum/decision.
5. Local reports are secondary research notes. The corrections below supersede their affected
   claims. Every load-bearing citation must resolve to a pinned primary source or be marked pending.

## Pinned local sources

`reference-manifest.json` is the canonical machine-readable ledger. `sibling:` locators resolve
against the parent of the VCVio repository by default (the supplied `/home/alh/SPHINCS` reference
bundle), or against `SLHDSA_REFERENCE_ROOT` when set. `repo:` locators resolve against VCVio. Thus
the paths below are unambiguous without baking this host's absolute path into the evidence format.
The S01 gate compares every key/value of each controlling FIPS, server, compatibility, protocol,
and SP IPD record; local file/git byte or revision verification is a separate mandatory check when
the sibling bundle is present. The repository record identifies the exact S02 repair input,
cross-checked against the active S02 session, and separately verifies that this fixed commit is an
ancestor of `HEAD`. Exact active Lean bytes are bound by the source-tree composite. This avoids a
self-referential future-commit field without accepting an arbitrary older ancestor as the declared
input.

| Class | Source | Revision/hash | Use |
|---|---|---|---|
| primary/normative | `sibling:NIST.FIPS.205.pdf` | 1,055,752 bytes; SHA-256 `8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d` | Current final FIPS 205 (2024-08-13): algorithms, all 12 sets, APIs, encodings |
| primary/non-normative draft | NIST SP 800-230 IPD | 282,069 bytes; SHA-256 `62d092f787a1f79260454bf332b642ff3b5b73dbcce2678a133a1406065e452e` | Six proposed limited-signature sets; Initial Public Draft only; strict `2^24` signatures/key cap |
| primary/security, repaired | `sibling:SPHINCS_EC.pdf` | SHA-256 `d1ca5fff2e7544c3591d665cd04a2e0f7454c0a2971388911eb6f6303c026001` | Paper accompanying the repaired tight EasyCrypt proof; preserve its abstraction/semantics boundary |
| primary/security, historical-invalidated | `sibling:papers/sphincsplus-framework-CCS2019.pdf` | SHA-256 `9b49545b61bc194f0d7793556b04ca8f2257990057e229f51164ce2aafe89aa6` | Exact historical Theorem 17 statement/games; its full tight proof is not authority after the WOTS flaw |
| primary/legacy-security | `sibling:papers/sphincsplus-r3.1-specification-2022.pdf` | SHA-256 `1169896fff4160e7a294162b8a3e061ffdf1888f3925f5614532c28bd3473c4a` | SPHINCS+ v3.1 bridge; not final FIPS extraction/checksum semantics |
| primary/security-evidence | `sibling:FV-SPHINCSPLUS-EC` | git `a28e4c53897a4bb57b575a177225862d48f824b7` | Abstract modular EasyCrypt proof; release requirements in its README |
| primary/legacy | `sibling:NIST-PQ-Submission-SPHINCS-20171130/Supporting_Documentation/sphincs.pdf` | SHA-256 `8365127b5619356a4ca0a122b44b0458a7e5d447cb8997a07c2e70e43b085bde` | Round 1 history only |
| primary/legacy | `sibling:NIST-PQ-Submission-SPHINCS-20190329/Supporting_Documentation/sphincs.pdf` | SHA-256 `58804cc62b4fbfac8e5f4e9df80639d719a7aaf13e706713ff605d168cbd2b23` | Round 2 history only |
| primary/legacy | `sibling:NIST-PQ-Submission-SPHINCS-20201001/Supporting_Documentation/sphincs.pdf` | SHA-256 `540968e4d58cb582d5f85636beed7a10894622ed8b99a7a863f85996869743c6` | Round 3 history only |
| primary/evidence | VCVio | repair base git `7b77e700b3d24a6ab94ed741a650954bbd90859a` | Invalidated S02 implementation retained only as exact repair input; active 28-file SLH-DSA source-tree composite pinned separately |
| secondary | `sibling:reports/00-SYNTHESIS.md` … `07-literature-and-resources.md` | hashes recorded below | Orientation only; corrected findings cannot be cited as primary authority |
| prompt | `sibling:prompt.md` | SHA-256 `2b40bca6253eeb3bcf84fa9178a66309509f446b07655e57342417319cd4d7cf` | Requirements; cryptographic claims require independent authority |

## S04 primitive authorities and vectors

FIPS 205 Section 11 remains the normative authority for composing the six SLH-DSA primitives.
The following exact editions and bytes control the constituent algorithms. Remote records are
pinned by URL, edition, byte size, and SHA-256 in `reference-manifest.json`; unlike sibling files,
the ordinary validation gate checks their metadata rather than redownloading them.

| Primitive | Controlling source | Exact pin | Load-bearing scope |
|---|---|---|---|
| SHA-256/SHA-512 | NIST FIPS 180-4, August 2015 update 1 | 833,315 bytes; SHA-256 `0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82` | Padding, big-endian length/word parsing, IVs, schedules, rounds; SHA-256 input below `2^64` bits and SHA-512 below `2^128` bits |
| SHAKE256 | NIST FIPS 202, August 2015 | 1,459,683 bytes; SHA-256 `1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e` | Keccak-f[1600], 1088-bit/136-byte rate, SHAKE suffix/domain, repeated squeezing |
| HMAC | NIST FIPS 198-1, July 2008 | 129,454 bytes; SHA-256 `67661ba1407b391c799ff407471de18f36697af51d78a777e817c067ac30da23` | HMAC construction and hash-then-pad keys; incorporated by FIPS 205 Section 11.2 |
| MGF1 | RFC 8017, November 2016, Appendix B.2.1 | 154,696 bytes; SHA-256 `1e72dc473d18df3fc5598cdc12795a9f18f36f1aef15abc23a55eb0d58151d11` | Four-byte big-endian counter, leading truncation, and `maskLen <= 2^32 hLen`; incorporated by FIPS 205 Section 11.2 |

The committed `HashSigTest/SLHDSA/PrimitiveVectors/vectors.json` projection is 8,950 bytes with
SHA-256 `b086e6e79d07e6fc64dbf6fad56219015d96f7c2c7a22fbfd4d699b27d6406ec`.
It identifies exact member hashes and cases from the pinned NIST CAVP SHA and SHAKE archives,
exact NIST HMAC and SHAKE example PDFs, algorithms, input/output lengths, and expected bytes. The
adjacent padding, absorb-rate, and all-profile fingerprint cases identify their independent
derivation. The two compact MGF1 cases are regression-only because RFC 8017 defines MGF1 but does
not publish a standalone KAT. NIST examples and CAVP response files are test evidence, not a NIST
validation certificate; profile fingerprints are independent composition evidence, not NIST
vectors. `PrimitiveVectors/NOTICE.md` preserves the NIST attribution/no-endorsement boundary and
the RFC/IETF copyright classification.

The VCVio composite is specifically SHA-256 of the 28-line GNU `sha256sum` manifest produced, in
C-locale glob order, by:

```text
LC_ALL=C sha256sum HashSig/SLHDSA/*.lean HashSig/SLHDSA/C13/*.lean \
  HashSig/SLHDSA/Concrete/*.lean HashSig/SLHDSA/Security/*.lean | sha256sum
```

Each manifest line is lowercase file hash, two ASCII spaces, repository-relative path, and LF. This
is a pinned recipe, not a path-independent Git tree object. The validator requires exact
command/glob correspondence, reproduces it directly, and copies the tree to a temporary fixture to
prove that one changed `Security/Architecture.lean` byte invalidates the recorded digest.

S01 resolves S00's SP 800-230 pinning obligation to the April 2026 Initial Public Draft at DOI
`10.6028/NIST.SP.800-230.ipd`. It is neither final nor part of FIPS 205, and its six limited-use sets
remain separate from the twelve-set normative profile. The draft's `2^24` signatures-per-key cap is
not optional operational advice. `SP800-230-IPD-6SET` names this six-set authority/profile surface;
`LEGACY-SHA2-128-24` separately names the single reduced parameter set implemented by current code.
Neither identifier implies the other surface is implemented or reviewed.
The normal gate registers every identity-bearing occurrence by exact path and normalized line across
canonical documents, S01 scripts, and the complete SLH-DSA test-support tree. This is a fail-closed
occurrence and structured-record policy; it does not claim general natural-language contradiction
detection for prose that contains neither registered identifier.
The active policy compares an ASCII-alphanumeric-only stream against each identity so
comment, newline, quote, backtick, or concatenation syntax cannot reconstruct an unregistered
spelling. On Linux, an identity-stable descriptor-relative scanner anchors the repository and every
active child, compares no-follow metadata to the opened device/inode/type, and rejects replacement
objects, symlinks, and special entries before reading. There is no weaker pathname fallback. The normative
profile artifact and every current matrix artifact have reviewed byte pins plus structured checks;
future accepted sessions must deliberately revise those pins when they revise the canonical data.

Local report SHA-256 values, in order 00 through 07, are:
`8ebeb4e6f2683606ded1e55e083c07e815b4ed42cf0c9774269c259d0c57b54f`,
`266d34b2b442b3e0ecbd7aaa601ec1c6d8d9fb353f288d8d87d7fc85c6cc71b1`,
`20844b0d0615fce97d11aedcb66b7502b509ff21f89aa3971e68803fd7ade831`,
`5f947b714fb3b661f535a3c0cd3b464ce7c1aa03b94b48999da6edefec3c03ff`,
`957d3f9c21a47d61edea7e493a29392fa2fa97cf9e90c9c39533f7f2baf52f94`,
`69bc4c8007dd1c82916a6bcdc65d03a32d480916f1c586843a62a22f5682562f`,
`f7ea6561d4d96448d78e715ccae8310cba799b154c4e8b248304e30698a9280b`, and
`f38c1deae24677188bbdb35a06c3373ce1c03f56dcfb9aef31a67bd0de6550d8`.

## Pinned NIST ACVP anchors (verified 2026-08-24)

- The algorithm protocol is the work-in-progress Internet-Draft
  `draft-livelsberger-acvp-slh-dsa-01`, not an ACVP “v1.1.0.38 schema.” Its repository is pinned at
  `892fd14710f3a7edbea230d0aecc5511e0257f8e`; the root AsciiDoc SHA-256 is
  `d9c7088a6bb0531b2a5ab65104f467a7abe0e5ffc4d22f8ec1b7b90978d7d061` and the root-plus-section
  composite is `bc38ec528afcaa7f6a8155fd75a7612166203c789a540c0ac42e860a04c40a54`.
  The pinned `-01` document is dated 2024-06-25; 2026 is only this evidence record's observation
  year, not the Internet-Draft publication year.
- ACVP-Server is pinned to current release v1.1.0.43, commit
  `975de31eb83d87039ec88934fdc47d8c312b892d`. Release v1.1.0.38 is only the external-interface
  server-format compatibility boundary, at exact commit
  `85f8742965b2691862079172982683757d8d91db`; pre-boundary sigGen/sigVer responses are incompatible.
- The 15 pinned files under the three `gen-val/json-files/SLH-DSA-*-FIPS205` directories are NIST
  GenVal **sample JSON** (`isSample = true`). They are not a validation certificate, separately
  approved KAT corpus, or proof of the Lean implementation. Every path, byte size, and SHA-256 is in
  `reference-manifest.json`; bounded local projections and their recipes are under
  `HashSigTest/SLHDSA/ACVP/fixtures/`.
- The repository's full NIST software notice is retained with the fixtures. Projections identify
  NIST as source and state their generation date, source commit/hash, selected IDs, and changes.

The current sample counts are keyGen 12 groups/120 tests, sigGen 72/624, and sigVer 36/504. SigVer
has 72 positive and 432 negative cases. For external pre-hash sigVer, only 24 of 144 exact
`(parameterSet, hashAlg)` cells have a positive case: every set lacks at least ten positive cells,
and SHA3-224 and SHAKE-128 have none anywhere. `positive-prehash-coverage.json` records all 144 cells
and the exact 24 positive pairs. Negative cases cannot establish correct OID/digest binding.

ACVP-Server issue #469 remains open. Proposed PR #471 also remains open and explicitly does not
regenerate the sample JSON, so it changes neither the pins nor the measurement. ACVP evidence is
reported only for covered cells and never extrapolated into FIPS conformance.

## Corrections that supersede the reports

- **CCS statement and invalid proof boundary:** CCS 2019 Theorem 17 states
  `PRF + PRFmsg + ITSR(Hmsg) + SM-TCR(Th) + 3*SM-TCR(F) + SM-DSPR(F)` with the theorem's
  separate query bounds. It is not `SM-TCR(H) + 3*SM-DSPR(F)`. Report 00 and report 07 summaries
  that use the latter shape are wrong. Separately, Kudinov, Kiktenko, and Fedorov exposed the WOTS
  reasoning error used by the CCS full tight proof, invalidating that full proof. Hülsing--Kudinov
  2022 repaired SPHINCS+ with explicit WOTS-TW notions; the local paper/EasyCrypt development later
  reconstructs and mechanizes that repaired architecture. The historical theorem text remains a
  comparison target, not sufficient proof authority. Its `3*TCR(F)+DSPR(F)` sub-bound was later
  reconstructed; it was not itself the identified WOTS error.
- **FORS extraction:** FIPS Appendix A records two distinct changes. One bit-extraction change was
  intended to align selection of a FORS key with the round-three reference implementation. A
  separate change clarified digest-to-per-tree FORS indices because the submission was ambiguous;
  the standardized method is not compatible with the submitted reference implementation's method.
  Algorithm 4's `base_2b` is MSB-first, while v3/3.1 prose enumerates bits LSB-first. Fixtures must
  identify which operation/version they exercise rather than collapsing both changes into a slogan.
- **WOTS checksum shift:** Appendix A separately changes line 6 of `wots_sign` and
  `wots_pkFromSig` to match the reference implementation. Submission pseudocode can shift `csum` by
  the wrong amount when `lgw != 4`; the FIPS formula controls even though all approved sets use 4.
- **EasyCrypt scope:** the local EasyCrypt development proves a parameterized, modular abstract
  SPHINCS+-TW security construction with abstract message/key/seed/hash operations, explicit parameter
  axioms, and game assumptions in EasyCrypt's classical probabilistic game semantics. It supports a
  repaired proof intended for post-quantum assumptions, but does not mechanize quantum adversaries,
  a QROM oracle semantics, or a quantum lifting/bound. It is strong security-proof evidence, but not
  a byte-level FIPS implementation, all-set conformance proof, concrete-hash proof, or deployment
  refinement. Reports implying those stronger scopes are corrected here.

## Reproduction status

The VCVio baseline commands were run and passed as recorded in the index. EasyCrypt was absent from
`PATH` and was not rerun; do not report its local checkout as reproduced until the pinned release and
solvers complete `make check` (or the documented container equivalent).
