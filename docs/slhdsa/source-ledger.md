# Source ledger and authority rules

`reference-manifest.json` is the machine-readable authority ledger. Sibling locators resolve from
the parent of the repository unless `SLHDSA_REFERENCE_ROOT` is set; repository locators resolve from
the repository root. Exact local bytes/revisions and the active SLH-DSA Lean source composite are
checked separately.

## Authority order

1. Final NIST standards control normative construction, encoding, and API behavior.
2. ACVP specifies test protocol/evidence; sample JSON is not a validation certificate and does not
   redefine FIPS 205.
3. Security papers and the EasyCrypt development control only the abstract theorem/game boundary.
4. Submissions, draft profiles, implementations, and derived vectors are profile or regression
   evidence and cannot override final FIPS text.

## Primary bibliography

| Source | Stable citation | Use |
|---|---|---|
| NIST FIPS 205, *Stateless Hash-Based Digital Signature Standard* (2024) | DOI `10.6028/NIST.FIPS.205`; exact PDF bytes pinned | Normative twelve-set algorithms, encodings, and APIs |
| Dang and Moody, *Additional SLH-DSA Parameter Sets for Limited-Signature Use Cases* (2026 IPD) | DOI `10.6028/NIST.SP.800-230.ipd`; exact PDF bytes pinned | Non-normative six-set draft profile and `2^24` signatures/key cap |
| Barbosa, Dupressoir, Hülsing, Meijers, and Strub, *A Tight Security Proof for SPHINCS+, Formally Verified* (2024) | Cryptology ePrint `2024/910`; exact local PDF and EasyCrypt revision pinned | Repaired classical modular proof evidence |
| Bernstein, Hülsing, Kölbl, Niederhagen, Rijneveld, and Schwabe, *The SPHINCS+ Signature Framework* (CCS 2019) | DOI `10.1145/3319535.3363229`; exact PDF bytes pinned | Historical theorem/game boundary; the invalid WOTS reasoning is not reused |
| Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+* (ASIACRYPT 2022, LNCS 13794, pp. 3-33) | DOI `10.1007/978-3-031-22966-4_1` | WOTS-TW repair boundary |
| Livelsberger, *ACVP SLH-DSA JSON Specification* (Internet-Draft, 2024-06-25) | `draft-livelsberger-acvp-slh-dsa-01`; exact repository revision/composite pinned | ACVP schema and sample-interface metadata |

## Primitive authorities and evidence

FIPS 205 Section 11 defines the SLH-DSA primitive composition. FIPS 180-4 controls SHA-256 and
SHA-512; FIPS 202 controls SHAKE256; FIPS 198-1 controls HMAC; RFC 8017 Appendix B.2.1 controls
MGF1. Editions, URLs, sizes, and SHA-256 values are pinned in the manifest.

`HashSigTest/SLHDSA/PrimitiveVectors/vectors.json` is a checked projection of pinned NIST SHA,
SHAKE, and HMAC evidence plus explicitly labeled derived boundary regressions. NIST examples and
CAVP response files are not a validation certificate. MGF1 compact cases, SHAKE rate-boundary
cases, and profile fingerprints are regression evidence only.

The active source composite is the SHA-256 of the C-locale `sha256sum` manifest for:

```text
HashSig/SLHDSA/*.lean
HashSig/SLHDSA/C13/*.lean
HashSig/SLHDSA/Concrete/*.lean
HashSig/SLHDSA/HypertreeGeneral/*.lean
HashSig/SLHDSA/Security/*.lean
```

Each manifest record is a lowercase hash, two spaces, repository-relative path, and LF. The
validator checks the recipe, current bytes, and a mutation canary.

## ACVP boundary

The ACVP protocol repository, ACVP-Server release, format-compatibility revision, 15 GenVal sample
files, projections, and hashes are pinned in the manifest and fixture provenance. The samples have
`isSample = true`. Current sample counts are keyGen 12 groups/120 tests, sigGen 72/624, and sigVer
36/504. Only 24 of 144 external pre-hash `(parameterSet, hashAlg)` cells contain a positive sigVer
case; negative cases do not establish correct OID/digest binding. Open ACVP-Server issue #469 and
its unregenerated proposed fix prevent extrapolation to complete implementation conformance.

## Normative corrections

- FIPS Algorithm 4 is MSB-first. The separate historical FORS key-selection and per-tree-index
  changes must not be collapsed into one bit-order claim.
- FIPS WOTS signing and recovery use the outer-mod checksum shift
  `(8 - (len2 * lgw mod 8)) mod 8`; submission pseudocode is not controlling for other widths.
- The repaired classical theorem uses challenger-owned component games and the WOTS-TW
  UD-C/TCR-C/PRE-C repair. Historical CCS text remains comparison authority, not a completed proof.
- The EasyCrypt development is abstract classical security evidence. It is not a byte-level FIPS
  refinement, a QROM mechanization, or a deployment theorem.

## Reproduction boundary

The local EasyCrypt checkout is pinned but is not treated as reproduced unless its declared tool
and solver versions complete the documented check. External sibling research notes remain secondary
orientation sources with exact hashes in the manifest; no technical claim depends on them instead
of a pinned primary source.
