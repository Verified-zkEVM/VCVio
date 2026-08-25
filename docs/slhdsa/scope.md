# Scope and profile decisions

The prompt contains RISC-V/Sail/extractor language copied from a different audit. That language is
**template residue**: this repository has no identified RISC-V opcode or Sail refinement target in
the SLH-DSA work. The underlying obligations remain valid and are retained in scheme-appropriate
form: inventory all load-bearing declarations, expose the TCB, and prove refinement to the actual
deployment implementation once that implementation and interface are selected.

## Proposed profile decision matrix

These boundaries are the reviewed S00 working proposal, not maintainer-approved policy. Approval
state and evidence are tracked in `matrices/decisions.csv`; later implementation can proceed only
under the accepted session gates and must not convert a proposal into a deployment claim.

| Profile | Authority and purpose | Required target | Current state | Security/refinement claim |
|---|---|---|---|---|
| `FIPS205-12` | Normative FIPS 205 | All 12 SHA2/SHAKE `{128,192,256}{s,f}` parameter sets; internal and external pure/pre-hash APIs; exact encodings and algorithms | Missing; current main tree is `d=1`, one reduced set, empty-context hedged wrapper | Ultimately functional correctness, conformance evidence, and a precisely scoped EUF-CMA theorem |
| `SPX-TW-ABS` | Abstract SPHINCS+-TW security model, using CCS 2019 as historical statement/game input and HK22/EasyCrypt as repaired proof evidence | Parameterized WOTS-TW/FORS/XMSS-MT composition; actual PRF, tweakable-hash, ITSR, transcript, and query-bound games | Current `Security.lean` is a rejected placeholder | The theorem must state its classical/QROM model and exact coefficients; it is not itself a FIPS implementation |
| `SP800-230-IPD-6SET` | Non-normative NIST SP 800-230 Initial Public Draft authority/profile surface | Six proposed SHA2/SHAKE limited-signature sets at categories 1/3/5, kept separate from FIPS 205; strict `2^24` signatures/key cap | Exact six-row draft table pinned; no six-set implementation claim | Initial Public Draft, not a FIPS 205 Table-2 profile and not sufficient for FIPS conformance |
| `LEGACY-SHA2-128-24` | Existing single-set legacy current-code subprofile | Only SHA2-128-24, `n=16,h=22,d=1,h'=22,a=24,k=6,w=4` | Executable and complete for its abstract functions; one embedded regression vector | Distinct from `SP800-230-IPD-6SET`; no draft six-set, FIPS, or security claim |
| `C13-ETH` | Separate Ethereum-oriented C13 variant | WOTS+C, FORS+C, two-layer HT, keccak/EVM encoding, grind predicates | Executable verification and conditional deterministic correctness; no `SignatureAlg` or security theorem | Must receive an explicit keep/merge/deprecate decision and independent spec/security/refinement targets |
| `DEPLOY-TBD` | Concrete deployment/refinement boundary | Exact Ethereum L1 verifier/source revision, ABI, serialization, gas/word semantics, rejection behavior, and trusted tooling | **Blocked: target and source revision are unresolved** | No end-to-end deployment claim is permitted until the target is pinned and a refinement theorem is reviewed |

## In scope

- A byte- and width-faithful FIPS 205 executable specification for all 12 approved sets.
- Correctness, API behavior, encoding/decoding round trips, invalid-input behavior, and ACVP
  conformance evidence with pinned provenance.
- A clean abstract construction layer and an early, explicit security/oracle architecture.
- EUF-CMA/ITSR and component reductions with actual positive target counts, target distributions,
  public-seed coupling, query predicates, transcripts, and asymptotic interpretations.
- Classical and QROM claims kept distinct; executable computation kept available except where a
  documented proof-only abstraction has no executable role.
- TCB, assumption, declaration, coverage, and proof-obligation inventories.

## Out of scope unless a decision expands it

- Treating round-1/2/3 algorithms, robust/Haraka variants, or SPHINCS-256 as FIPS 205.
- Treating EasyCrypt abstractions as a byte-level FIPS implementation proof.
- Claiming that embedded C-reference vectors are NIST KAT or ACVP conformance.
- Fault, side-channel, timing, randomness-quality, key-erasure, or operational usage-cap proofs.
  These remain explicit operational boundaries, not implied guarantees.
- RISC-V/Sail refinement absent an identified artifact.

## Blocking decisions

S01 pins normative sources. S02 fixes the theorem/oracle architecture before construction refactors.
The C13 disposition is a dedicated decision session. Deployment work is blocked until `DEPLOY-TBD`
has an owner-approved repository, commit, ABI, and theorem boundary.
