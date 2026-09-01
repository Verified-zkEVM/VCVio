# Scope and profiles

| Profile | Authority and purpose | Required target | Current state | Security/refinement claim |
|---|---|---|---|---|
| `FIPS205-12` | Normative FIPS 205 | All twelve approved sets and internal/external APIs | Internal arbitrary-depth construction is modeled | External APIs codecs ACVP coverage and security remain open |
| `SPX-TW-ABS` | Repaired classical SPHINCS+-TW proof sources | Exact games reductions and composition | Conditional games and target infrastructure exist | Reductions SUF residual master inequality asymptotics and QROM remain open |
| `SP800-230-IPD-6SET` | NIST SP 800-230 Initial Public Draft | Six proposed limited-signature sets and strict `2^24` signatures/key cap | Exact draft rows and metadata are pinned | Non-normative and no implementation claim |
| `LEGACY-SHA2-128-24` | Repository regression profile | One reduced depth-one profile | Abstract/concrete runtime regression | Not FIPS the six-set draft or a security claim |
| `C13-ETH` | Separate Ethereum-oriented variant | C13 construction and its own authority | Executable verification and conditional facts | No FIPS security or deployment-refinement claim |
| `DEPLOY-TBD` | Future selected implementation | Pinned repository revision ABI and toolchain | Blocked because no target is selected | No end-to-end refinement claim |

## In scope

- Byte- and width-faithful FIPS 205 construction for all twelve approved sets.
- Construction correctness, address/codec laws, invalid-input behavior, and evidence with pinned
  provenance.
- Explicit classical security games, transcripts, query predicates, component reductions, and
  exact finite/asymptotic bounds.
- A separately stated QROM model if one is implemented.
- A separately pinned executable-to-deployment refinement theorem.

## Explicit non-claims

- Round-1/2/3, robust/Haraka, SPHINCS-256, the draft six-set profile, and C13 are not FIPS 205
  profiles.
- EasyCrypt security evidence is not a byte-level FIPS implementation proof.
- Embedded or derived vectors are not NIST KAT/ACVP certificates.
- No fault, side-channel, timing, entropy-quality, key-erasure, usage-cap, or availability proof is
  implied.
- No deployment or RISC-V/Sail refinement is claimed without a selected target artifact.
