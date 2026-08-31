# SLH-DSA formalization harness

This directory is the canonical index and gate record for the SLH-DSA/SPHINCS+ work. It separates
the normative FIPS 205 target, the abstract security model, the legacy reduced implementation, the
C13 construction, and any future deployment refinement. A passing regression test is never treated
as standards conformance or as a security proof.

## Current gate

S00 through S04 are accepted at their recorded independent review boundaries. B01 then reconciled
that work with upstream main and PR #593; independent B01 r1 accepted exact repair commit
`1f3cfa89882af79755e87d90659edd7150186416` with zero findings, and its artifact is committed and
pushed at exact head `4161910f57d3634d667a9072bf5a7731b49e4467`.
S01 reviews r0 through r15 are immutable **FAIL** artifacts. Independent r16 is **PASS**, so S01 is accepted and S02 is eligible to start.

Independent S05 r0 accepted exact candidate `33770467d9209d0e270db5edd7a88958641db2b2`
with zero findings; its review artifact is committed and pushed at exact head
`7e029e660b9353f70e9de03ab4e6cc71f54e27da`.

Independent S06 r0 accepted exact candidate `91845ddfa8a704400600fdbf1c64f82659c4ca52`
with zero findings; its review artifact is committed and pushed at exact head
`91e97865f4d1c91fac18172e41d91000142194de`.

B02 and its remote reconciliation are independently accepted at reviewed head
`609185098935feea82f4d5b6fb7a9d62aefce9c9`. Independent B03 r2 accepted the repaired integration
candidate `23a85b6db2dd57e79a5dfab67a31b6d121193b57` with zero findings; its immutable review artifact
is recorded at `e6ad65272816dfe78e0f2f5e6a0dccf5f3032cd1`. The B03
normal merge series first imported `fe469308b758ac381b770fb83cee4a7f792400cd`, then folded exact
latest shared head `2014783d7d461b64164e3ec2844ce7f1eeb4c846` into merge
`8917b7edb64614ab5417575a383abab15e396f2e` without rewriting either history.
Independent B03 r0 reviewed candidate `157855d88b9bc550de5964bdd90d112ee16ae9dd`
with no blocking technical finding but failed it on three active-document inconsistencies. Its
immutable FAIL artifact is committed at `17f1b060861a146b0bd2c4e67b0a7637b788feb4`; r1 found one
remaining index inconsistency, and r2 accepted its exact repair.

B03 imports intrinsic XMSS/FORS signatures, typed-position arbitrary-depth hypertree and general
internal-scheme programs, their naturality/deterministic interpretations, and structural finite
query upper bounds. Kernel theorems now close arbitrary-depth pure/fixed-answer hypertree correctness
and general internal sign/verify completeness. A Medium gap remains between the callback-parametric
`*With` layer and the explicit-query/pure interpretations, and S07 fixtures/address/runtime plus S09
codecs/external APIs remain open. Depth-one output compatibility is proved, while general signing
performs the FIPS-mandated discarded final recovery and therefore has a longer free-oracle trace.

The exact SUF advantage partition and structural FORS/XMSS/WOTS reachable-target ledgers are useful
security infrastructure, not reductions. The same-message SUF residual is unbounded; structural
address/count/Nodup facts do not yet establish encoded injectivity, nonempty distinct-target batch
packaging, actual-query coverage, target-input pairing, or final-validity/disjointness.

B04 history-preservingly imports the canonical PR #594/#596 generic games and adds thin SLH-DSA
problem instantiations plus WOTS construction-address trace contracts. `CanonicalGames` and
`TraceTargets` are conditional infrastructure: `CountingInterface`, an inhabitant of
`ReductionAdversaries`, outer-CMA signing-log refinement, FORS/XMSS/hypertree trace bridges,
old-to-canonical experiment equivalences, and the master inequality remain open. The security
interface still assumes `ReductionSystem`, and `RepairedMasterStatement` remains an unproved
`Prop`. PR #585 theorem content may be ported but never raw-merged, and cumulative PR #591 remains
reserved for S15.

S01's pinned authority, provenance, and strict sample-schema parser anchors remain schema/provenance
evidence rather than implementation conformance. Its descriptor/AST machinery is frozen absent a
concrete regression. The B01 HashSig aggregate has no admission exception; the S02 replacement
security architecture remains a reviewed candidate architecture rather than a completed reduction
or top-level theorem, and D-006/D-009 remain proposed.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true

## Canonical documents

- [Scope and profiles](scope.md)
- [Source ledger and authority rules](source-ledger.md), with checked
  [reference manifest](reference-manifest.json)
- [Specification](specification.md)
- [Lean blueprint](lean-blueprint.md)
- [Session plan](plan.md)
- [Proof obligations](proof-obligations.md)
- [Review protocol](review-protocol.md)
- [Validation gates](validation.md)
- [Decisions](decisions.md) and [findings](findings.md)
- [Session records](sessions/README.md), [reviews](reviews/README.md), and [report](report/README.md)
- Machine-readable [matrices](matrices/), including the exact
  [FIPS profile/API/primitive record](matrices/fips205-profile.json) and
  [non-normative SP 800-230 IPD profile](matrices/sp800-230-ipd-profile.json), plus
  [decision approvals](matrices/decisions.csv)

## Gate commands

```text
./scripts/slhdsa/validate.sh --docs-only
./scripts/slhdsa/validate.sh
python3 -B scripts/slhdsa/check-acvp-provenance.py
lake exe slhdsa_acvp_parser
```

The first command validates harness structure and the defense-in-depth source policy without
building libraries or running algorithms; it does re-elaborate Lake configuration into disposable
TOML to verify the parser target and absence of effective source-directory/path-argument selectors.
The second also checks the HashSig build, the authoritative elaborated-environment policy audit and
compiled negative fixtures, generated umbrella, isolation rules, inherited KATs, S03 codecs, S04
primitives, S05 WOTS construction, S06 XMSS construction, the B02 digest/position and B03
construction/query/interface declaration probes, and the S01 provenance/strict-parser runtime gates. Immediately
before the parser
runtime, it reconfigures, rehashes, and disables caches while building into an initially absent
private output root. It attests all three frozen parser/schema source-to-object-to-executable chains,
requires the exact 24-file current module/C/object/trace/sidecar manifest with trace-token agreement,
computes SHA-256 over the fresh executable through a descriptor-relative no-follow traversal before
and after executing that exact resolved ordinary binary, and rejects every alias or artifact outside
the fresh root. Every production descriptor path uses one non-retrying owner/cleanup helper: active
exceptions retain their exact identity while every owner is attempted once, and nominal cleanup
reports one deterministic failure only after all owners are attempted. The temporary Lake
build-directory override is restored before deleting its temp
root on ordinary exit, errors, errexit, and handled signals; SIGKILL cannot execute a shell EXIT
trap. The two
standalone commands expose provenance and runtime behavior respectively;
only the full wrapper binds runtime behavior to the attested source trace. Report compilation is
documented separately
because TeX availability is an environment property.

## Baseline evidence (2026-08-24)

- VCVio commit `f1853af40da1efa11a71c2d7011996eebdbf6938`, branch
  `codex/sphincsplus-formalization`; Lean `v4.32.2`.
- `lake build`: PASS, 3008 jobs, with inherited sorries outside this work.
- `lake build HashSig`: PASS, 2744 jobs, with the one local security `sorry` above.
- `lake exe slhdsa_kat` and `lake exe slhdsa_c13_kat`: runtime PASS.
- `lake exe mk_all --lib HashSig --module --check`, extern isolation, and interop isolation: PASS.
- EasyCrypt was not on `PATH` and was not rerun. Its local revision is recorded, but its proof status
  is cited as external evidence rather than reproduced evidence.

These are captured observations. Re-review must rerun the relevant commands; job counts are not
semantic invariants.
