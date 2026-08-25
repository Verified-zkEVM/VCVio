# SLH-DSA formalization harness

This directory is the canonical index and gate record for the SLH-DSA/SPHINCS+ work. It separates
the normative FIPS 205 target, the abstract security model, the legacy reduced implementation, the
C13 construction, and any future deployment refinement. A passing regression test is never treated
as standards conformance or as a security proof.

## Current gate

Session S00 is **accepted by independent re-review r9** after eight preserved review failures and
their evidence-backed dispositions. S01 reviews r0 through r15 are immutable **FAIL** artifacts.
Independent r16 is **PASS**, so S01 is accepted and S02 is eligible to start. S02
security-architecture reviews r1 through r3 are immutable **FAIL** artifacts; r4 initially passed,
but the complete independent r5 audit found six blockers and invalidated that acceptance. The
repaired S02 tree is pending r6, and S03 remains blocked until r6 passes.
S01's pinned authority, provenance, and strict sample-schema parser anchors do not claim
implementation conformance. R16
accepted the F-061/F-062 repairs: cleanup uses constant/count-only evidence, preflights
descriptor aliases before closing each unique integer once, and gates an exact scoped AST ownership
lifecycle. This machinery is now frozen: later sessions should center on Lean deliverables and must
not ratchet or reopen the descriptor/AST policy without a concrete regression. The allowlisted `sorry` remains the body of
`SLHDSA.slhdsa_euf_cma_security`, whose declaration begins at
`HashSig/SLHDSA/Security.lean:150` (the token is currently at line 175). This is an open critical
proof obligation, not an accepted axiom. The repaired S02 modules define the proposed replacement
architecture and standalone component-game boundary; they do not prove or replace that legacy
composition theorem, and they are not accepted until r6.

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
The second also checks the HashSig build, the authoritative elaborated-environment
policy audit and compiled negative fixtures, generated umbrella, isolation rules, and both runtime
regressions, plus the S01 provenance and strict-parser runtime gates. Immediately before the parser
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
