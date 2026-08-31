# B03 concurrent construction/query/security-stack integration

Status: integration implementation complete. Independent r0 found no blocking Lean issue and three
active-document inconsistencies; this docs-only repair requires fresh successor review before push
or S07.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: exact reviewed B02 reconciliation head
`609185098935feea82f4d5b6fb7a9d62aefce9c9`.

## Exact history-preserving merge

B03 first performed a normal no-ff merge of exact shared head
`fe469308b758ac381b770fb83cee4a7f792400cd`:

- merge commit `212486f77181c1ab3c681b89e1d2d75cc79b8473`;
- first parent `609185098935feea82f4d5b6fb7a9d62aefce9c9`;
- second parent `fe469308b758ac381b770fb83cee4a7f792400cd`; and
- merge tree `9c8c2fa84d6d4ad75f07ac15a5ae30b225d2778b`.

When the shared stack advanced, B03 preserved that merge and folded exact latest head
`2014783d7d461b64164e3ec2844ce7f1eeb4c846` through a second normal no-ff merge:

- merge commit `8917b7edb64614ab5417575a383abab15e396f2e`;
- first parent `212486f77181c1ab3c681b89e1d2d75cc79b8473`;
- second parent `2014783d7d461b64164e3ec2844ce7f1eeb4c846`; and
- merge tree `d85705964fe80bc5856015390df946a0df648b09`.

The merge was conflict-free. It preserves local corrected FIPS 205 §9 Algorithms 19–20 citation,
all accepted B02/S06 history and review artifacts, and every remote construction, query-bound, and
security hunk. No commit was cherry-picked, reordered, squashed, or dropped.

## Imported construction and query surface

The shared stack makes `XmssSig.auth` an intrinsic `Vector _ hp`, and makes each FORS opening expose
`.sk` plus intrinsic `.auth : Vector _ a` inside an intrinsic `k`-vector signature. Active tests use
`.wots`, `.auth.toList`, and FORS `.sk`/`.auth.toList`; the current S06 probe now pins
`xmssSignBounded_eq` and `xmssSign_eq_mk` rather than the removed erasure adapter.

`LayerPosition.atLayer`, `GeneralHypertree`, and `GeneralScheme` provide typed arbitrary-depth loops,
query-preserving naturality, and deterministic-handler interpretations. Their query-bound modules
prove finite structural upper bounds uniform in the message, not exact message-dependent counts.
`recoverFromPosition_signFromPosition`, `pkFromSig_sign`, and
`GeneralScheme.verifyInternal_signInternal` now close pure/fixed-answer arbitrary-depth correctness.

`DepthOneCompatibility` proves output compatibility with the legacy d=1 API. General d=1 signing
also executes Algorithm 12's discarded final recovery, so its free-oracle trace is strictly longer;
the equivalence theorems do not claim program equality. A Medium callback `*With` to
explicit-query/pure parity theorem remains open, as do S07 FORS conformance fixtures/address/runtime
and S09 codecs/external APIs/reject behavior.

## Security boundary and concurrent ownership

Security games now key tweaks by the primitive's encoded `AdrsKey`; compatibility equations prove
that structural `Adrs` adapters still evaluate through `F`, `H`, and `Tl` exactly. The provisional
`Security.GeneralScheme.securityInterface` delegates operation fields to the general construction,
but is conditional shape only: `ClassicalSecurityContext` assumes `ReductionSystem`, and
`Security.RepairedMasterStatement` remains an unproved `Prop`. No S02/S11 reduction, master theorem,
or security completion is claimed.

The exact `sufAdvantage = eufAdvantage + sameMessageAdvantage` identity is only a disjoint event
partition; the same-message residual has no bound and `RepairedMasterStatement` remains EUF-only.
`Security.ReachableTargets` supplies structural FORS/XMSS/WOTS addresses, cardinalities, and
`Nodup`. It does not establish concrete encoded injectivity, nonempty `DistinctTargetBatch`
packaging, actual-query coverage, target-input pairing, final-validity/disjointness, or canonical
PR #594/#596 game adapters.

PR #594/#596 remain authoritative generic-game work; later adapters/equivalence must relate or
replace bespoke games. PR #585 theorem content may be ported, never raw-merged. Cumulative PR #591
remains reserved for S15 extractor/transcript/shared-ROM integration.

## Assurance and reviewer handoff

The exact B03 probe covers 27 trajectory, construction/correctness/naturality, d=1 compatibility,
finite-query-bound, SUF partition, structural reachable-ledger, encoded-address compatibility,
conditional interface, and proposition-shape roots.
Every root uses only the recorded standard axiom subset; none uses `sorryAx`. The nested
`HashSig/SLHDSA/HypertreeGeneral/*.lean` source root is now included in the provenance composite.
PolicyAudit accepts the exact seventeen named Lean-generated recursion helpers only after checking their safe
parents, common HashSig ownership, partial-but-kernel-safe status, and absence of extern,
initializer, runtime override, axiom, and `sorryAx` surfaces; this is not a trust-policy weakening.
The final static audit observes 44 HashSig modules and 3,447 owned constants and retains the exact
transitive axiom union `{propext, Classical.choice, Quot.sound}`.

Focused builds cover Position, XMSS/conformance, FORS, GeneralHypertree/query/correctness,
GeneralScheme/query/correctness, DepthOneCompatibility, Security GeneralScheme/Architecture/SUF and
ReachableTargets, Concrete.Instance, and corresponding tests. Retained S05/S06 runtimes, aggregate builds, generated imports, isolation,
documentation/provenance, PolicyAudit, and the authoritative wrapper are final gates recorded in the
implementation handoff.

A fresh successor reviewer must inspect the exact two history-preserving merge commits, bounded
adaptation commit, and docs-only repair atop immutable r0 FAIL, confirm
historical S06/B02 session/review blobs are byte-identical, check that no missing correctness or
security theorem is claimed, and replay the focused/full evidence. The implementer does not create
the review artifact.
