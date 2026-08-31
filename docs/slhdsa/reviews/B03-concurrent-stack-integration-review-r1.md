# B03 concurrent-stack integration review r1

Verdict: **FAIL**

Finding count: **0 blocking; 1 nonblocking** (Low).

This is a fresh successor review of the docs-only repair candidate
`83fe7849a1bc8dfc8f046034b067200ac36a494b`. I did not implement B03 or its repair. This review
artifact is my only repository change.

## Reviewed boundary

- candidate: `83fe7849a1bc8dfc8f046034b067200ac36a494b`
- candidate tree: `6e29535892e89ad2e5bc08931863c00c07151e7b`
- candidate parent / immutable r0 FAIL artifact commit:
  `17f1b060861a146b0bd2c4e67b0a7637b788feb4`
- implementation below r0: `157855d88b9bc550de5964bdd90d112ee16ae9dd`

The worktree was clean at review start. `git rev-parse HEAD HEAD^{tree} HEAD^ HEAD^^` reproduced the
four identities above. The candidate-versus-parent name-status delta contains only the eight
claimed active documentation/matrix files (including the B03 session record) and
`scripts/slhdsa/check-harness.py`. There is no `*.lean`, `HashSig`, or `HashSigTest` source delta.
The harness diff changes only the exact size/SHA-256 pins for the two intentionally edited CSVs.

The implementation and candidate `HashSig` trees are both
`c2ff05f401fd412ffdaf43b2e0e531efc9ca96e5`; their `HashSigTest` trees are both
`be6e935bb090ea72ecc89de091e3adf6cef092b1`. The r0 artifact blob remains exactly
`5b0e08c5fb9e96b8bfe06de43d4e0418d902313c`. The candidate delta does not touch the historical
S06 or B02 session/review artifacts; in particular the accepted S06 session/review blobs remain
`96308d8b...`/`383072da...`, and the accepted B02 session/initial-review/reconciliation-review blobs
remain `fc335f0f...`/`f0807f75...`/`d3efae65...` as pinned and checked in r0.

## Closure review

The exact locations reported by r0 are repaired correctly:

- B03-001 is closed. The session index now names
  `recoverFromPosition_signFromPosition`/`pkFromSig_sign` and
  `GeneralScheme.verifyInternal_signInternal` as discharging pure/fixed-answer arbitrary-depth
  correctness and internal completeness. It keeps callback `*With` parity, S07 conformance/runtime,
  S09 external APIs/codecs, and all reductions open.
- B03-002 is closed in the plan, prose, and matrices. PO-012 is now the discharged legacy `d = 1`
  compatibility obligation rather than a duplicate arbitrary-depth owner. PO-021 and PO-022 are
  discharged by B03 with review status pending; PO-024 retains callback parity for S08. S07 takes an
  accepted B03 boundary, S08 is restricted to callback parity/conformance, and S09 retains external
  pure/pre-hash APIs, codecs, modes, domain/context/OID handling, and rejection behavior.
- The exact B03-003 checklist text is closed: `proof-obligations.md` records B02 and its remote
  reconciliation as independently accepted at
  `609185098935feea82f4d5b6fb7a9d62aefce9c9`, while preserving that B02 alone made no general
  hypertree-correctness claim.

The security boundary remains conservatively open. PO-003 remains open for S11;
`ReductionSystem` is assumed and `RepairedMasterStatement` is still an unproved EUF-only `Prop`.
PO-025 retains the unbounded same-message SUF residual, and PO-026 retains encoded-injectivity,
batch/query-alignment, validity/disjointness, and canonical PR #594/#596 adapter work. No active
matrix row turns structural ledgers or the advantage identity into a completed reduction.

However, the required cross-README consistency is not achieved. The canonical reviews index still
contains the superseded pre-B02-review handoff described below.

## Validation evidence

```text
git diff --check 17f1b060861a146b0bd2c4e67b0a7637b788feb4..83fe7849a1bc8dfc8f046034b067200ac36a494b
# no output

git diff --check 157855d88b9bc550de5964bdd90d112ee16ae9dd..83fe7849a1bc8dfc8f046034b067200ac36a494b
# no output

wc -c docs/slhdsa/matrices/coverage.csv docs/slhdsa/matrices/proof-obligations.csv
8813 docs/slhdsa/matrices/coverage.csv
8992 docs/slhdsa/matrices/proof-obligations.csv

sha256sum docs/slhdsa/matrices/coverage.csv docs/slhdsa/matrices/proof-obligations.csv
7e986b8f14fc8b125327609a726e52d3387c5c6d5737327788388ec8636d3d1c  docs/slhdsa/matrices/coverage.csv
6830a95ba15b2584024113286bd536e8c47ffa5578760bc39186b04cecb67015  docs/slhdsa/matrices/proof-obligations.csv

./scripts/slhdsa/validate.sh --docs-only
SLH-DSA harness check: PASS
SLH-DSA ACVP provenance: PASS (9 committed artifacts; 15 server artifacts; 144 coverage cells/24 positive)
SLH-DSA docs-only validation: PASS
```

Focused positive searches found the corrected B03 theorem ownership, exact accepted B02 head, S07
accepted-B03 input, S08 callback owner, S09 external API remainder, and still-open SUF/reduction/
ledger language. The corresponding stale search found only
`docs/slhdsa/reviews/README.md:89-90`, quoted in the finding. The harness independently parsed the
CSV records, enforced unique IDs and exact whole-file pins, and ran its matrix-corruption negative
tests.

A second full Lean wrapper was intentionally not run: the candidate has no Lean source change, both
Lean source trees are byte-identical to the already technically reviewed B03 implementation, and
the requested focused docs/harness/provenance/matrix gates passed. A full rerun could not adjudicate
the remaining false active handoff statement.

## Finding

### B03-R1-001 — Low — the active reviews index still says accepted B02 is pending

`docs/slhdsa/reviews/README.md:89-90` says:

> B02 has no review artifact yet; its unpushed integration candidate requires a fresh independent
> review before S07.

This is false. B02 has both an initial integration review and a remote-reconciliation review, and
the resulting boundary is accepted at exact reviewed head
`609185098935feea82f4d5b6fb7a9d62aefce9c9`. The main README, session index, plan, checklist, and
matrices now say so, making the canonical reviews README the sole contradictory active successor
route. It violates the repair requirement that every active README record B02 as accepted rather
than pending.

Repair: update the reviews index to link the two B02 review artifacts and record exact accepted head
`609185098935feea82f4d5b6fb7a9d62aefce9c9`; remove the pending-review/S07-blocked sentence. Do not
alter the immutable historical review artifacts.

## Final assessment

The three r0 locations are substantively corrected, all focused gates pass, and the Lean source is
unchanged. Nevertheless, the review contract permits PASS only with zero blocking and zero
nonblocking findings. The remaining false canonical reviews-index handoff makes this repair
candidate **FAIL**.
