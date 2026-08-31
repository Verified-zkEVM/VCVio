# B02 PR #595 digest and position boundary integration

Status: integration implementation complete; fresh independent B02 review required before push or
S07.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: exact pushed S06 review head
`91e97865f4d1c91fac18172e41d91000142194de`. Its only added artifact,
`docs/slhdsa/reviews/S06-xmss-review-r0.md`, independently accepted exact S06 candidate
`91845ddfa8a704400600fdbf1c64f82659c4ca52` (tree
`b8dc93911cb2a6b9c6f556cd3915c491f3b258f6`) with zero findings.

## Exact history-preserving merge

PR #595 was inspected at exact remote-tracking head
`be823fbb6745e95412efe2bf49e0e46055953413`; its merge base is already-integrated PR #593 head
`0caf09ca831ba0686db549b596ddfeb121de69ac`. B02 performed a normal conflict-free no-ff merge:

- merge commit `ad7a21c01af50559f6e8a4eec7a193aa601c74ee`;
- first parent `91e97865f4d1c91fac18172e41d91000142194de`;
- second parent `be823fbb6745e95412efe2bf49e0e46055953413`; and
- merge tree `2927d55c07b23198e6a3dce0eccde5ed4905dfaf`.

No PR commit was cherry-picked or squashed, and no conflict resolution was required. The exact PR
history retains `9fef5fa9` (digest/layer positions) and `be823fbb` (named FIPS trajectories). Every
PR code, test, Scheme, aggregate-import, encoding-reference, and lint-workflow hunk is present. The
post-merge integration commit changes only the requested citation/boundary prose, assurance probe,
active records, matrices, and provenance pins.

## Authoritative ownership

`HashSig/SLHDSA/Position.lean` is authoritative across S07–S09 for:

- `digestMdBytes`, `digestTreeBytes`, and `digestLeafBytes` with their exact list extents;
- `DigestParts` and `splitDigest`, preserving typed `md`, `idxTree`, and `idxLeaf`;
- `DigestParts.forsAdrs`, carrying both digest-derived indices into the FORS address; and
- `LayerPosition`, `initial`, `next`, `toAdrs`, the final-tree-zero theorem, and field equations.

`HashSigTest/SLHDSA/Position.lean` remains the authoritative mutation-sensitive evidence for the
three-layer split/transition canary, all twelve digest summaries, all twelve initial/first-layer
position/address summaries, a complete seven-layer SHA2-128s trajectory, all-ones truncation
boundaries, and the limited d=1 zero-tree case. S07–S09 must consume these declarations and tests;
they must not duplicate or rename them.

The sole normative citation repair changes the Position digest-decomposition reference from FIPS
205 §4.1 to §9, Algorithms 19–20. No algorithm or proof was changed by that repair.

## Scheme boundary

The merged Scheme correctly uses `parts.md` and `parts.forsAdrs` for FORS signing and recovery.
Its hypertree signing and verification calls still pass `Adrs.zero`, tree index `0`, and
`parts.idxLeaf.val` to the existing one-layer interface. This is FIPS-correct only for valid
`d = 1`, where `DigestParts.idxTree_eq_zero_of_d_eq_one` proves that the parsed tree index is zero.
Functional signer/verifier agreement for the transitional implementation remains intact, but it is
not general FIPS construction coverage. S08/S09 must thread authoritative `LayerPosition` through a
general hypertree; B02 and S07 deliberately do not generalize Scheme.

## Concurrent boundaries

PR #594 exact head `c0930e49f74580fc8c0c22fbbffd8496df38972a` and PR #596 exact head
`7068fd993e35748822d07bba922fe70fe2953cd9` remain later security work. Cumulative PR #591 exact
head `eff02207a77464edb07d750b8dbb00a9667543db` remains reserved for S15 addressed
transcript/extractor/shared-ROM integration. None is merged, imported, or duplicated by B02. No
S07 FORS construction or security reduction begins here.

## Focused validation evidence

The merged Position/Scheme surface and the compatibility roots compiled together:

```text
lake build HashSig.SLHDSA.Position HashSig.SLHDSA.Scheme \
  HashSig.SLHDSA.WotsEncoding HashSig.SLHDSA.XmssConformance \
  HashSigTest.SLHDSA.Position HashSigTest.SLHDSA.Scheme
Build completed successfully (2702 jobs)

lake env lean scripts/slhdsa/B02InventoryProbe.lean
B02 declaration/axiom probe: PASS (15 exact load-bearing roots)
```

The B02 probe pins the three digest extents, both parsed-index equations, d=1 tree-zero fact,
`LayerPosition.initial`/`next`/final-tree/address roots, FORS tree/key-pair propagation, retained
Scheme query bounds, and retained deterministic correctness. Exact individual footprints use only
the existing standard `propext`, `Classical.choice`, and `Quot.sound` subsets; none depends on
`sorryAx`.

The aggregate `lake build HashSig HashSigTest` passes (2,757 jobs). Generated umbrella, extern and
interop isolation, deterministic documentation/harness, and ACVP provenance checks pass. The
compiled policy audit observes 37 HashSig modules and 2,852 owned constants, with the unchanged
exact five generated helpers and standard axiom union. The 36-file source-tree composite is
`1d5df27f6d9c48d9af24755727e3f9d007ee9ff7bf6522c21bd44247bb6aba67`. The authoritative full
wrapper ran once after this metadata synchronization and passed, including the fresh parser gate,
all six construction/runtime executables, exact probes, compiled policy fixtures, and aggregate,
generated-import, isolation, documentation, and provenance checks.

## Reviewer handoff

Review the exact two-commit B02 series: the no-ff merge and its bounded integration/docs child.
Verify both parent identities and that every PR #595 hunk/history survives; replay byte extents,
index masking, FORS address propagation, layer transition bounds, all twelve summaries, and the
complete trajectory; inspect the d=1 Scheme limitation and its zero-tree proof; confirm exact axiom
and trust footprints and the absence of S07/general-hypertree/security work. The implementer does
not author a review artifact. Any finding reopens B02; only a fresh zero-finding review may
authorize push and S07.
