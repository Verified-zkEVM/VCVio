# B02 PR #595 integration review r0

Verdict: **PASS**

Date: 2026-08-31
Reviewer: fresh independent technical reviewer (not the B02 implementer)
Reviewed candidate: `fc06e95c24abcf0cc85f57b1426cedf9698a632e`
Candidate tree: `92637adb99b9cd271fc1b95cfafcbe268b7d2ea6`
Required integration parent: `ad7a21c01af50559f6e8a4eec7a193aa601c74ee`
Merge first parent: `91e97865f4d1c91fac18172e41d91000142194de`
Merge second parent: `be823fbb6745e95412efe2bf49e0e46055953413`

## Repository state, history, and merge fidelity

The review began with an empty `git status --short` at the exact candidate. Its tree and sole
parent match the required values. The parent is a normal two-parent merge whose first parent is the
accepted and pushed S06 review head and whose second parent is the exact PR #595 head. Their merge
base is exact already-integrated PR #593 head `0caf09ca831ba0686db549b596ddfeb121de69ac`.
The merge tree is `2927d55c07b23198e6a3dce0eccde5ed4905dfaf`.

The PR history is preserved without squash or cherry-pick: commit
`9fef5fa9877cbf209bd728bd8f01926f97a938b8` adds the digest/position surface and commit
`be823fbb6745e95412efe2bf49e0e46055953413` adds the named trajectory tests. Reconstructing the
merge produced an empty remerge diff, confirming that it was conflict-free and contains no manual
resolution. The PR changed exactly seven files.

At the merge, the lint workflow, `Position.lean`, `Scheme.lean`, `Position` test, and `Scheme` test
blobs are byte-identical to the PR head. The aggregate `HashSig.lean` retains the PR's `Position`
import together with every S03--S06 import from the accepted first parent. The PR's Encoding
reference to `Position.splitDigest` is present in the current, substantially extended accepted
Encoding implementation. Thus no older PR blob displaced the accepted fixed-width encoding or
WOTS work. The candidate child changes Position only to repair its normative citation and Scheme
only to state the existing d=1 limitation; its other changes are the B02 assurance probe and active
records. All PR-owned definitions, proofs, tests, and lint coverage survive.

The cumulative candidate changes 23 files relative to S06: the seven PR files plus bounded B02
documentation, inventory, provenance, and validation integration. There is no generic Merkle,
extractor, security-game, FORS implementation, or general hypertree implementation change. I read
the current `AGENTS.md`, B02 plan/session, both PR commits and original blobs, the complete candidate
diff, Position and Scheme sources/tests, the relevant Params/Encoding/Hypertree definitions, and
FIPS 205 Algorithms 12--13 and 19--20. This review artifact is my only repository change.

## Digest extents and typed indices

The three slice functions partition a `Bytes p.m` value at the exact FIPS byte boundaries:

- `digestMdBytes` extracts `[0, digestBytes)` where `digestBytes = ceil(k*a/8)`;
- `digestTreeBytes` extracts the following `treeIdxBytes = ceil((h-hp)/8)` bytes; and
- `digestLeafBytes` extracts the final `leafIdxBytes = ceil(h/(8*d))` bytes.

Because `m` is defined as the sum of those three lengths, each cast preserves precisely the
claimed extent without padding or loss. Their list theorems expose the same take/drop boundaries.
`toInt` is the existing big-endian decoder. `splitDigest` reduces the middle slice modulo
`2^(h-hp)` and the final slice modulo `2^hp`, so byte-alignment high bits cannot escape into either
index. Both moduli are positive, making `idxTree : Fin (2^(h-hp))` and
`idxLeaf : Fin (2^hp)` non-vacuous for every raw parameter record. For valid parameters,
`h = d*hp`, so these are exactly the FIPS tree and per-XMSS-leaf widths.

The d=1 boundary theorem correctly combines validity's `h = d*hp` with `d = 1`, obtaining
`h-hp = 0`; `idxTree` is consequently an element of `Fin 1` and has value zero. This proof is a
real arithmetic consequence of `Params.Valid`, not a test-only fact or a hard-coded limited-profile
case.

The three-layer canary independently makes every slice and mask observable: `a5 || ab || fe`
becomes message `[a5]`, tree `0xab = 171`, and four-bit leaf `0xe = 14`. The twelve named summaries
exercise all six arithmetic shapes in both SHA2 and SHAKE families with increasing bytes, checking
the message extent, last message byte, tree value, and leaf value. The all-ones check reaches
exactly `2^(h-hp)-1` and `2^hp-1` for all twelve profiles, distinguishing correct high-bit masking.
The limited d=1 profile separately checks its empty tree-index slice and zero result.

## Layer trajectory and addresses

`layerTreeHeight p layer = (d-(layer+1))*hp` is the number of tree-index bits remaining after the
leaf at that layer has been chosen. A `LayerPosition` intrinsically carries a layer below `d`, a
tree below `2^layerTreeHeight`, and a leaf below `2^hp`. `initial` maps parsed tree and leaf fields
directly into layer zero; validity proves `h-hp = (d-1)*hp`, so its transport has the exact bound.

For a nonfinal position, `next` raises the layer by one, sends the low `hp` tree bits to the next
leaf with `% 2^hp`, and sends the remaining high bits to the next tree with `/ 2^hp`. The proof uses
the exact exponent decomposition
`layerTreeHeight l = hp + layerTreeHeight (l+1)`, so the new quotient bound decreases by precisely
one XMSS height. There is no reversed high/low convention or off-by-one layer. At a final layer the
remaining exponent is zero and the tree is the unique element below one.

The all-profile trajectory canary checks initial and first-transition layer/tree/leaf fields and
the projected address for all twelve parameter names. The complete SHA2-128s seven-layer path
checks every quotient/remainder step through final tree zero. Its distinct intermediate values make
layer order, bit direction, and field swaps observable.

`LayerPosition.toAdrs` starts from the zero address and sets exactly its typed layer and tree;
type-dependent fields remain clear for the consuming component. `DigestParts.forsAdrs` follows
Algorithm 19 exactly: zero layer, parsed tree, `FORS_TREE` type with cleared dependent fields, and
parsed leaf as the key-pair address. Field equations and the three-layer full-record canary pin all
of these values. The repaired Position reference correctly cites FIPS 205 Section 9 Algorithms
19--20 for digest decomposition and Algorithms 12--13 for the hypertree recurrence.

## Scheme compatibility boundary

Both signing and verification now consume one `parts := splitDigest p digest`. FORS signing and
recovery receive `parts.md.toList` and the authoritative `parts.forsAdrs`, so neither parsed index
is discarded at the FORS boundary. Their public-hash schedule and query-bound proofs remain the
same except for this address/data packaging.

The current hypertree is still intentionally the existing one-layer API. Key generation uses the
zero tree; signing and verification pass `Adrs.zero`, tree `0`, and `parts.idxLeaf.val`. This is
FIPS-correct precisely on valid d=1 parameters, where the theorem above proves parsed `idxTree = 0`.
The fixed-answer and pure deterministic correctness theorems remain true for the transitional
program, but neither those theorems nor the B02 records claim general approved-profile Scheme
correctness. The main Scheme/Hypertree module docs, specification, README, plan, obligations,
coverage, validation, and B02 session all identify general `LayerPosition` consumption as S08/S09
work. B02 and S07 do not prematurely generalize the hypertree or introduce a second position API.

## Trust, ownership, and records

The PR and integration source add no `sorry`, axiom, `native_decide`, unsafe/native implementation,
or trust shortcut. The B02 probe covers all three byte extents, both parsed-index equations, the
valid-d=1 zero theorem, initial/next/final/address position roots, FORS tree/key-pair propagation,
both Scheme query bounds, and retained deterministic correctness. All 15 individual axiom sets
match their exact expected subsets. Their union is only `propext`, `Classical.choice`, and
`Quot.sound`.

The policy audit independently observes 37 HashSig modules and 2,852 owned constants with that
same exact axiom union and the unchanged five justified compiler helpers. No Position or Scheme
helper widens the allowlist. Focused source/test elaboration and text lint pass. The generated
aggregate includes Position, and extern/interop isolation remains intact.

PR #591 head `eff02207a77464edb07d750b8dbb00a9667543db`, PR #594 head
`c0930e49f74580fc8c0c22fbbffd8496df38972a`, and PR #596 head
`7068fd993e35748822d07bba922fe70fe2953cd9` are non-ancestors of the candidate. No candidate import
or diff introduces their transcript/extractor/shared-ROM or generic-game content. There is one
authoritative `DigestParts`/`splitDigest`/`LayerPosition` surface, owned by merged PR #595 for
S07--S09, and no S07 FORS construction has begun.

The S05 and S06 implementation-session and review-artifact blobs are identical between the accepted
first parent and candidate. Active matrices add the exact B02 declaration rows and leave general
Scheme consumption pending. Documentation/provenance validation verifies the 36-file source
composite `1d5df27f6d9c48d9af24755727e3f9d007ee9ff7bf6522c21bd44247bb6aba67` and every local
reference pin.

## Commands and independent evidence

All commands were run from `/home/alh/SPHINCS/VCV-io` at the exact candidate unless a command names
another revision.

```text
git status --short
  PASS: empty at review start
git rev-parse HEAD HEAD^ HEAD^{tree} ad7a21c0^1 ad7a21c0^2
  fc06e95c24abcf0cc85f57b1426cedf9698a632e
  ad7a21c01af50559f6e8a4eec7a193aa601c74ee
  92637adb99b9cd271fc1b95cfafcbe268b7d2ea6
  91e97865f4d1c91fac18172e41d91000142194de
  be823fbb6745e95412efe2bf49e0e46055953413
git merge-base 91e97865... be823fbb...
  0caf09ca831ba0686db549b596ddfeb121de69ac
git show --remerge-diff ad7a21c0...
  PASS: empty remerge diff; conflict-free merge
git diff --check 91e97865... fc06e95c...
  PASS

git diff --name-status 0caf09ca... be823fbb...
  PASS: exact seven PR files
git rev-parse be823fbb:<path> ad7a21c0:<path>
  PASS: exact matching lint, Position, Scheme, Position-test, and Scheme-test blobs
git diff be823fbb... ad7a21c0... -- HashSig.lean HashSig/SLHDSA/Encoding.lean
  PASS: accepted S03--S06 imports/encoding retained with both PR-owned integration hunks

lake build HashSig.SLHDSA.Position HashSig.SLHDSA.Scheme \
  HashSig.SLHDSA.WotsEncoding HashSig.SLHDSA.XmssConformance \
  HashSigTest.SLHDSA.Position HashSigTest.SLHDSA.Scheme
  Build completed successfully (2702 jobs).
lake env lean HashSig/SLHDSA/Position.lean
lake env lean HashSigTest/SLHDSA/Position.lean
lake env lean HashSig/SLHDSA/Scheme.lean
lake env lean HashSigTest/SLHDSA/Scheme.lean
  PASS
lake env lean scripts/slhdsa/B02InventoryProbe.lean
  B02 declaration/axiom probe: PASS (15 exact load-bearing roots)
lake exe lint-style HashSig HashSigTest.SLHDSA.Position HashSigTest.SLHDSA.Scheme
  PASS

lake exe mk_all --lib HashSig --module --check
  No update necessary
bash scripts/check-extern-isolation.sh
  Extern isolation check: OK.
bash scripts/check-interop-isolation.sh
  Interop TCB isolation check: OK.
./scripts/slhdsa/validate.sh --docs-only
  harness, provenance, matrices, manifest, and mutation checks: PASS
  SLH-DSA docs-only validation: PASS

git merge-base --is-ancestor eff02207a77464edb07d750b8dbb00a9667543db HEAD
git merge-base --is-ancestor c0930e49f74580fc8c0c22fbbffd8496df38972a HEAD
git merge-base --is-ancestor 7068fd993e35748822d07bba922fe70fe2953cd9 HEAD
  PASS: all three exit 1 (non-ancestors)
git rev-parse <accepted>:<S05/S06-session-or-review> HEAD:<same-path>
  PASS: all four path pairs have identical blobs

lake env lean scripts/slhdsa/PolicyAudit.lean
  static import: 37 HashSig modules
  compiler-helper allowlist: PASS (5 exact `_unsafe_rec` auxiliaries)
  inventory: 2852 owned constants; exact standard axiom union
  elaborated policy audit and fixtures: PASS

./scripts/slhdsa/validate.sh
  harness/provenance and fresh parser mutation/runtime gates: PASS
  builds: PASS (3449, 2738, and 2756 jobs)
  S03/S04/S05/S06/B02 exact declaration/axiom probes: PASS
  policy audit, generated aggregate, compiled fixture, and isolation: PASS
  inherited KAT, C13, codec, primitive, WOTS, and XMSS executables: PASS
  SLH-DSA full baseline validation: PASS
```

The wrapper's warnings are expected and outside the reviewed HashSig trust boundary: absent
optional native submodules produce unused empty stubs, upstream non-HashSig modules retain known
admissions, and deliberate policy fixtures elaborate declarations which the audit must reject.
The exact HashSig policy result and every reviewed gate passed.

## Findings and verdict

Blocking findings: **0**.

Nonblocking findings: **0**.

The exact B02 candidate passes. The merge preserves PR #595 history and owned hunks while retaining
all accepted S05/S06 integration; digest parsing has exact big-endian slices, masks, and intrinsic
bounds; the layer recurrence and address projections match FIPS; tests cover all named shapes and
discriminating boundaries; the Scheme uses the new FORS address while honestly remaining d=1-only;
and trust, provenance, ownership, import, and validation boundaries are intact. This review accepts
only candidate `fc06e95c24abcf0cc85f57b1426cedf9698a632e` and does not implement S07 or authorize an
unreviewed descendant.
