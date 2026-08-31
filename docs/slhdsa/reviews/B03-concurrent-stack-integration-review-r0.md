# B03 concurrent-stack integration review r0

Verdict: **FAIL**

Finding count: **0 blocking; 3 nonblocking** (two Medium, one Low).

This is a fresh independent review of candidate
`157855d88b9bc550de5964bdd90d112ee16ae9dd`.  I did not implement B03.  I made no
implementation or active-document change; this review artifact is the only review-side change.

## Reviewed boundary

- candidate: `157855d88b9bc550de5964bdd90d112ee16ae9dd`
- candidate tree: `df94aad350ef46ddb5d581ea43b38e3627fcdcdc`
- candidate parent: `8917b7edb64614ab5417575a383abab15e396f2e`
- first merge: `212486f77181c1ab3c681b89e1d2d75cc79b8473`
  - parents: reviewed local `609185098935feea82f4d5b6fb7a9d62aefce9c9` and shared head
    `fe469308b758ac381b770fb83cee4a7f792400cd`
  - tree: `9c8c2fa84d6d4ad75f07ac15a5ae30b225d2778b`
- second merge: `8917b7edb64614ab5417575a383abab15e396f2e`
  - parents: `212486f77181c1ab3c681b89e1d2d75cc79b8473` and shared head
    `2014783d7d461b64164e3ec2844ce7f1eeb4c846`
  - tree: `d85705964fe80bc5856015390df946a0df648b09`

The worktree was clean at review start.  In a writable temporary shared clone,
`git merge-tree --write-tree` reproduced `9c8c2f...` for the first parent pair and `d85705...`
for the second.  Thus both merges are the exact conflict-free automatic merge results; the
candidate does not conceal a manual conflict resolution, drop, squash, or reorder.

The local FIPS 205 Section 9 Algorithms 19--20 citation remains in `Position.lean`.  The accepted
S06 session/review blobs remain exactly `96308d8b...`/`383072da...`; the accepted B02 session,
initial review, and reconciliation review remain exactly `fc335f0f...`, `f0807f75...`, and
`d3efae65...`.

## Technical review

### Positions and intrinsic component representations

`LayerPosition` uses the reachable tree exponent
`(d - (layer + 1)) * h'`.  `next` takes the low `h'` bits with remainder for the next leaf and
the remaining high bits with division for the next tree.  Its exponent proof is an exact
`pow_add` decomposition, and `atLayer` is obtained only by repeated `next`, rather than by a
second closed-form trajectory.  At the final layer the tree is intrinsically in `Fin 1`, so
`tree_eq_zero_of_isFinal` and the top address `(d - 1, 0)` are nonvacuous consequences of validated
`d > 0`.

The XMSS migration makes the WOTS signature and `Vector _ h'` authentication path intrinsic in
`XmssSig`.  The vector producer has the same bottom-up sibling-subtree schedule as the canonical
`PerfectMerkleTree.authPathM`; the erasure and deterministic interpretation theorems preserve that
schedule.  `XmssConformance` is consequently a thin typed-index wrapper over the canonical XMSS
type and algorithms, not a parallel signature semantics.  The migrated correctness and binding
proofs discharge path length through the type and retain the original leaf-index hypothesis.

FORS similarly represents exactly `k` openings, each with one secret value and `Vector _ a`.
The global index `i * 2^a + forsIdx` is retained for secret, leaf, path, and recovery addresses.
Its vector path erases to the canonical path and preserves monadic ordering.  This intrinsic
migration does not itself claim the S07 Appendix-A fixtures, concrete address acceptance, runtime
coverage, or KAT evidence.

### Arbitrary-depth programs and correctness

`signFromPositionM`/`signFromPosition` emit exactly the remaining number of intrinsic XMSS
signatures in increasing layer order.  For more than one layer, each signature is recovered and
its root becomes the next message; the final top signature is not needlessly recovered.  At the
entry call with `d = 1`, the `recoverFinal` branch performs Algorithm 12's mandatory recovery and
discards its value.  `recoverFromPositionM` consumes one component and advances by the same typed
position recurrence at every layer.

`recoverFromPosition_signFromPosition` is genuine arbitrary-`d` correctness.  The zero-layer
branch is impossible from `pos.layer < d` and `pos.layer + layers = d`; the singleton branch uses
the intrinsic leaf bound in `xmssPkFromSig_xmssSign` and identifies the final address exactly; the
recursive branch uses the inserted head/tail equations and recurses at `pos.next`.  It yields the
unique top XMSS root, and `pkFromSig_sign` plus `verify_sign` lift it to the deterministic API.
There is no vacuous extra hypothesis, restricted depth, or unchecked natural index.

`GeneralScheme` retains all three `H_msg` outputs, uses `parts.forsAdrs`, recovers the FORS public
key, and supplies the typed digest parts to the general hypertree.  Key generation computes the
top-layer root.  `verifyInternal_signInternal` shares one fixed total public-hash interpretation
across key generation, signing, and verification and correctly composes FORS and hypertree
completeness for every validated depth.  It does not claim an external FIPS API or randomized-ROM
security theorem.

The depth-one equivalences are correctly scoped by an explicit `d = 1` hypothesis.  Root,
recovery, verification, key generation, and verification programs agree with the legacy d=1 API.
Signing deliberately has a different free-oracle trace: `signM_toOneLayer_eq` and
`signInternalM_toOneLayer_eq` expose the additional discarded XMSS recovery, while the fixed-answer
theorems prove output equality only.  The candidate's private `Vector.get`/`getElem` rfl lemma and
simp-spelling changes are semantics-preserving Lean 4.33.1 compatibility changes.

The M-loop/pure-loop fixed-answer equations and query-preserving naturality theorems are present.
There is still no theorem relating callback-parametric `signFromPositionWith` and
`recoverFromPositionWith` to those proved representations.  The main B03 record, PO-024, and the
coverage notes explicitly retain this Medium future obligation; no correctness result reviewed
above depends on silently assuming it.

### Query bounds

The imported query theorems are structural upper bounds.  WOTS signing/recovery use coarse
`len * (w - 1)` bounds; their honest cycle uses the exact complementary-chain partition.  XMSS
adds the intrinsic path and compression costs.  Algorithm 12 charges `d - 1` sign/recovery cycles
plus the top signature for `d > 1`, and charges a full cycle for the required d=1 discarded
recovery.  Algorithm 13 charges one recovery per layer.  The GeneralScheme bounds add one `H_msg`,
the intrinsic FORS schedules, and the relevant general-hypertree bound.  Neither source nor active
B03 prose mislabels these as exact message-dependent counts.

### Security boundary and reachable ledgers

`StrongFresh` is exact request/signature-pair freshness.  The proved pointwise partition into a
fresh request and a same-request/new-signature case is disjoint, so the common transcript
distribution gives the exact
`sufAdvantage = eufAdvantage + sameMessageAdvantage` identity.  No bound is provided for the
same-message residual.  `RepairedMasterStatement` remains an EUF-only `Prop`, and
`ClassicalSecurityContext` contains an assumed `ReductionSystem`; the candidate therefore makes no
S02/S11 reduction or master-theorem claim.

The reachable-target module correctly enumerates:

- all layer/tree coordinates and all WOTS leaves, with the architecture's exact tree and instance
  counts;
- every possible bottom-layer FORS position, the global FORS leaf/internal-node indices, and one
  root-compression address per position;
- all internal XMSS nodes; and
- WOTS instances, chains, executed steps, selected steps, and public-key compressions.

The coordinate lists and structured-address images have the stated cardinality and `Nodup`
properties.  The executable WOTS step ledger has `w - 1` entries per chain; the architecture's
WOTS-TCR cap deliberately remains the looser source-proof `w` cap and is proved only as an upper
bound.  Conversion to the primitive's `AdrsKey` is duplicate-free only under injectivity restricted
to the chosen structural ledger.  No global SHA-2 compression injectivity, nonempty
`DistinctTargetBatch`, actual-query/input coverage, cross-role validity/disjointness, or game-ready
adapter is asserted.  PR #594/#596 remain the canonical generic-game owners, PR #585 is port-only,
and PR #591 remains later extractor work.

## Trust and evidence

The exact 43-file source-composite recipe, including the nested
`HashSig/SLHDSA/HypertreeGeneral/*.lean` root, reproduced
`a96482af2c7035f9cb7ef460f839fe6896707d4eb0fd68909e1c5cdad2f1e612`.
Source and candidate-diff inspection found no new `sorry`, axiom declaration, `native_decide`,
unsafe definition, extern, or runtime override.  `PolicyAudit.lean` still applies all prior
environment/module-extension checks and names exactly seventeen Lean-generated partial recursion
helpers.  Each new entry names its ordinary safe structural parent; the validation logic still
requires the exact observed set, `isUnsafeRecName?` parent identity, common HashSig ownership,
partial-but-kernel-safe helper status, safe parent status, absence of extern/init/runtime
overrides, and absence of `sorryAx`.  The checks were not weakened to a name-only allowlist.

Executed evidence:

```text
lake build HashSig.SLHDSA.Position HashSig.SLHDSA.Xmss \
  HashSig.SLHDSA.XmssConformance HashSig.SLHDSA.Fors \
  HashSig.SLHDSA.HypertreeGeneral HashSig.SLHDSA.HypertreeGeneral.QueryBound \
  HashSig.SLHDSA.GeneralScheme HashSig.SLHDSA.GeneralSchemeQueryBound \
  HashSig.SLHDSA.DepthOneCompatibility HashSig.SLHDSA.Security.Architecture \
  HashSig.SLHDSA.Security.GeneralScheme HashSig.SLHDSA.Security.ReachableTargets \
  HashSig.SLHDSA.Concrete.Instance HashSigTest.SLHDSA.Position \
  HashSigTest.SLHDSA.Xmss HashSigTest.SLHDSA.Fors \
  HashSigTest.SLHDSA.HypertreeGeneral HashSigTest.SLHDSA.GeneralScheme \
  HashSigTest.SLHDSA.ReachableTargets HashSigTest.SLHDSA.StrongUnforgeability
Build completed successfully (2732 jobs).

lake env lean scripts/slhdsa/S06InventoryProbe.lean
S06 declaration/axiom probe: PASS (22 exact load-bearing roots)
lake env lean scripts/slhdsa/B02InventoryProbe.lean
B02 declaration/axiom probe: PASS (15 exact load-bearing roots)
lake env lean scripts/slhdsa/B03InventoryProbe.lean
B03 declaration/axiom probe: PASS (27 exact load-bearing roots)

lake build HashSig HashSigTest
Build completed successfully (2768 jobs).

git diff --check 8917b7edb64614ab5417575a383abab15e396f2e..157855d88b9bc550de5964bdd90d112ee16ae9dd
# no output
```

The full `PolicyAudit.lean` environment scan was started after the three successful probes but was
terminated after approximately four minutes without output or failure once the independent verdict
was already necessarily FAIL.  A subsequent docs-only wrapper attempt was likewise terminated
after approximately one minute without output.  The authoritative full wrapper was not started:
the concrete active-record findings below already preclude acceptance, and repeating its broad
suite would not repair or adjudicate them.  These interrupted commands are not reported as PASS
evidence.

## Findings

### B03-001 — Medium — the active session index falsely leaves proved correctness open

`docs/slhdsa/sessions/README.md:44-45` says that general honest correctness/completeness remains
open.  This directly contradicts the reviewed theorems, the B03 session record, COV-019/COV-020,
and PO-021/PO-022.  It also conflates completed internal correctness with the genuinely open S07
conformance, callback parity, S09 external API, and security work.

Repair: change the B03 index entry to state that pure/fixed-answer general hypertree correctness
and internal GeneralScheme completeness are supplied by B03.  List only callback `*With` parity,
S07 conformance, S09 external/codecs/domain separation/rejection, and security reductions as open.

### B03-002 — Medium — active obligation, coverage, and successor plans retain the superseded d=1 story

The new PO-021 correctly discharges arbitrary-depth correctness, but
`docs/slhdsa/matrices/proof-obligations.csv:13` still leaves the same general-d correctness
obligation PO-012 open against legacy `htVerify_htSign`, with the pre-B03 assertion that only the
zero-tree d=1 Scheme path exists.  The same stale state remains in
`docs/slhdsa/proof-obligations.md:60-62` and COV-003/COV-004 at
`docs/slhdsa/matrices/coverage.csv:4-5`.  Meanwhile the successor plan still gives S07 the accepted
B02 boundary (`docs/slhdsa/plan.md:225`), asks S08 to implement the already imported general fold
and correctness (`:235-240`), and asks S09 to implement undifferentiated internal algorithms and
completeness (`:244-250`).

This does not make the Lean construction unsound, but it leaves two contradictory active owners
for one completed obligation and directs successors to duplicate imported work.

Repair: reconcile PO-012 with PO-021 by marking it superseded/discharged or redefining it narrowly
as the remaining all-profile conformance/runtime obligation with a new exact target.  Qualify the
old `Scheme`/coverage rows as legacy d=1 compatibility while pointing to `GeneralScheme` for the
general consumer.  Make accepted B03 the S07 input; restrict S08 to callback parity, concrete
all-depth/profile conformance, address traces, and trust review; restrict S09 to the missing
external/pure/pre-hash API, domain separation, context/OID, codecs, rejection, and mode behavior
while retaining B03 internal completeness.

### B03-003 — Low — the active checklist says accepted B02 is still awaiting review

`docs/slhdsa/proof-obligations.md:57-59` records B02's typed digest/position integration as pending
independent review.  B02 and its reconciliation are already independently accepted at exact head
`609185098935feea82f4d5b6fb7a9d62aefce9c9`, as correctly stated elsewhere in this candidate and
confirmed by the immutable review blobs.

Repair: replace the pending sentence with the exact accepted/reconciled boundary and preserve the
separate statement that B02 alone did not claim general-hypertree correctness.

## Final assessment

There is no blocking technical finding in the imported construction, query-bound, security-event,
or structural-ledger Lean work.  Nevertheless, the review contract permits PASS only with zero
blocking and zero nonblocking findings.  The three contradictory active records make this
candidate **FAIL**.  Repair the bounded documentation/status surfaces above, rerun the exact probes,
completed PolicyAudit/docs gates, and the authoritative wrapper, then submit a new immutable review
artifact.
