# S06 XMSS construction review r0

Verdict: **PASS**

Date: 2026-08-31
Reviewer: fresh independent technical reviewer (not the S06 implementer)
Reviewed candidate: `91845ddfa8a704400600fdbf1c64f82659c4ca52`
Candidate tree: `b8dc93911cb2a6b9c6f556cd3915c491f3b258f6`
Required accepted parent: `7e029e660b9353f70e9de03ab4e6cc71f54e27da`

## Repository state and scope

The review began with an empty `git status --short` at the exact candidate. Its sole parent and
tree match the required accepted S05 review boundary and expected tree. I read the current
`AGENTS.md`, S06 plan and complete session record, every one of the 21 changed files, the canonical
`PerfectMerkleTree` and `Xmss` implementations, and FIPS 205 Section 6 Algorithms 9--11 from the
pinned local standard. I made no implementation or candidate-document changes. This artifact is
the review's only repository change.

The Lean payload consists of the local bounded/conformance adapter, concrete XMSS address
corollaries, aggregate imports, and focused construction tests. Lake and validation changes add the
S06 executable and exact-root probe. The remaining files are inventories, matrices, provenance,
validation, plan, and session records. No generic `VCVio` Merkle, extractor, security, or existing
`HashSig/SLHDSA/Xmss.lean` implementation file changes in this candidate.

## Bounded positions, authentication paths, and FIPS climb

`TreePosition treeHeight` encodes exactly Algorithm 9's premises: `level <= treeHeight` and
`index < 2^(treeHeight-level)`. The subtraction is guarded intrinsically, the top-level index type
is the nonempty `Fin 1`, and `index_lt_leafCount` correctly weakens the level-relative bound to the
full leaf-count bound. `LeafIndex p = Fin (2^p.hp)` is likewise inhabited and supplies the exact
honest-correctness premise rather than replacing it with an unrelated parameter-validity
assumption.

`authPathVector` is a width-`z` view of the existing `PerfectMerkleTree.authPath`; its list-erasure
theorem proves equality to that canonical path. Induction through `authPath_succ` proves entry `j`
is the root of the height-`j` sibling subtree. The independent low-bit lemma correctly identifies
the existing even `i+1` / odd `i-1` sibling with `i xor 1`, yielding the exact Algorithm 10 index
`(idx / 2^j) xor 1`. The XMSS specialization then rewrites that subtree root to the existing
`xmssNode` without changing its semantics.

The explicit honest Algorithm 11 characterization uses `Nat.rec`, with no generated recursive
helper. After step `k`, the accumulated node is the height-`k` subtree at `idx/2^k`; the next hash
uses height `k+1`, horizontal index `idx/2^(k+1)`, and the height-`k` sibling. Even parity places the
accumulator on the left and odd parity places it on the right. This matches both the standard's
mutable tree-index division and the canonical perfect-tree recursion. The proof handles the even
identity `q=2*(q/2)` and odd identity `q=2*(q/2)+1` with the corresponding sibling, then proves the
result is exactly the perfect-subtree root. Its second theorem equates the characterization to
canonical `authPath`/`climb`; it is not used as a competing arbitrary-signature recovery engine.

The bounded Algorithm 9 wrapper calls `xmssNode` directly. Bounded signing constructs the existing
WOTS signature plus the typed view of the existing authentication path, and its erasure theorem is
exactly `xmssSign`. Bounded recovery calls `xmssPkFromSig` on that erasure. Honest correctness
therefore invokes the unchanged `xmssPkFromSig_xmssSign` with precisely `idx.isLt`. Bounded binding
only discharges `sig.erase.2.length = p.hp`; it preserves the original changed-leaf premise,
height range, honest child pair, `TREE` address, and collision conclusion for an arbitrary bounded
signature.

The mature callback/oracle-parametric WOTS and XMSS programs, public-hash naturality, deterministic
interpretations, query bounds, `chain_compose`, `wotsPkFromSig_wotsSign`, Merkle completeness, XMSS
correctness, and binding implementations are unchanged. The new adapter therefore neither weakens
nor reproves those results under artificial hypotheses.

## Address and concrete boundaries

The generic field equations follow the constructors actually used. `wotsLeafAdrs` preserves layer
and tree, changes the type to `WOTS_HASH`, sets the key-pair index, and clears words two and three.
`xmssNodeAdrs` preserves layer and tree, changes the type to `TREE`, clears word one, and stores the
exact height and horizontal index in words two and three. Canonicality follows from a canonical
base and four-byte fits; full 32-byte serialization round-trips both address forms.

Case analysis over all twelve approved profiles proves the exact local `hp <= 9` bound. It gives
every leaf index and every level-relative node coordinate ample four-byte capacity without adding a
SHA2 condition to generic `Params.Valid`. Starting from `Sha2Address`, the derived WOTS-leaf and
XMSS-node addresses retain the checked one-byte layer and eight-byte tree bounds, so
`Sha2Address.ofAdrs` succeeds. The S05 WOTS boundary is reused under the proof-carrying leaf address
for secret derivation, every chain/hash step, and WOTS public-key compression. SHAKE retains the
full `Adrs.toVector` key and obtains exact round trips for reachable leaf and node addresses.

These results cover every address family used by concrete XMSS evaluation. The runtime also
enumerates every reachable leaf and internal-node address for each approved height before the
selected concrete equalities. Thus the SHA2 implementation's fail-closed zero result cannot explain
the tested sign/recover/root equalities.

## Executable discrimination

The height-two toy primitive is genuinely address sensitive: its node type is an address trace,
PRF emits its address, and every variable-arity hash prepends its own address to its children. The
test checks the exact four `WOTS_PK` leaf addresses and three `TREE` internal addresses, totaling
all seven tree positions. It iterates all four leaf indices, checks both authentication entries
against explicit sibling indices, and recovers the same root at each index. Consequently both
parity orientations and every height-two authentication path are exercised.

`FipsParameterSet.all` is the explicit twelve-element enumeration. For every profile the runtime
iterates `2^hp` leaves and, for every level 1 through `hp`, all `2^(hp-level)` internal nodes. Each
entry must pass checked SHA2 acceptance and the full-address round trip, so the loops are nonempty
and complete. The selected operational cases use distinct deterministic seed/public-seed/message
vectors and run actual bounded signing, recovery, and canonical root generation at indices 0 and 7
for SHA2-128f and SHAKE-128f, plus SHA2-192f. The last profile selects the category-3 SHA2 bundle
and therefore exercises its SHA-512 `H`/`T_l` path. `yToBytes` is identity for these approved byte
bundles, so the comparison is equality of the actual fixed-width nodes. These are substantive
derived regressions, not mislabeled XMSS KATs or ACVP evidence.

## Trust, concurrency boundary, and records

The new source contains no `sorry`, axiom, `native_decide`, unsafe definition, external/native
implementation, or trust shortcut. The exact 21-root probe covers position bounds, authentication
erasure and indexing, both climb equalities, generic and concrete address facts, bounded erasure,
correctness and binding, plus retained canonical XMSS roots. Every expected individual footprint
matched. The union is only `propext`, `Classical.choice`, and `Quot.sound`.

The authoritative policy independently observed 36 HashSig modules and 2,748 owned constants with
the same exact axiom union. Its compiler-helper set remains exactly the five pre-existing helpers
for `base2bFill`, `base2bGo`, `digitsOfBaseW`, `chainWith`, and `C13.chain`; no
`honestClimbFips._unsafe_rec` remains. `PolicyAudit.lean` is byte-identical to the accepted parent
(SHA-256 `5ca328f6c8ae1b3be89ef52db35e9c45cbb2718ad00b8e2b2ebb668ed287d316`), so the
allowlist was not tuned for this candidate.

PR #591 head `eff02207a77464edb07d750b8dbb00a9667543db`, PR #594 head
`c0930e49f74580fc8c0c22fbbffd8496df38972a`, PR #595 head
`be823fbb6745e95412efe2bf49e0e46055953413`, and PR #596 head
`7068fd993e35748822d07bba922fe70fe2953cd9` are all non-ancestors of the candidate. The diff adds
no `NodeQuery`, transcript/extractor, generic-game, digest-position, or shared-ROM implementation.
The local `(height,index)` node-hash callback and explicit `Adrs` constructors retain a clean
address-key seam for later PR #575/#591 adaptation without duplicating their security machinery.
The records consistently reserve PR #591 for S15, #595 across S07--S09, and #594/#596 for later
security sessions. Their citations also preserve the correct FIPS division: XMSS in Section 6,
hypertree in Section 7, and FORS in Section 8.

Aggregate imports, Lake target, inventories, coverage and proof-obligation matrices, source
composite, reference manifest, validation text, and session/handoff records passed the documentation
and provenance gates. They claim bounded XMSS construction/refinement and derived runtime evidence,
not an XMSS KAT, ACVP certificate, concrete-hash refinement, or security reduction.

## Commands and independent evidence

All commands were run from `/home/alh/SPHINCS/VCV-io` at the exact candidate unless a command names
another revision.

```text
git status --short
  PASS: empty at review start
git rev-parse HEAD HEAD^ HEAD^{tree}
  91845ddfa8a704400600fdbf1c64f82659c4ca52
  7e029e660b9353f70e9de03ab4e6cc71f54e27da
  b8dc93911cb2a6b9c6f556cd3915c491f3b258f6
git diff --stat 7e029e66... 91845ddf...
  21 files changed, 949 insertions(+), 40 deletions(-)
git diff --name-status 7e029e66... 91845ddf...
  PASS: exact reviewed scope; no generic VCVio/Merkle/security file
git diff --check 7e029e66... 91845ddf...
  PASS

lake env lean HashSig/SLHDSA/XmssConformance.lean
lake env lean HashSig/SLHDSA/Concrete/Xmss.lean
  PASS
lake exe slhdsa_xmss_tests
  SLH-DSA S06 XMSS construction tests: PASS
  (height-2 exhaustive; 12-profile addresses; SHA2/SHAKE 128f and SHA2-192f indices 0/7)
lake env lean scripts/slhdsa/S06InventoryProbe.lean
  S06 declaration/axiom probe: PASS (21 exact load-bearing roots)
lake env lean scripts/slhdsa/PolicyAudit.lean
  static import: 36 HashSig modules
  compiler-helper allowlist: PASS (5 exact `_unsafe_rec` auxiliaries)
  inventory: 2748 owned constants; exact standard axiom union
  elaborated policy audit and fixtures: PASS

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
git merge-base --is-ancestor be823fbb6745e95412efe2bf49e0e46055953413 HEAD
git merge-base --is-ancestor 7068fd993e35748822d07bba922fe70fe2953cd9 HEAD
  PASS: all four exit 1 (non-ancestors)

./scripts/slhdsa/validate.sh
  harness/provenance and fresh parser mutation/runtime gates: PASS
  builds: PASS (3449, 2737, and 2754 jobs)
  S03/S04/S05/S06 exact declaration/axiom probes: PASS
  policy audit, generated aggregate, and isolation: PASS
  inherited KAT, C13, codec, primitive, WOTS, and XMSS executables: PASS
  SLH-DSA full baseline validation: PASS
```

The wrapper warnings are expected and outside the reviewed HashSig trust boundary: absent optional
native submodules produce unused empty stubs, upstream non-HashSig modules retain known admissions,
and deliberate policy fixtures elaborate declarations which the audit must reject. The exact
HashSig policy result and all reviewed executable outcomes passed.

## Findings and verdict

Blocking findings: **0**.

Nonblocking findings: **0**.

The exact S06 candidate passes. Its bounds match FIPS node and leaf domains; authentication entries
and every honest climb step have the correct indices and orientation; bounded APIs erase to the
canonical XMSS/Merkle semantics; address acceptance excludes masked SHA2 failure; runtime evidence
is discriminating; mature oracle/correctness/security seams remain unchanged; and trust,
concurrency, citation, provenance, and validation boundaries remain intact. This review accepts
only candidate `91845ddfa8a704400600fdbf1c64f82659c4ca52` and does not implement S07 or authorize an
unreviewed descendant.
