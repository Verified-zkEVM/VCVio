# S06 Merkle and XMSS construction candidate

Status: implementation complete; fresh independent S06 review required before push.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: exact pushed S05 review head
`7e029e660b9353f70e9de03ab4e6cc71f54e27da`. Its sole added artifact,
`docs/slhdsa/reviews/S05-wots-review-r0.md`, independently accepted exact S05 candidate
`33770467d9209d0e270db5edd7a88958641db2b2` with zero findings.

## Scope and ownership

S06 supplies the missing thin bounded/conformance interface for FIPS 205 §6 Algorithms 9–11. It
preserves the existing oracle/callback-parametric `xmssNode`, `xmssSign`, and `xmssPkFromSig` and
the generic `PerfectMerkleTree` engine as the only construction semantics. Existing naturality,
query bounds, deterministic-handler parity, Merkle-root equality, honest recovery, and binding
remain unchanged; S06 adds typed adapters and refinement equations around them.

Cumulative PR #591 exact inspected head
`eff02207a77464edb07d750b8dbb00a9667543db` owns the later addressed
transcript/extractor/batch/stateful/shared-ROM security stack. It is not merged or cherry-picked,
and S06 does not edit generic addressed-Merkle or extractor modules; integration is reserved for
S15. PR #595 exact inspected head `be823fbb6745e95412efe2bf49e0e46055953413` remains reserved
across S07–S09 (S07 digest splitting/FORS addressing; S08/S09 typed hypertree positions). PR #594
`c0930e49f74580fc8c0c22fbbffd8496df38972a` and PR #596
`7068fd993e35748822d07bba922fe70fe2953cd9` retain their later security ownership. None is
imported or duplicated here.

## Bounded XMSS and Merkle refinement

`HashSig/SLHDSA/XmssConformance.lean` adds:

- `TreePosition treeHeight`, carrying `level ≤ treeHeight` and
  `index < 2^(treeHeight-level)`, plus `LeafIndex p := Fin (2^p.hp)`;
- a `Vector` authentication path whose erasure is definitionally tied by theorem to the existing
  list path and whose entry `j` is exactly the height-`j` sibling subtree at
  `(idx / 2^j) xor 1`;
- an explicit honest FIPS Algorithm 11 loop: step `k` hashes at height `k+1` and index
  `idx/2^(k+1)`, with parity of `idx/2^k` selecting left/right. Induction proves both its canonical
  perfect-subtree root and exact equality to the existing `authPath`/`climb` semantics; and
- thin typed node, signing, and recovery wrappers. `BoundedSig` internalizes authentication width
  `p.hp`; erasure recovers the existing `XmssSig`, honest correctness reuses
  `xmssPkFromSig_xmssSign`, and arbitrary bounded signatures reuse `xmssPkFromSig_binding` with the
  exact path-length premise discharged by the type.

No second recovery or node algorithm is exported. The explicit FIPS loop is an equation for honest
paths; arbitrary signature recovery still calls the canonical `xmssPkFromSig`/`climb` engine.

## Address boundary

The conformance module proves exact field preservation, type changes, clearing, four-byte
canonicality, and full 32-byte serialization round trips for `wotsLeafAdrs` and `xmssNodeAdrs`.
`HashSig/SLHDSA/Concrete/Xmss.lean` derives the approved-profile local height bound `hp ≤ 9`, proves
every typed leaf/node coordinate fits, and sends every reachable leaf and node through the checked
`Sha2Address.ofAdrs` boundary. It reuses S05 WOTS theorems for secret derivation, every chain/hash
step, and WOTS public-key compression under the typed leaf address. SHAKE/full-address corollaries
prove exact serialization round trips. These facts prevent the total concrete adapter's zero
fallback from masking the tested SHA2 paths without burdening generic `Params.Valid` with
SHA2-specific restrictions.

## Discriminating and executable evidence

`HashSigTest/SLHDSA/XmssConstructionTests.lean` exhausts an address-sensitive deterministic
height-two tree: all four leaves, seven node positions, both parities, exact authentication entries,
complete WOTS-leaf and TREE-address traces, and bounded sign/recover/root equality at every leaf.
It then cheaply enumerates every reachable leaf and internal-node position for all twelve approved
profiles and rejects any checked-SHA2 failure (or failed full-address round trip).

Concrete construction cases use deterministic fixed-width seeds/messages and a canonical narrow
address at indices 0 and 7 for SHA2-128f and SHAKE-128f, plus SHA2-192f to exercise SHA-512. Each
compares bounded sign/recovery with the canonical XMSS root. The all-profile enumeration and the
generic/concrete address proofs ensure the selected SHA2 cases cannot succeed through fail-closed
zero fallback. These are derived construction regressions, not authoritative XMSS KATs, ACVP
evidence, concrete-hash refinement, or a security reduction.

## Validation evidence

Focused checks passed warning-free apart from documented optional-native-submodule stubs:

```text
lake env lean HashSig/SLHDSA/XmssConformance.lean
PASS

lake build HashSig.SLHDSA.XmssConformance HashSig.SLHDSA.Concrete.Xmss
Build completed successfully

lake build slhdsa_xmss_tests
Build completed successfully

.lake/build/bin/slhdsa_xmss_tests
SLH-DSA S06 XMSS construction tests: PASS
(height-2 exhaustive; 12-profile addresses; SHA2/SHAKE 128f and SHA2-192f indices 0/7)
elapsed 6.50 seconds; maximum RSS 70,680 KiB

lake env lean scripts/slhdsa/S06InventoryProbe.lean
S06 declaration/axiom probe: PASS (21 exact load-bearing roots)
```

The probe resolves typed position/path roots, the exact authentication entry and FIPS climb
equations, generic and concrete address roots, bounded honest correctness and binding, and retained
canonical XMSS theorems. Its observed footprints use only the existing standard `propext`,
`Classical.choice`, and `Quot.sound` subsets; no root depends on `sorryAx`.

The remaining focused gates also passed:

```text
lake build HashSig HashSigTest
Build completed successfully (2755 jobs)

lake exe mk_all --lib HashSig --module --check
No update necessary

bash scripts/check-extern-isolation.sh
Extern isolation check: OK.

bash scripts/check-interop-isolation.sh
Interop TCB isolation check: OK.

./scripts/slhdsa/validate.sh --docs-only
SLH-DSA docs-only validation: PASS
```

The first authoritative wrapper attempt reached the compiled policy after every preceding gate had
passed and correctly rejected one new compiler-generated
`SLHDSA.XmssConformance.honestClimbFips._unsafe_rec` helper. The implementation was narrowly
rewritten through `Nat.rec`; its step equations and all refinement proofs remained unchanged in
meaning. The focused module, 21-root probe, and `PolicyAudit.lean` then passed with the original
exact five-helper allowlist. No trust boundary was widened.

After the repair and metadata synchronization, the necessary final
`./scripts/slhdsa/validate.sh` replay completed with `SLH-DSA full baseline validation: PASS`. It
observed 36 HashSig modules, 2,748 owned constants, exactly five compiler helpers, and exact axiom
union `[propext, Classical.choice, Quot.sound]`; replayed the fresh parser/provenance/mutation
gates, imports/isolation, inherited KAT and component suites, all S03–S06 probes, and the new S06
runtime. Expected warnings were confined to absent optional native submodules, upstream non-HashSig
admissions, and deliberate policy rejection fixtures.

## Reviewer handoff

Review the exact unpushed candidate commit containing this record. Check that typed wrappers erase
exactly to the canonical algorithms; replay the xor-sibling and FIPS climb induction; inspect both
generic and concrete address proofs; confirm binding retains intrinsic path width; run the toy,
all-profile address, and selected concrete cases; verify the exact axiom probe and ownership absence
for PRs #591 and #594–#596. The implementer does not author or pre-fill an independent review
artifact. Any finding reopens S06; only a fresh zero-finding review may authorize push and S07.
