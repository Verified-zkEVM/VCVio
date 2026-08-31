# Checked proof-obligation checklist

Status is authoritative in `matrices/proof-obligations.csv`; this prose explains acceptance tests.
No checkbox is discharged by a build alone.

## Rejected legacy `Security.lean` and replacement architecture

- [x] The S02 replacement has formula-derived positive caps for all eight source-game target roles.
  Actual traces may be shorter or empty; selecting a missing target makes the event false. The
  rejected legacy theorem still admits zero caller-supplied counts.
- [ ] S02 packages public/secret seed and root coherence for each generated key, and primitive
  queries use that public key. Its arbitrary `SchemeInterface` has no refinement law coupling
  keygen/sign/verify/randomizer to general SLH-DSA; F-079/PO-003 remain open for S08/S09.
- [ ] Every additive loss is proved bounded/finite from a game hop. Current
  `slhdsaInterleavingLoss` accepts unbounded `qS/qH`; for large queries it can exceed one and make the
  inequality trivial. Its formula is an invented stand-in, not a proved ITSR loss.
- [x] S02 defines `qS` and `qH` as pathwise predicates on the actual adversary program for every
  public key. Internal signer instrumentation and runtime accounting remain for S12.
- [ ] S02 implements the proposed post-hop `Hmsg` ITSR experiment and every required FORS/WOTS
  `T_l` role, but D-006 remains unapproved and PO-006 is provisional.
- [x] S04 provides a separate `Primitives.ByteLaws` injectivity bundle, its `yToBytes_eq_iff`
  theorem, and concrete witnesses for both approved families. This discharge remains pending S04
  review and does not add a cryptographic assumption to the structural primitive interface.
- [ ] S02's candidate removes caller-supplied target samplers. Under proposed D-009, each
  quantitative component is a standalone source-shaped challenger with its own target oracle and
  same-execution collection log where required. D-009 has no named approver, so PO-008 remains
  provisional and the proposal does not supersede the earlier contract.
- [ ] A parameter-indexed asymptotic theorem exists. Current statement is one finite inequality with
  no security parameter, polynomial-time/query condition, or negligibility conclusion.
- [ ] The S02 proposition has the exact repaired EasyCrypt twelve-term order and coefficients in
  classical semantics, but D-006 remains proposed. Constructing reductions and proving it remain
  open; the rejected legacy statement still has only the allowlisted `sorry`.

## Parameters, encodings, and ADRS

- [ ] Validity: positivity, `h=d*h'`, approved-set table, `w/len/m` formula and size theorems for all
  12 sets; legacy/C13 cannot satisfy normative approval by accident.
- [ ] Fixed widths and range safety for all arithmetic; no silent `Nat` underflow/division-by-zero.
- [ ] `toInt`/`toByte`, `base_2b`, checksum shift, digest split, bit order, truncation, and padding laws.
- [ ] ADRS field setters/getters, clearing, type separation, serialization and SHA2 compression laws;
  no address reuse across domains.
- [ ] Key/signature codecs round trip and reject every invalid length/format.

## Algorithms and API

- [ ] S04 implements the exact typed `F/H/T_l/PRF/PRF_msg/H_msg` grammars for all twelve sets,
  with checked SHA2 addresses and focused standard/boundary/profile tests. Independent review and
  a general mathematical refinement theorem remain, so executable evidence does not close PO-017.
- [x] S05 implements and kernel-connects the exact WOTS+ checksum byte pipeline, preserves the
  existing deterministic recovery theorem, and exercises all twelve concrete profiles; independent
  r0 accepted the exact candidate with zero findings.
- [x] S06 packages FIPS §6 leaf/node bounds and authentication width intrinsically, proves exact
  sibling entries and the honest FIPS climb equation to the canonical Merkle engine, retains honest
  recovery and arbitrary-signature binding, and closes approved reachable SHA2/SHAKE addresses.
  Independent S06 r0 accepted the exact candidate with zero findings. FORS and general `d`
  hypertree exactness remain successor work.
- [x] B02 consumes PR #595's typed `(md,idx_tree,idx_leaf)` decomposition, exact byte extents,
  intrinsic bounds, FORS address, and `LayerPosition` low-bit/high-bit trajectory for all approved
  profiles. The integration remains pending independent B02 review.
- [ ] Scheme consumes `LayerPosition` through a general `d`-layer hypertree. It currently uses the
  digest-derived FORS address but passes `Adrs.zero`, tree zero, and `idxLeaf` to the d=1 hypertree;
  this is FIPS-correct only when valid `d=1` makes `idxTree = 0`. General consumption is S08/S09.
- [x] B03 imports typed arbitrary-`d` hypertree and GeneralScheme programs, naturality,
  deterministic interpretations, finite structural query upper bounds, and kernel-checked honest
  GeneralHypertree recovery plus internal GeneralScheme completeness (PO-021/PO-022).
- [ ] Callback-parametric `signFromPositionWith`/`recoverFromPositionWith` still lack a named parity
  theorem to the explicit-query/pure construction (PO-024, Medium). Depth-one output compatibility
  is proved, but general signing intentionally performs one discarded final recovery.
- [ ] Intrinsic FORS `k`/`a` widths are imported, but S07 conformance fixtures, reachable-address
  checks, and approved-profile runtime remain PO-023.
- [ ] Internal and external pure/pre-hash domain separation, context, OID, deterministic/hedged modes.
- [ ] Completeness and reject behavior load-bearing roots have zero `sorryAx`.
- [ ] ACVP evidence covers every claimed cell; positive pre-hash coverage is tracked separately due to
  issue #469. Existing two embedded KATs remain regression evidence only.

## Hash/refinement/security

- [ ] Concrete primitive/vector equivalence and abstract/concrete refinement; executable algorithms.
- [ ] Formal EUF-CMA, freshness, query bounds, transcript and oracle mapping.
- [ ] B03's encoded `AdrsKey` compatibility equations and conditional GeneralScheme interface are
  infrastructure only. `ReductionSystem` remains assumed and `RepairedMasterStatement` remains an
  unproved `Prop`; neither discharges a security reduction.
- [ ] The exact SUF advantage partition leaves the same-message residual unbounded and the repaired
  master statement EUF-only (PO-025).
- [ ] Structural reachable-target ledgers still require concrete encoded injectivity, nonempty
  `DistinctTargetBatch` packaging, actual-query/input alignment, final-validity/disjointness, and
  canonical #594/#596 adapters (PO-026).
- [ ] Precise ITSR and selected tweakable-hash/PRF notions with positive target cardinalities.
- [ ] Separate WOTS, FORS, XMSS/HT reductions; exact target/query/time transformations.
- [ ] Sorry-free top composition with verified coefficients and quantitative computability.
- [ ] Classical versus QROM semantics and claims explicitly separated.
- [ ] Asymptotic polynomial-time/negligibility theorem and all-12 finite accounting.
- [ ] Deployment target, ABI and source revision pinned; executable Lean-to-deployment refinement.

## Operational boundaries

- [ ] Randomness/entropy, key lifecycle, usage caps, side channels, faults, DoS/gas, compiler/runtime,
  and external crypto libraries are either proven/modelled or explicitly excluded in the report.
- [ ] `unsafe`, `extern`, `noncomputable`, axioms, `sorryAx`, native code and test-vector trust are
  inventoried with reverse dependency and load-bearing rationale.
- [ ] Runtime behavior and elaborated proofs are both checked; neither substitutes for the other.
