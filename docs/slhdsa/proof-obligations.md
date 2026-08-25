# Checked proof-obligation checklist

Status is authoritative in `matrices/proof-obligations.csv`; this prose explains acceptance tests.
No checkbox is discharged by a build alone.

## Current Security.lean defects (all open)

- [ ] Target counts are strictly positive and tied to parameter/transcript formulas. Current natural
  arguments admit zero, making `Fin 0` target families and reductions potentially vacuous.
- [ ] Every RHS primitive uses the `PK.seed` generated with the attacked public key. Current theorem
  accepts a fixed free `pkSeed`, with no equality to `adv`'s EUF-CMA experiment key.
- [ ] Every additive loss is proved bounded/finite from a game hop. Current
  `slhdsaInterleavingLoss` accepts unbounded `qS/qH`; for large queries it can exceed one and make the
  inequality trivial. Its formula is an invented stand-in, not a proved ITSR loss.
- [ ] `qS` and `qH` are predicates on actual adversary/oracle executions. Current values occur only
  in the loss; no signing/hash oracle count is modeled.
- [ ] `Hmsg` has an actual ITSR game and `T_l` has the required security surface. Current theorem has
  neither an `Hmsg` adversary/advantage nor a `T_l` term.
- [ ] `yToBytes` is injective/coherent where abstract digit extraction is security-relevant. Current
  `Primitives` has a function but no law.
- [ ] Challenge samplers are honest-transcript-derived. Current FORS/WOTS input samplers are arbitrary
  caller-supplied `ProbComp`s and need not match scheme targets.
- [ ] A parameter-indexed asymptotic theorem exists. Current statement is one finite inequality with
  no security parameter, polynomial-time/query condition, or negligibility conclusion.
- [ ] The selected statement matches a pinned primary proof. Current decomposition does not match
  CCS 2019 Theorem 17 coefficients/notions and its only proof is the allowlisted `sorry`.

## Parameters, encodings, and ADRS

- [ ] Validity: positivity, `h=d*h'`, approved-set table, `w/len/m` formula and size theorems for all
  12 sets; legacy/C13 cannot satisfy normative approval by accident.
- [ ] Fixed widths and range safety for all arithmetic; no silent `Nat` underflow/division-by-zero.
- [ ] `toInt`/`toByte`, `base_2b`, checksum shift, digest split, bit order, truncation, and padding laws.
- [ ] ADRS field setters/getters, clearing, type separation, serialization and SHA2 compression laws;
  no address reuse across domains.
- [ ] Key/signature codecs round trip and reject every invalid length/format.

## Algorithms and API

- [ ] `F/H/T_l/PRF/PRF_msg/H_msg` types and concrete SHA2/SHAKE behavior match FIPS.
- [ ] WOTS+, XMSS, FORS, and general `d` hypertree exactness and deterministic correctness.
- [ ] Digest yields `(md,idx_tree,idx_leaf)` with bounds and correct per-layer evolution.
- [ ] Internal and external pure/pre-hash domain separation, context, OID, deterministic/hedged modes.
- [ ] Completeness and reject behavior load-bearing roots have zero `sorryAx`.
- [ ] ACVP evidence covers every claimed cell; positive pre-hash coverage is tracked separately due to
  issue #469. Existing two embedded KATs remain regression evidence only.

## Hash/refinement/security

- [ ] Concrete primitive/vector equivalence and abstract/concrete refinement; executable algorithms.
- [ ] Formal EUF-CMA, freshness, query bounds, transcript and oracle mapping.
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
