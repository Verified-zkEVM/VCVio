# Checked proof-obligation checklist

Status is authoritative in `matrices/proof-obligations.csv`; this prose explains acceptance tests.
No checkbox is discharged by a build alone.

## Rejected legacy `Security.lean` and replacement architecture

- [x] The S02 replacement has formula-derived positive caps for all eight source-game target roles.
  Actual traces may be shorter or empty; selecting a missing target makes the event false. The
  rejected legacy theorem still admits zero caller-supplied counts.
- [x] The S02 replacement fixes a coherent generated-key distribution inside an explicit attacked
  `SchemeInterface`; primitive queries use that key's seed/root. The rejected legacy theorem still
  accepts a disconnected free `pkSeed`.
- [ ] Every additive loss is proved bounded/finite from a game hop. Current
  `slhdsaInterleavingLoss` accepts unbounded `qS/qH`; for large queries it can exceed one and make the
  inequality trivial. Its formula is an invented stand-in, not a proved ITSR loss.
- [x] S02 defines `qS` and `qH` as pathwise predicates on the actual adversary program for every
  public key. Internal signer instrumentation and runtime accounting remain for S12.
- [x] S02 defines the post-hop `Hmsg` ITSR experiment and every required FORS/WOTS `T_l` role.
- [ ] `yToBytes` is injective/coherent where abstract digit extraction is security-relevant. Current
  `Primitives` has a function but no law.
- [x] S02 removes caller-supplied target samplers. Each quantitative component is a standalone
  source-shaped challenger with its own target oracle and same-execution collection log where
  required; D-009 records why these targets are not extracted from the outer EUF transcript.
- [ ] A parameter-indexed asymptotic theorem exists. Current statement is one finite inequality with
  no security parameter, polynomial-time/query condition, or negligibility conclusion.
- [x] The S02 proposition has the exact repaired EasyCrypt twelve-term order and coefficients in
  classical semantics. Constructing reductions and proving it remain open; the rejected legacy
  statement still has only the allowlisted `sorry`.

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
