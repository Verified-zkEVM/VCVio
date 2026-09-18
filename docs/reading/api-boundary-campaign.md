# API boundaries and definitional equality

## Contract and evidence

The campaign starts at VCVio `c2085a1a3a367c0b1ff33f5cb32d2673d5dbbeae`,
Lean/Mathlib v4.34.0, and PolyFun `3710d71b28404a151b8d1f0ce080ea448778dec0`.
It covers the eight active production libraries and the isolated complexity adapter.
Dormant Interop remains outside the migration. Tests and examples provide consumer evidence;
a source census is not a line-by-line semantic review.

`python3 scripts/api-boundary-census.py` reports source signals by module. It reuses the
comment/literal-aware scanner from the existing exposure check. Counts identify places to
inspect; they are not defect counts or a ban on `rfl`, `change`, or `dsimp`.

Each reviewed boundary records its intended use, concrete consumer evidence, disposition,
and validation below. The dispositions are **intentional**, **repaired**, **pending**, and
**upstream-blocked**. A repaired row requires consumer validation, not merely a new lemma.

The API policy is:

- Keep intentional type-level interoperability and constructor computation. Publish the
  smallest reducer needed by dependent elaboration, with a consumer showing why it is needed.
- Use public constructor, application, observation, extensionality and characterization
  theorems for implementation-independent reasoning. Prove those theorems at the owning boundary.
- Distinguish module visibility, availability of bodies, transparency modes, and `@[defeq]`
  theorem registration. In Lean 4.34, syntactic `:= rfl` requests exported definitional equality;
  an ordinary `by` proof can establish a propositional equation about an opaque public definition.
- Use the owning carrier API and its normal forms. Actual dependent Sigma positions remain
  Sigma types. Do not install reverse-normalization simp rules or change imported reducibility
  attributes to compensate for an avoidable consumer mismatch.
- Custom algebra or order on a reducible alias must not change instance selection for the
  underlying unrelated type. Use standard tags, explicit interpretations, or a distinct carrier.
- Add interfaces, migrate consumers, then narrow exposure. Retain sound compatibility names;
  compatibility must not restore leaking instances or silently change an existing operation.
- Generic structural laws belong upstream; measure semantics and cryptographic policy stay in
  VCVio. Upstream candidates require an exact reproducer and an explicit removal condition.

## Review ledger

| Boundary | Evidence and intended interface | Disposition |
| --- | --- | --- |
| SLH-DSA `Security.generalAlg` | Three public projection equations now have ordinary proofs with the bundle opaque. `HashSigTest/ModuleAPI/SchemeGames.lean` verifies that reduction alone fails, uses the verification equation in direct and composed consumers, and retains perfect completeness. | repaired |
| `QueryCount` and counting writers | Removed the custom function monoid. `withCounting` uses `AddWriterT`, and `runAdd` publishes ordinary counts. `VCVioTest/ModuleAPI/Counting.lean` tests ordinary function multiplication, repeated labels, output preservation, and both failure transformer orders. Unary and relational handler clients use the tagged writer state explicitly. | repaired |
| `QueryCache` | A distinct carrier confines extension order to caches. Lookup syntax, explicit function equivalence, updates, sum projections, and finite/countable transports remain available. `VCVioTest/ModuleAPI/Cache.lean` tests unrelated function order, dependent fibers, overwrites, repeated cache hits, and round trips. Existing PRF network measure tests exercise countability. | repaired |
| `QueryLog`, traversal and replay | Trace observations should use public occurrence, lookup, filtering and path laws, retaining ordered dependent answers. PolyFun #239 is open at the initial snapshot. | upstream-blocked |
| Oracle specifications, coercions and handlers | The transparent `OracleComp`/`FreeM` and dependent signature façades are intentional. Audit compound signatures, handler application, transport and recursive wiring through ordinary imports. | pending |
| Probability and transformers | Native Measure/Kernel equations, successful-output mass and structural support are distinct contracts. Retain measurability and probability assumptions explicitly. | pending |
| Program logic and complexity | Predicate elimination, WP coherence, tactic computation forms and data-indexed certificate instances require consumer checks. Preserve named reductions and resource certificates. | pending |
| Interaction and runtime | Test shared state, scheduler/handler data, trace observations, fuel and failure through execution equations. | pending |
| Cryptographic games and conversions | Published constructor/projection equations for TCR, PRE, UD, and DSPR final-validity conversions. Removed unneeded global reducibility so downstream simp indexing agrees with the opaque API. HashSig proves both compression-game identifications through public laws; ordinary-import fixtures retain the named whole-experiment equality. | repaired |
| Lattice and executable interfaces | Audit coefficient/conversion/transform laws and the instance paths of vector-backed polynomials. Executable changes require differential tests. | pending |
| HashSig primitive and game packaging | Separate carrier projections required by dependent queries from value-level operations and proof-only exposure. | pending |

## Validation and rollout

The SLH-DSA pilot at `b148e9ff` passes `./scripts/validate.sh --lint --test --axioms`:
21,476 declarations in 720 modules, the existing 33 sorry-tainted declarations, and no
nonstandard axioms. A separate Lake package builds and runs with an ordinary import of
the same consumer fixture. The workflow registers that fixture as its own consumer library.

Every repair includes ordinary-import consumers, including an external Lake package when a
package boundary is involved. Cases include independent universes, genuinely different answer
fibers, empty/infinite fibers where supported, instance coherence, and the behavior that motivated
the interface. Use focused `linter.tacticCheckInstances` probes for dependent elaboration.

Semantic checks distinguish support from positive mass, preserve subprobability/failure behavior,
and exercise nonvacuous models. Counting and logging checks include failed handlers and transformer
order. The full per-PR gate is `./scripts/validate.sh --lint --test --axioms`; affected native
interfaces additionally run the FFI/vector checks, and affected optional adapters build separately.
Exposure and PMF baselines only decrease. No new sorry or nonstandard axiom debt is admitted.

Migrate one API family per reviewable change. Preserve source attribution and existing contributor
PRs. Adopt upstream API only at a merged, validated dependency revision; independent repairs can
proceed while an upstream change is pending. Record the precise validated revision with each PR.

## Context

- [PolyFun #216: free constructor normal forms](https://github.com/Verified-zkEVM/PolyFun/pull/216)
- [PolyFun #227](https://github.com/Verified-zkEVM/PolyFun/pull/227) and
  [#228: native object interfaces](https://github.com/Verified-zkEVM/PolyFun/pull/228)
- [PolyFun #229: independent class policies](https://github.com/Verified-zkEVM/PolyFun/pull/229)
- [PolyFun #230: support and continuation interfaces](https://github.com/Verified-zkEVM/PolyFun/pull/230)
- [PolyFun #231](https://github.com/Verified-zkEVM/PolyFun/pull/231) and
  [#232: upstream reuse and semantic audit](https://github.com/Verified-zkEVM/PolyFun/pull/232)
- [PolyFun #239: dependent paths and trace observations](https://github.com/Verified-zkEVM/PolyFun/pull/239)

### Counting validation

The counting repair at `e26cbd04` passes `./scripts/validate.sh --lint --test --axioms`.
The separate ordinary-import consumer also builds and runs. All existing structural bound
proofs and handler specifications compile. The old additive `Monoid (QueryCount ι)` cannot be
retained as compatibility: its instance also changed unrelated function multiplication.
Clients of raw writer state use `Multiplicative.toAdd`; clients of results use `runAdd`.
The deprecated probability bridges remain; their shared compatibility constraints reduce the
syntactic source count without claiming removal of the discrete semantic dependency.

### Final-validity conversion validation

The conversion repair at `cea45480` passes `./scripts/validate.sh --lint --test --axioms`:
21,500 declarations, 720 modules, 33 existing sorry-tainted declarations, zero nonstandard axioms.
The separate package consumer builds and runs. The definitions, adversary conversions, samplers,
experiments, and bounds are unchanged. Global `@[reducible]` was unnecessary for the existing
proofs and caused the new simp projection laws to be indexed under unfolded implementations;
ordinary-import simplification works after removing it. No unsafe reducibility override is used.

### Cache validation

The cache repair at `02de09d9` passes `./scripts/validate.sh --lint --test --axioms`:
21,507 declarations, 720 modules, 33 existing sorry-tainted declarations, zero nonstandard axioms.
The external cache consumer builds and runs. Two downstream proofs now identify cache updates
and product projections explicitly. Construct caches with `QueryCache.ofFn`; use `.toFn` when a
plain function is required. The cache order still requires identical stored values and does not
inherit the value order of response types.
