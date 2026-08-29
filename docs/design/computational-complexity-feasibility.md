# Computational-complexity feasibility record

Status: reviewer checkpoint, updated 2026-08-28. This record evaluates whether the current
interaction-first design is mathematically sound and whether it is ready for ordinary
cryptographic use. The answer is deliberately split:

- the committed foundation is an honest backend-relative definition of strict oracle PPT;
- the current candidate source interprets syntactic paths directly as Mathlib measures, adds
  full-measure finite-uniform laws, and exposes measure-kernel statements for symmetric
  encryption together with a measure-native OTP instantiation; and
- broad compositional use is still deferred until bounded iteration, quantitative handler
  substitution, an actual variable-width OTP witness, and concrete-backend adequacy are proved.

No declaration is counted as machine-checked merely because it is present in an uncommitted
working tree. Output recovery and bounded `seqComp` now live in PolyFun's generic resource layer;
the VCVio integration passes the root library, examples, and retained test build. This record does
not claim a concrete variable-width OTP PPT witness.

## Evidence classes

The assessment uses four evidence classes.

| Class | Meaning |
| --- | --- |
| Validated baseline | Committed source covered by the validation recorded in the usability spike. |
| Candidate | Source exists in the integration worktree but must pass the gates below before promotion. |
| Optional backend evidence | A concrete result in `VCVioComplexity`; it does not strengthen the generic definition by fiat. |
| Open obligation | A theorem, executable construction, or adequacy result that is not currently available. |

The historical validated comparison points are VCVio
`f64bca16c1efe6e558f07683eecae0baa5b18b99`, PolyFun
`73a924e3160c3930da96f8fa8f3c7298c1b06520`, and complexitylib
`b6738219a3a3c50967d6bd16cba9487887ca6b66`. The former
`dtumad/complexity-composition` and `dtumad/quantitative-bounded-composition` integration branches
are historical provenance for this design; the reviewed implementation now uses the pinned
PolyFun resource and finite-`FreeM` contract layers recorded by the repository manifests.

## Why the foundation is non-cheating

The complexity predicate does not classify an arbitrary Lean function as efficient. It starts
from a `FreeM` interaction program and requires a `QuantitativeRealization` with executable
backend code for initialization, observation, and every enabled update. An `Implements` proof
connects that machine to the original interaction tree. Exact `ExecutionTrace` folds charge local
work, queries, encoded traffic, peak state size, and peak readout size.

`RunsWithinUnder` then quantifies over every finite, well-typed trace admitted by one explicit
answer relation. It includes both branchwise resolution and progress, so an empty answer relation
at a reachable query cannot make the bound vacuous. `StrictPPTWitness` requires one realization,
one polynomial returned-payload recovery law, and one second-order resource polynomial for every
model admitted by a pinned `OracleContract`.
The modulus exposes oracle-answer growth instead of treating an arbitrarily long answer as a
unit-cost reply.

Security families are packed into one sigma-typed program. A family is uniform only when one
realizer and one polynomial implement that packed program; pointwise machines for each security
parameter do not suffice. Representations are pinned in the boundary, and executable
`PolyRealizer` witnesses include both work and encoded-output-growth bounds.
`QuantitativeRealization.OutputSizeRecovery` and `returnedSize_le_peakHeadSize` connect a returned
payload to the already charged tagged readout. `PolyOutputSizeRecovery` supplies the first-order
polynomial form; every candidate strict witness stores this law explicitly. It does not add a
freely asserted output meter.

This arrangement blocks the principal escape hatches:

- expensive or noncomputable work hidden in `pure` or a continuation has no executable realizer;
- a convenient encoding cannot be selected existentially after seeing the theorem;
- a per-parameter lookup-table machine does not establish uniform PPT;
- polynomial query count alone says nothing about local work or state growth; and
- probability-zero branches remain charged whenever the syntactic contract admits them.

The definition remains backend-relative. It becomes conventional machine-model PPT only after a
compiler or simulation theorem proves that the selected backend faithfully implements these
realizers with polynomial overhead.

The probability interpretation and the executable backend are separate choices. Mathlib
`Measure` supplies semantics; it is not a runtime model. Conversely, complexitylib remains an
optional adapter package and is not imported by the generic VCVio or PolyFun definitions. It can
be replaced by another backend that discharges the same realization, cost, and adequacy
obligations. Existing complexitylib canaries are evidence for that adapter only, not a reason to
adopt its definitions as the foundation.

## Typed syntax before probability

Probability is an interpretation of the same typed interaction syntax, not the source of its
resource bound. For a probabilistic polynomial functor `P`, `FreeM.withPath program` returns the
selected leaf together with a dependent `Path program`. Every response in that path has exactly
the type determined by its preceding query. `withPathLength` projects that dependent syntax to a
plain natural number before any probability semantics is chosen.

The candidate measure-native bridge denotes these two syntactic observers directly:

- `pathMeasure program` is `denote (withPath program)` when the caller explicitly supplies a
  measurable space on the dependent path type;
- `queryCountMeasure program` is `denote (withPathLength program)` and therefore needs no global
  measurable-space choice for paths;
- `map_length_pathMeasure` states that mapping the full path measure through `Path.length` gives
  `queryCountMeasure`; and
- `map_output_pathMeasure` states that forgetting a sampled path gives the original
  measure-valued denotation `denote program`.

The last two results are equalities of Mathlib measures, not equality of selected point
probabilities. The design deliberately installs no global measurable-space instance for the
dependent path type. Most complexity clients can use the canonical measure on natural-number
query counts and introduce a full path measure only when they need one.

The strict complexity statement remains pathwise and precedes that interpretation. A total
syntactic roll bound bounds the length of every complete typed path. The candidate
`expectedQueryCount` is the `lintegral` of the natural-number observation against
`queryCountMeasure`. `expectedQueryCount_le_of_isTotalRollBound` integrates the pointwise theorem
and derives an expected query bound. `StrictPPTWitness.expectedQueryCount_le` obtains the
corollary when the chosen resource model admits every typed answer.

Two trace types must not be conflated:

- `FreeM.Path` is indexed by a source program and is what the probability semantics samples;
- `QuantitativeRealization.ExecutionTrace` is indexed by executable machine states and is what
  the exact resource semantics charges.

The candidate bridge proves the output marginal and expected *syntactic query count*. It does not
yet construct a measure on concrete `ExecutionTrace`s, prove that sampled machine work has a
particular expectation, or weaken relational answer contracts by an almost-sure support
argument. Those are useful later corollaries, not assumptions needed by strict PPT.

## Measure-native OTP route and its current boundary

The candidate `Examples/OneTimePad/ComputationalComplexity.lean` supplies a syntactic and
measure-native vertical slice over the existing trusted layers:

- `coinVector n` is recursive `OracleComp coinSpec` syntax with one Boolean query per coordinate;
- `coinVector_path_length` and `coinBitVec_path_length` prove that every complete typed path has
  exactly `n` queries;
- `queryCountMeasure_coinBitVec_eq_dirac` identifies the whole query-count law with
  `Measure.dirac n`, and `expectedQueryCount_coinBitVec_eq` derives expectation `n`;
- `denote_coinVector_eq_uniform` proves the whole Boolean-vector measure is uniform, and
  `denote_coinBitVec_eq_uniform` transports that law through the explicit `bitVecOfFnLE`
  bijection;
- `coinOneTimePad_measureComplete` proves the round-trip law is Dirac at the input; and
- `denote_coinOneTimePad_cipherGivenMsg_eq_uniform` proves the entire ciphertext law is uniform
  for each fixed message, yielding `coinOneTimePad_measurePerfectSecrecyAt`.

This is meaningful feasibility evidence: the random tape is exposed as `n` typed coin
interactions, and the whole-measure OTP proof follows without replacing the program by a claimed
runtime function or reducing it to singleton event probabilities.

The native finite-probability layer now uses `uniformOn Set.univ`. Its focused helpers establish:

- `uniformOn_univ_apply_singleton`, the expected singleton mass on a finite nonempty space;
- `uniformOn_univ_prod`, a full measure equality identifying independent uniforms with the
  uniform law on the product; and
- `map_uniformOn_univ_of_bijective`, a full pushforward equality for a measurable bijection.

The OTP example uses the product and pushforward equalities exactly this way. Repeated products
construct the random tape law, and the XOR map for a fixed message is a measurable bijection that
preserves the entire uniform measure. This proof reasons about the complete ciphertext law,
rather than recovering it from a collection of scalar probability calculations. PMF/evaluation
lemmas remain a useful compatibility surface for existing discrete proofs, not the semantic
foundation of the new path.

The candidate symmetric-encryption layer packages denotations through a `MeasureSemantics`:

- `completeKernel` is the message-indexed round-trip kernel, and `measureComplete` says every row
  is the Dirac law at the input message;
- `perfectSecrecyCipherKernel` is the message-to-ciphertext channel, and
  `measurePerfectSecrecyAt` says all of its rows are equal; and
- the corresponding `..._iff_...` lemmas identify these propositions with kernel-row
  equalities, while `measurePerfectSecrecyAt_of_constant` supports a common-law proof.

The OTP example instantiates the corresponding measure propositions: correctness is a Dirac
round-trip law and perfect secrecy is equality of ciphertext laws, proved through one common
uniform law. The generic equivalence lemmas identify these propositions with kernel-row
equalities whenever the row family is supplied with its measurability proof. This is a complete
semantic result at every width, but not one packed executable family. Measure equality supplies
no executable cost bound by itself.

The packed `coinBitVecFamily` and `CoinBitVecFamily.IsPPTByUnder` declaration identify the correct
uniform proof boundary. They do **not** inhabit it. In particular, the slice does not provide:

- one quantitative realization of the packed family;
- executable, polynomially bounded backend code for the recursion, `Fin.cons`, `bitVecOfFnLE`, or
  XOR;
- a strict-PPT fair-coin handler certificate;
- a resource theorem for closing the sampler through that handler;
- a strict-PPT theorem for key generation, encryption, decryption, or the complete scheme; or
- any backend, complexitylib or otherwise, implementing the variable-width OTP family.

`fairCoinMeasureSpec` is an explicit semantic choice for oracle answers. Assigning the uniform
measure to a coin response does not provide an efficient sampler implementation. Likewise, an
exact query theorem is not an execution-time theorem.

## Integration delta

The current integration worktree adds the following reviewer-visible pieces.

- PolyFun has returned-output-size recovery, a branchwise resolution lemma from bounded
  conforming prefixes plus progress, and exact dependent source data that decomposes a `seqComp`
  execution prefix into left, handoff, and right phases. The source has exactly the composite
  prefix's visible-query length. `PolynomialSeqCompHandoffBound` constrains the second-phase bound
  at every conformingly reachable return, and `PolynomialSeqCompCostCertificate` compares the
  actual composed realization's cost with the exact phase-source cost plus explicit overhead.
  `PolynomialRunBound.seqComp` uses these data and the two component bounds to derive the composite
  cost bound, progress, and resolution; its termination proof does not rely on overhead query
  units.
- VCVio has member-by-member security-family resource contracts with lossless packing
  through one global label/modulus space. The raw dependent sigma-label carrier is not dynamic
  access to the current parameter from a finite polynomial. VCVio also has polynomial
  returned-size bounds on every strict witness and a `BindCertificate` that packages PolyFun's
  generic reachable-handoff and exact structural-cost obligations. A propositional
  bridge constructs a `HandlerCertificate` from packed-handler PPT, an explicit inner-to-outer
  model map, and result conformance for each selected model pair.
- A genuinely dependent handler canary uses different response types (`Bool` and `Fin 3`) and
  proves semantic conformance survives typed substitution.
- A separate constant-positive PolyFun backend drives two Boolean queries across a real handoff.
  The first reply changes the second phase's state and final output, the concrete trace has exact
  cost `⟨6, 2, 4, 1, 1⟩`, and the universal `PolynomialSeqCompCostCertificate` has zero overhead. The
  composition theorem derives `⟨8, 2, 4, 1, 1⟩` solely from the two independent phase bounds.
- The measure-native typed-path bridge provides `pathMeasure`, the canonical
  `queryCountMeasure`, their length and output marginal equalities, and exact or bounded
  measure-native expectations derived from syntactic path theorems.
- Full-measure `uniformOn` product and measurable-bijection pushforward laws support independent
  fair-bit and masking arguments. Generic symmetric-encryption kernels state correctness as
  Dirac rows and perfect secrecy as equality of ciphertext-channel rows. The explicit-coin OTP
  example establishes the corresponding whole-measure correctness and perfect-secrecy theorems.
  All quantitative OTP witnesses remain open.

The sequencing result is a genuine derivation, not a restatement of the desired composite bound.
PolyFun reconstructs the bound, progress, and resolution from exact phase decomposition. It does
not manufacture the one backend-specific fact that cannot be generic: the cost of the structural
realizers used by the assembled machine. `PolynomialSeqCompCostCertificate.certificate` states
that fact against the concrete composite `ExecutionCost`, and its `overhead_le` field requires the
structural allowance to be polynomial. This is generic proof-bearing bounded sequencing, not a
claim that every backend gets cost-free closure.

## Reviewer acceptance matrix

| Claim | Current evidence | Required acceptance evidence | Decision |
| --- | --- | --- | --- |
| Local runtime cannot hide in Lean functions | Executable realizers, exact costs, and `Implements` in the validated baseline | Preserve negative fixtures and trust gates | Accept foundation |
| Oracle answers are honestly charged | Contracts, response-size moduli, conforming traces, progress | Preserve zero-probability and empty-response tests | Accept foundation |
| Security families are uniform | One packed program is required by the validated predicate; a nonconstant packing canary is green | Preserve the packing canary | Accept foundation |
| Returned size follows from charged observations | PolyFun `PolyOutputSizeRecovery`, strict-witness field, and derived returned-size polynomial; root build is green | Preserve root and trust gates | Accept foundation |
| Probability reuses typed syntax | Candidate `pathMeasure`/`queryCountMeasure`, measure marginals, and expected-query theorems | Root build, focused tests, and axiom sweep | Candidate |
| Finite uniform laws are measure-native | Candidate product and bijective-pushforward equalities for `uniformOn univ` | Build `UniformOn` source and focused tests | Candidate |
| Symmetric-encryption security has a kernel form | Candidate generic correctness/ciphertext kernels and row-equivalence lemmas | Build source and OTP example | Candidate API |
| Fair-bit OTP semantics are measure-native | Candidate full uniform, correctness, secrecy, and exact query-count measure equalities | Build through the `Examples` umbrella | Candidate |
| Variable-width fair-bit OTP is uniform PPT | Only the packed proposition is named | One packed realizer, one polynomial, and all-path bound | Not proved |
| Certified bounded sequencing derives the assembled bound | PolyFun `PolynomialRunBound.seqComp` and VCVio `BindCertificate`; root build is green | Preserve root and trust gates | Accept foundation |
| Dependent handlers preserve answer policy | Green `Bool`/`Fin 3` semantic canary | Preserve focused handler test | Accept semantic result |
| Handler substitution preserves PPT | Baseline semantic leaf closure plus candidate certificate ergonomics | Typed substitution machine, trace splice, termination, and resource-polynomial substitution | Not proved |
| A bounded loop is usable by applications | Ranked fixed-loop control canaries in the baseline | Executable uniform fold/loop constructor with exact and polynomial bounds | Not proved |
| complexitylib realizes finite examples | Optional exact pure and one-coin machines behind an isolated adapter | Keep optional package tests and trust report green | Accept replaceable leaf evidence |
| complexitylib is an adequate general backend | No general closure-gate inhabitant or compiler | `OracleTM` compilation/simulation, transcript preservation, and polynomial overhead | Not proved |
| Unqualified conventional `IsPPT` is justified | Backend-relative `...By` predicates only | Concrete adequacy plus uniformity and representation theorems | Defer |

Certified sequencing has crossed its root integration gate. The decisive open usability rows are
bounded iteration and handler substitution;
until they pass, reviewers should expect loop- or handler-heavy clients to construct or analyze
composite machines directly.

## Reproducible validation gates

Record the exact VCVio and PolyFun revisions in the review description. The VCVio manifest must
pin the reviewed PolyFun revision, and both worktrees must be clean before treating a result as a
validated branch result.

Run the full PolyFun validation in the PolyFun checkout:

```bash
cd .lake/packages/PolyFun
./scripts/validate.sh --lint --test --axioms
```

Run the root build, aggregate test library, focused new modules, trust checks, and isolation gates:

```bash
lake exe cache get
lake build
lake build VCVioTest
lake env lean ToMathlib/Probability/UniformOn.lean
lake env lean VCVioTest/UniformOn.lean
lake env lean VCVio/EvalDist/PFunctorPath.lean
lake env lean VCVio/CryptoFoundations/SymmEncAlg/Measure.lean
lake env lean Examples/OneTimePad/ComputationalComplexity.lean
lake env lean VCVioTest/CryptoFoundations/MeasureSemantics.lean
lake env lean VCVioTest/CryptoFoundations/OracleClosure.lean
lake env lean VCVioTest/OracleComp/SecurityFamily.lean
lake exe mk_all --lib VCVio --module --check
lake exe mk_all --lib Examples --module --check
lake exe mk_all --lib VCVioTest --module --check
./scripts/test-axiomsweep.sh
lake exe axiomsweep --check
bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh
bash scripts/check-complexity-backend-isolation.sh
```

Validate the optional backend separately; its result is evidence about that leaf package only:

```bash
cd VCVioComplexity
./scripts/test.sh
./scripts/compatibility-preflight.sh
```

`./scripts/compatibility-preflight.sh --require-upstream-stack` is an intentional red gate while
the recorded complexitylib combinator and asymptotic ports remain unavailable. If it starts
passing, reevaluate the local closure adapters; do not silently broaden the trusted dependency
surface.

No positive result is accepted if it introduces `sorryAx`, a custom axiom, `native_decide`,
`unsafe` computational evidence, an unverified cost meter, or a dependency from core VCVio or
PolyFun to `VCVioComplexity` or complexitylib.

## Promotion and defer decision

Promote the validated baseline as the backend-neutral strict-PPT foundation. After all gates pass,
the polynomial returned-size recovery, family-contract adapter, bounded PolyFun sequencing theorem,
VCVio bind constructor, measure-native typed-path bridge, finite-uniform measure laws, generic
symmetric-encryption kernels, semantic dependent-handler canary, and fair-coin OTP semantic slice
are suitable as incremental VCVio/PolyFun APIs and examples. They demonstrate that the
interaction-first approach is mathematically coherent and can reuse existing probability and
cryptographic proofs.

Defer the claim that the framework is broadly usable for PPT proofs. Do not export an unqualified
`IsPPT`, present `CoinBitVecFamily.IsPPTByUnder` as inhabited, infer execution cost from a measure
equality, or describe semantic handler closing as quantitative closure. Promotion to a generally
usable framework requires, at minimum:

1. a uniform bounded fold or loop sufficient for `coinVector`;
2. quantitative typed handler substitution;
3. an actual packed, variable-width OTP-family witness over at least one nontrivial backend; and
4. a proved adequacy path for any backend advertised as conventional PPT.

The witness in item 3 need not use complexitylib. Any replaceable backend may discharge the
generic realization and cost interfaces. If complexitylib is advertised as conventional PPT,
however, item 4 still requires its own compiler or simulation and polynomial-overhead theorem.

The architecture is feasible and its current positive theorems are non-cheating. Its present
review status is **sound foundation and useful semantic vertical slice; broad compositional PPT
usability deferred**.
