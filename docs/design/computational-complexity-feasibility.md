# Computational-complexity feasibility record

Status: reviewer checkpoint, 2026-08-24. This record evaluates whether the current
interaction-first design is mathematically sound and whether it is ready for ordinary
cryptographic use. The answer is deliberately split:

- the committed foundation is an honest backend-relative definition of strict oracle PPT;
- the current candidate source makes the probability connection and a fair-coin OTP semantic
  slice substantially clearer; and
- broad compositional use is still deferred until bounded iteration, quantitative handler
  substitution, an actual OTP witness, and concrete-backend adequacy are proved.

No declaration is counted as machine-checked merely because it is present in an uncommitted
working tree. The candidate output-recovery and bounded-`seqComp` APIs have passed focused PolyFun
and VCVio checks, but the broad validation gates below remain pending. This record does not claim
a concrete OTP PPT witness.

## Evidence classes

The assessment uses four evidence classes.

| Class | Meaning |
| --- | --- |
| Validated baseline | Committed source covered by the validation recorded in the usability spike. |
| Candidate | Source exists in the integration worktree but must pass the gates below before promotion. |
| Optional backend evidence | A concrete result in `VCVioComplexity`; it does not strengthen the generic definition by fiat. |
| Open obligation | A theorem, executable construction, or adequacy result that is not currently available. |

The immutable validated comparison points are VCVio
`f64bca16c1efe6e558f07683eecae0baa5b18b99`, PolyFun
`73a924e3160c3930da96f8fa8f3c7298c1b06520`, and complexitylib
`b6738219a3a3c50967d6bd16cba9487887ca6b66`. The current integration branches are
`dtumad/complexity-composition` and `dtumad/quantitative-bounded-composition`; their candidate
delta must be reviewed and validated independently of the recorded baseline.

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

## Typed syntax before probability

Probability is an interpretation of the same typed interaction syntax, not the source of its
resource bound. For a probabilistic polynomial functor `P`, `FreeM.withPath program` returns the
selected leaf together with a dependent `Path program`. Every response in that path has exactly
the type determined by its preceding query. The candidate `pathDistribution` is simply `evalDist`
of this instrumented program, and `map_output_pathDistribution` proves that forgetting the path
recovers `evalDist program` exactly.

The strict complexity statement remains pathwise and precedes that interpretation. A total
syntactic roll bound bounds the length of every complete typed path. The candidate
`expectedQueryCount_le_of_isTotalRollBound` integrates this pointwise theorem and derives an
expected query bound. `StrictPPTWitness.expectedQueryCount_le` obtains the corollary when the
chosen resource model admits every typed answer.

Two trace types must not be conflated:

- `FreeM.Path` is indexed by a source program and is what the probability semantics samples;
- `QuantitativeRealization.ExecutionTrace` is indexed by executable machine states and is what
  the exact resource semantics charges.

The candidate bridge proves the output marginal and expected *syntactic query count*. It does not
yet construct a probability distribution on concrete `ExecutionTrace`s, prove that sampled
machine work has a particular expectation, or weaken relational answer contracts by an
almost-sure support argument. Those are useful later corollaries, not assumptions needed by
strict PPT.

## What the fair-coin OTP slice establishes

The candidate `Examples/OneTimePad/ComputationalComplexity.lean` supplies a semantic vertical
slice over the existing trusted syntax and probability layer:

- `coinVector n` is recursive `OracleComp coinSpec` syntax with one Boolean query per coordinate;
- `coinVector_isTotalQueryBound_iff` and `coinBitVec_isTotalQueryBound_iff` characterize the exact
  syntactic budget as `n <= budget`;
- mapping through the explicit executable `bitVecOfFnLE` produces the same distribution as
  canonical uniform sampling of `BitVec n`;
- semantic closing through `uniformSampleImpl` preserves `evalDist`;
- the explicit-coin OTP is complete and perfectly secret; and
- every complete typed path has length exactly `n`, and its expected typed-path query count is
  therefore exactly `n`.

This is meaningful feasibility evidence: the random tape is exposed as `n` typed coin
interactions, and the established probability-level OTP proof can be recovered without replacing
the program by a claimed runtime function.

The packed `coinBitVecFamily` and `CoinBitVecFamily.IsPPTByUnder` declaration identify the correct
uniform proof boundary. They do **not** inhabit it. In particular, the slice does not provide:

- one quantitative realization of the packed family;
- executable, polynomially bounded backend code for the recursion, `Fin.cons`, `bitVecOfFnLE`, or
  XOR;
- a strict-PPT fair-coin handler certificate;
- a resource theorem for closing the sampler through that handler;
- a strict-PPT theorem for key generation, encryption, decryption, or the complete scheme; or
- any complexitylib machine implementing the variable-width OTP.

`fairCoinImpl` is a semantic `QueryImpl`. Distribution preservation does not turn it into an
efficient sampler. Likewise, an exact query theorem is not an execution-time theorem.

## Candidate integration delta

Subject to validation, the current integration worktree adds the following reviewer-visible
pieces.

- PolyFun has candidate returned-output-size recovery, a branchwise resolution lemma from bounded
  conforming prefixes plus progress, and exact dependent source data that decomposes a `seqComp`
  execution prefix into left, handoff, and right phases. The source has exactly the composite
  prefix's visible-query length. `SeqCompHandoffBound` constrains the second-phase bound at every
  conformingly reachable return, and `SeqCompCostCertificate` compares the actual composed
  realization's cost with the exact phase-source cost plus explicit overhead.
  `QuantitativeRealization.RunsWithinUnder.seqComp` uses these data and the two component bounds to
  derive the composite cost bound, progress, and resolution; its termination proof does not rely
  on overhead query units.
- VCVio has candidate member-by-member security-family resource contracts with lossless packing
  through one global label/modulus space. The raw dependent sigma-label carrier is not dynamic
  access to the current parameter from a finite polynomial. VCVio also has polynomial
  returned-size bounds on every strict witness and a `BindCertificate` that derives a reachable
  handoff envelope from the first witness's output-size polynomial. It composes the second
  resource polynomial at that bound and invokes PolyFun's bounded-sequencing theorem, requiring
  only the exact structural cost comparison and a polynomial overhead bound. A propositional
  bridge constructs a `HandlerCertificate` from packed-handler PPT, an explicit inner-to-outer
  model map, and result conformance for each selected model pair.
- A genuinely dependent handler canary uses different response types (`Bool` and `Fin 3`) and
  proves semantic conformance survives typed substitution.
- A separate constant-positive PolyFun backend drives two Boolean queries across a real handoff.
  The first reply changes the second phase's state and final output, the concrete trace has exact
  cost `⟨6, 2, 4, 1, 1⟩`, and the universal `SeqCompCostCertificate` has zero overhead. The
  composition theorem derives `⟨8, 2, 4, 1, 1⟩` solely from the two independent phase bounds.
- The typed-path probability bridge and fair-coin OTP slice provide the results described above.

The sequencing result is a genuine derivation, not a restatement of the desired composite bound.
PolyFun reconstructs the bound, progress, and resolution from exact phase decomposition. It does
not manufacture the one backend-specific fact that cannot be generic: the cost of the structural
realizers used by the assembled machine. `SeqCompCostCertificate.cost_le` states that fact against
the concrete composite `ExecutionCost`, and VCVio requires its overhead to be polynomial. This is
generic proof-bearing bounded sequencing, not a claim that every backend gets cost-free closure.

## Reviewer acceptance matrix

| Claim | Current evidence | Required acceptance evidence | Decision |
| --- | --- | --- | --- |
| Local runtime cannot hide in Lean functions | Executable realizers, exact costs, and `Implements` in the validated baseline | Preserve negative fixtures and trust gates | Accept foundation |
| Oracle answers are honestly charged | Contracts, response-size moduli, conforming traces, progress | Preserve zero-probability and empty-response tests | Accept foundation |
| Security families are uniform | One packed program is required by the validated predicate | Validate candidate family-contract packing tests | Accept after gates |
| Returned size follows from charged observations | Candidate `PolyOutputSizeRecovery`, strict-witness field, and derived returned-size polynomial; focused checks are green | Broad PolyFun/root builds, tests, and axiom sweeps | Candidate after broad gates |
| Probability reuses typed syntax | Candidate path marginal and expected-query theorems | Root build, focused tests, and axiom sweep | Candidate |
| Fair-bit OTP semantics are correct | Candidate exact query, distribution, completeness, and secrecy proofs | Build the example through the `Examples` umbrella | Candidate |
| Fair-bit OTP is uniform PPT | Only the packed proposition is named | One packed realizer, one polynomial, and all-path bound | Not proved |
| Certified bounded sequencing derives the assembled bound | Candidate `RunsWithinUnder.seqComp` and VCVio `BindCertificate`; focused checks are green | Broad PolyFun/root builds, tests, and axiom sweeps | Candidate after broad gates |
| Dependent handlers preserve answer policy | Candidate `Bool`/`Fin 3` semantic canary | Build focused handler tests | Candidate semantic result |
| Handler substitution preserves PPT | Baseline semantic leaf closure plus candidate certificate ergonomics | Typed substitution machine, trace splice, termination, and resource-polynomial substitution | Not proved |
| A bounded loop is usable by applications | Ranked fixed-loop control canaries in the baseline | Executable uniform fold/loop constructor with exact and polynomial bounds | Not proved |
| complexitylib realizes finite examples | Optional exact pure and one-coin machines | Keep optional package tests and trust report green | Accept optional evidence |
| complexitylib is an adequate general backend | No general closure-gate inhabitant or compiler | `OracleTM` compilation/simulation, transcript preservation, and polynomial overhead | Not proved |
| Unqualified conventional `IsPPT` is justified | Backend-relative `...By` predicates only | Concrete adequacy plus uniformity and representation theorems | Defer |

Certified sequencing has crossed its focused implementation gate but still awaits broad branch
validation. The decisive open usability rows are bounded iteration and handler substitution;
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
lake env lean Examples/OneTimePad/ComputationalComplexity.lean
lake env lean VCVioTest/CryptoFoundations/PathSemantics.lean
lake env lean VCVioTest/CryptoFoundations/OracleClosure.lean
lake exe mk_all --lib VCVio --module --check
lake exe mk_all --lib Examples --module --check
lake exe mk_all --lib VCVioTest --module --check
./scripts/test-axiomsweep.sh
lake exe axiomsweep --check
bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh
bash scripts/test-complexity-backend-isolation.sh
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
VCVio bind constructor, typed-path probability bridge, semantic dependent-handler canary, and
fair-coin OTP semantic slice are suitable as incremental VCVio/PolyFun APIs and examples. They
demonstrate that the interaction-first approach is mathematically coherent and can reuse existing
probability and cryptographic proofs.

Defer the claim that the framework is broadly usable for PPT proofs. Do not export an unqualified
`IsPPT`, present `CoinBitVecFamily.IsPPTByUnder` as inhabited, or describe semantic handler closing
as quantitative closure. Promotion to a generally usable framework requires, at minimum:

1. a uniform bounded fold or loop sufficient for `coinVector`;
2. quantitative typed handler substitution;
3. an actual packed OTP witness over at least one nontrivial backend; and
4. a proved adequacy path for any backend advertised as conventional PPT.

The architecture is feasible and its current positive theorems are non-cheating. Its present
review status is **sound foundation and useful semantic vertical slice; broad compositional PPT
usability deferred**.
