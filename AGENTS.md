# VCVio — AI Agent Guide

Machine-checked cryptographic proofs in Lean, built on Mathlib.

## Fast Start

1. Run `lake exe cache get && lake build`.
2. Read `Examples/OneTimePad/Basic.lean` for a compact modern proof (correctness and privacy).
3. Choose the work area by task. Use `VCVio/` for oracle/probability/program-logic work.
   Use `LatticeCrypto/` for lattice schemes and reductions, and `LatticeCryptoTest/` for vectors or differential tests.
4. If `𝒟` lemmas fail unexpectedly, check for `[OracleSpec.AnswerMeasure spec]`.
   Also check for a measurable space on the result type. Oracle answer types need none.
   The concrete `unifSpec` and `coinSpec` have global uniform-measure instances.
   Other specs need a chosen interpretation.

`AGENTS.md` is the canonical guide. `CLAUDE.md` is a symlink to this file.

## Attribution, Headers, And Docstrings

Follow [`CONTRIBUTING.md`](CONTRIBUTING.md) for the repo's explicit attribution policy.

- New Lean files should use the standard copyright / licence / authors header and a module docstring.
- For ordinary Lean source files, use the standard prologue layout: header, blank line, `module`, public imports, blank line, module docstring.
- Docstrings must be intrinsic and descriptive. Cross-reference live sibling definitions when helpful, but do not mention removed or renamed declarations, change history, or use reactive wording such as "replaces" or "renamed from".
- Preserve existing headers on routine edits.
- Only rewrite attribution when a file is genuinely new or materially replaced.
- Do not add a separate AI-attribution line.
- For inline section breaks within a Lean file, use Mathlib-style doc-comment headers `/-! ## Title -/`.
  The multi-line `/-! ## Title \n\n explanation -/` form is also suitable.
  **Do not use ASCII banners** such as `-- ====...===` flanking a `-- § Title` line.
  `doc-gen4` renders the `/-!` form but does not render ASCII banners, which make the file feel artificially partitioned.
  A section that seems to need a loud header usually needs its own `namespace` or file.
  See *Section Headers Within A File* in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Writing

Before you draft or revise prose, follow the [writing workflow](docs/agents/write-technical-prose.md).
It applies to documentation, docstrings, comments, commit messages, PR and issue text, and review
comments. Assess existing prose against the [writing standard](docs/agents/writing.md) rather than
preserving its defects. Before you hand over a PR description, run `scripts/check-writing.py` on
the changed prose, the commit messages, and the draft. Its findings are advisory, so read each one.

## Module Scopes

Active Lean libraries and tests use Lean's module system. Put declarations in a `public section`.
Use `public meta section` for tactic and elaborator code.
Existing ordinary source files use `@[expose] public section` to preserve downstream definitional equalities from before migration.
New files use plain `public section` and expose individual definitions with `@[expose]` where unfolding is part of the intended API.

The per-library count of broadly exposed files is a ceiling (`scripts/check-expose-boundary.sh`, baseline `scripts/expose_boundary_baseline.tsv`).
Converting a file lowers that ceiling. Raising it needs an explicit baseline change under review.
Executable and runtime implementation modules should use opaque `public section` when callers do not need to unfold their definitions.

- Use `public import` for dependencies that form part of the module's transitive public surface and
  `public meta import` for exported tactic/elaborator dependencies.
- Use plain `import` for implementation-only dependencies. A proof module may use `import all` to
  access an unexposed implementation from the same dependency when proving its public API.
- Do not enable `backward.privateInPublic` or `backward.proofsInPublic`.
  Resolve visibility and proof-metavariable issues directly.
- Keep the dormant `Interop` library outside this policy until it is migrated separately.

Section `variable` lines carry an instance assumption only when the theorems in scope share it.
Lean auto-includes an instance-implicit section variable in every theorem that mentions its types.
Suppose most theorems ignore section-wide `[Fintype Chal] [Inhabited Chal] [SampleableType Chal]` assumptions.
Those assumptions require an `omit [...] in` line before each such theorem.
Put the assumptions on the declarations that use them, or open a `section` around the block that shares them.

Never declare an instance assumption that another in scope implies (`[Finite X]` beside `[SampleableType X]`).
Use `omit` for a single exceptional case.
See *Section Variables* in [`CONTRIBUTING.md`](CONTRIBUTING.md) and gotcha 31.

## What This Project Is

VCVio is a framework for formal cryptographic proofs built around `OracleComp spec α`.
This type is the free monad on the polynomial functor induced by an oracle signature `OracleSpec ι := ι → Type`.
Its universal fold `simulateQ impl : OracleComp spec α → r α` is the unique monad morphism extending any `impl : QueryImpl spec r` to the free monad.
For `OracleComp`, `support` is the set of possible outputs, equal to the fold into `SetM` that answers every query with `Set.univ`.

The probability semantics `evalDist` / `𝒟[…]` is a successful-output Mathlib `Measure`.
It folds the answer measures chosen by `[OracleSpec.AnswerMeasure spec]`. Missing mass is failure.
Events are written `Pr{let x ← oa}[p x]`, whose braces take any `do` sequence with its sugar.
A single output is `Pr{let x ← oa}[x = a]`.
The failure probability is `prFail oa`, and distributional equality is `oa =ᵈ ob`.

Uniform answer measures are `[OracleSpec.UniformAnswerMeasure spec]`.
`ProbComp α := OracleComp unifSpec α` specializes to computations whose only oracle is uniform selection.

The repo also includes a first-class lattice cryptography library under `LatticeCrypto/`, built on top of the `VCVio` framework.
That layer contains generic lattice algebra plus ML-DSA, ML-KEM, and Falcon specifications, security statements, concrete implementations, and tests.
The native FFI bridges live in the separate `Extern/` library.

## Repo Map

See the [repository ownership map](docs/design/repository-layout.md) for placement rules,
build boundaries and the staged consolidation.

- `VCVio/`: generic oracle-computation framework, program logic, crypto abstractions, and generic reductions.
- `VCVio/Algorithms/` contains shared pure SHA-2, HMAC, MGF1, SHA-3 and SHAKE implementations.
  Their independent regressions run with `lake exe algorithm_tests`.
- `VCVioCslib/`: optional cslib-backed non-uniform P/poly adapters.
  It is a separate Lake library so core `VCVio` remains backend-neutral.
- `ToMathlib/`: local Mathlib-facing utilities and lemmas intended to remain below the framework layer.
- `Extern/`: native FFI surface, with the `@[extern]` bindings (SHA-3/SHAKE, ML-KEM, ML-DSA, Falcon) and the FFI-backed concrete instances that reach them.
  No proof library may import it.
  The backing `extern_lib`s become empty stubs when `third_party/` submodules are absent.
- `LatticeCrypto/`: lattice-specific algebra, hardness assumptions, scheme definitions, security theorems, and concrete implementations.
- `HashSig/`: hash-based signatures.
  SLH-DSA (SPHINCS+, FIPS 205) has proof-level specs, component-level FIPS conformance results, and an SUF-CMA bound.
  The bound gives strong unforgeability in the classical random-oracle model with three oracles: the tweakable hash, `Hmsg`, and `PRFmsg`.
  Strong unforgeability gives EUF-CMA at the same bound.
  `securityTarget_two_one` holds per public seed and averaged over seed distributions.
  `shakeRomScheme` states a model of the SHAKE parameter sets over a single SHAKE256 random oracle on byte strings.
  `shakeRomScheme_map_shakeAnswer` gives the library's FIPS 205 SHAKE internal algorithms when SHAKE256 answers that oracle.
  These algorithms are checked against pinned NIST ACVP vectors at SLH-DSA-SHAKE-128f, 192f, and 256f.
  In that model, the SUF-CMA bound adds `(q_s + 1) / 2^{8n}` and a weak-key term to the three-oracle bound.
  At `n = 32`, the weak-key term is only the weak seeds' share of the bound at every seed.
  The theorems are `shakeStrongAdvantage_le_securityBound` and, per public seed, `shakeStrongAdvantage_pure_le_securityBound`.
  Hedged signing replaces `(q_s + 1) / 2^{8n}` with `1 / 2^{8n} + q_s (q_h + q_s + 1) / 2^{16n}` (`shakeStrongAdvantage_le_securityBound_hedged`).
  The EUF-CMA forms are `shakeAdvantage_le_securityBound`, `shakeAdvantage_pure_le_securityBound`
  and `shakeAdvantage_le_securityBound_hedged`.
  `Security/Wire.lean` transports the bounds to strict byte-list public keys and signatures in pure mode with a fixed checked context.
  It preserves both query budgets and strong freshness.
  Canonical parsing and injectivity are proved in `Codec.lean`. `Security/Profile.lean` binds SHAKE parameters, signing mode, context,
  codecs, uniform seed sampling, and the matching exact bound evaluator. Prehash collision
  accounting, variable-length-XOF adversaries, and complete FIPS conformance remain open.
  The specialized `HashSig/SLHDSA/SHAKE128s/` subtree contains `Statement/`, `Proof/` and `Bridge/`
  for deterministic pure-mode SHAKE-128s over one fixed 30-byte random oracle, with independent
  uniform key seeds. `SLHDSA.SHAKE128s.slhDsa_sufCma_127` allows message/context signing requests
  and byte-string signatures.
  Its work counts signing requests, direct adversary hash calls and final-verification hash calls.
  There is a separate `2^64` signing-request lifetime cap. Key-generation and signer hashes are excluded.
  The general security, wire, evaluator and
  certificate modules remain alongside it. `SHAKE128s/Bridge/Wire.lean` exports the exact
  fixed-context advantage equality and the syntactic-to-counted budget transports.
  The verifier overhead has a proved universal cap of 3929 oracle calls. `SHAKE128s/Statement/Theorems/WireStrongUnforgeability.lean`
  exports `wireStrongAdvantage_le_workBound` and `wireStrongAdvantage_le_min_bound` for
  `RomQueryBound qh qs` and `qs ≤ 2^64`. The common scope is deterministic signing, a fixed valid
  context, independent uniform seeds, and the shared fixed-30-byte oracle.
  `slhdsa_shake128s_game_tests` exercises actual counted work through the proved-equal computable
  runner in `HashSigTest/SLHDSA/SHAKE128s/Support.lean`. `slhdsa_shake128s_wire_bridge_tests`
  executes the actual adapter's translation, freshness, framing and rejection controls.
  Both are explicit `lake test` steps. See
  [the specialized design record](docs/design/slh-dsa-shake128s-suf-cma.md).
  `HashSig/` is a peer of `LatticeCrypto/`.
  It depends on `VCVio`/`ToMathlib`, but nothing in those libraries imports it back.
- `LatticeCryptoTest/`: ACVP vectors, executable regression tests, and cross-checks against native backends.
- `VCVioTest/`: framework smoke tests and test support modules.
- `VCVioWidgets/`: optional widget experiments and visualizations.
- `VCVioCslib/`: optional cslib-backed non-uniform P/poly certificates and security-game adapters.
  It stays outside the default library graph but participates in repository validation.
- `VCVioComplexity/`: optional isolated Lake package for the complexitylib-backed exact-machine substrate.
  It is not part of VCVio's default dependency graph.
- `Examples/`: compact framework examples such as OneTimePad, ElGamal, Schnorr, and program-logic tactic walkthroughs.
- `Interop/`: experimental bridges to Rust verification frontends (hax, aeneas). **Strict TCB isolation**: nothing in core VCVio depends on it. See `docs/agents/interop.md`.
- `csrc/`: C FFI shims used for differential testing against native ML-DSA, ML-KEM, and Falcon code.
- `third_party/`: native backends as git submodules.
  When they are not checked out (fresh clones, Lake dependency checkouts), the native `extern_lib` targets build as empty stub archives.

## Placement policy

The [repository ownership map](docs/design/repository-layout.md) defines current roots and
planned migration slices. Shared pure implementations belong in `VCVio/Algorithms/`, named
constructions and their proofs in `VCVio/Schemes/`, and cryptographic interfaces, assumptions,
games and generic reduction theory in `VCVio/CryptoFoundations/`. Examples are instructional
consumers. Existing HashSig and LatticeCrypto peers migrate only in dependency-complete slices.

Keep implementations unique, preserve the FFI/test boundary, and add a separate library only
for a dependency, trust or build-isolation requirement. The import guards enforce pure-algorithm independence,
optional interop isolation and the FFI boundary. Other placement rules guide review.

## Module Layering

For `VCVio/`:

```
ToMathlib → Prelude → EvalDist/Defs → OracleComp core → EvalDist bridge
  → {SimSemantics, QueryTracking, Constructions, Coercions, ProbComp}
  → {ProgramLogic, CryptoFoundations, CryptoFoundations/Asymptotics} → Examples
```

New files must respect this DAG. `EvalDist/` must never import from `OracleComp/`.

For `LatticeCrypto/`, the rough dependency direction is:

```
{Ring/*, DiscreteGaussian}
  → HardnessAssumptions
  → {MLDSA, MLKEM, Falcon}
  → Concrete implementations / security wrappers
  → Extern (FFI bindings + FFI-backed instances)
  → LatticeCryptoTest
```

Scheme-specific code in `LatticeCrypto/` may depend on `VCVio/CryptoFoundations`, but not the other way around.

The native FFI surface lives in `Extern/`: it may import `VCVio`, `LatticeCrypto`,
and `ToMathlib`, but no proof library (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`,
`HashSig/`, `Examples/`, `VCVioWidgets/`, `Interop/`) may import `Extern.…`. That
keeps every proof library and any downstream Lake project requiring VCVio link-safe when the `third_party/` submodules are absent.
`scripts/check-extern-isolation.sh` enforces the boundary on every PR.

For `Interop/`, the dependency contract is one-way:

```
Interop/{Hax,Aeneas,Rust}/  →  VCVio/, ToMathlib/, (Hax.…), (Aeneas.…)
```

`Interop/**` may **never** be imported from `VCVio/`, `LatticeCrypto/`,
`LatticeCryptoTest/`, `Examples/`, `ToMathlib/`, `Extern/`, `VCVioWidgets/`,
or `VCVioTest/`. This contract is enforced by
`scripts/check-interop-isolation.sh` and the
`Interop TCB Isolation` GitHub workflow on every PR.

## Critical Gotchas

1. **Probability assumptions are explicit for arbitrary specs.** `support` on `OracleComp spec` works without a probability interpretation.
   Direct `evalDist` / `𝒟[…]` and `Pr{…}[…]` need `[OracleSpec.AnswerMeasure spec]`.
   For `𝒟[…]`, they also need an ambient `MeasurableSpace` on the result.
   Oracle answer measures live on the discrete σ-algebra, so answer types take no `MeasurableSpace` hypotheses.
   Continuous answers belong at the `PFunctor.FreeM` level.
   Uniform-measure instances are global for `unifSpec` and `coinSpec`.
   For another spec, uniform answers use `[OracleSpec.UniformAnswerMeasure spec]`.
   `UniformAnswerMeasure.ofFiniteNonempty` builds a local instance on the component spec from `Finite`/`Nonempty` answer types.
   Sums get their instances from `UniformAnswerMeasure.add`.
   There are no bundled `spec.Fintype` / `spec.Inhabited` / `spec.DecidableEq` classes.
   Data on answer types are ordinary hypotheses on `spec.Range t` (see gotcha 12).
2. **`autoImplicit = false` is set globally in `lakefile.lean`**. Do not add `set_option autoImplicit false` in individual files. Every variable must be explicitly declared.
3. **`𝒟[oa]` is definitionally the measure fold** `PFunctor.FreeM.denote` of the answer measures.
   `Pr{…}[…]` is `prEvent` of that measure.
   `support` is PolyFun's `MonadAttach` support, equal to the fold into `SetM` that answers every query with `Set.univ`.
   `PFunctor.FreeM.support_eq_liftM_univ` gives this equality.
   The definitional identities are internal to `VCVio/EvalDist/**` and `VCVio/OracleComp/**`.
   Code outside those directories uses the public equation lemmas (`PFunctor.FreeM.evalDist_eq_denote`, `prEvent_def`).
   Existing downstream `rfl` uses are grandfathered. New proofs use the public equations.
4. **Use `+` for combining oracle specs.** `++ₒ` is dead.
5. **Follow only uncommented code.** Commented-out code is legacy.
   Use `Examples/OneTimePad/Basic.lean` as canonical reference.
6. **Preserve partial proofs** with `stop` instead of deleting large proof blocks.
7. **Do not disable linters to silence errors**.
   Do not use `set_option linter.* false` or `set_option weak.linter.* false`.
   Do not add repo-level `leanOptions` that turn lints off to dodge a fixable issue. Fix the root cause instead.
   The one deliberate, documented exception is `weak.linter.unicodeLinter, false` in `lakefile.lean`.
   This exception permits FIPS-204 math notation and diacritics in cited author names.
8. **Interop TCB isolation is mandatory**. Core VCVio (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `Examples/`, `LatticeCryptoTest/`, `Extern/`, `VCVioWidgets/`, `VCVioTest/`) must never `import Interop.…`, `import Hax.…`, or `import Aeneas.…`. CI fails the PR if it does. See `docs/agents/interop.md`.
9. **Extern link-safety isolation is mandatory**.
   Proof libraries (`VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `HashSig/`, `Examples/`, `VCVioWidgets/`, `Interop/`) must never `import Extern.…`.
   The native backends behind it build as empty stubs whenever the `third_party/` submodules are absent.
   Those submodules are always absent for Lake dependency checkouts. An import of `Extern` would therefore break downstream executable links.
   Test libraries may import it. `scripts/check-extern-isolation.sh` enforces the boundary in CI.

10. **Probability is `Measure`/`Kernel`, never `PMF`.** Semantic code uses `𝒟[…]`, `Pr{…}[…]`, `=ᵈ`, Mathlib measures and kernels.
    Mathlib owns `PMF`, so VCVio cannot deprecate it.
    The environment linter `ToMathlib.Lint.usesPMF` reports any declaration that uses it directly.
    `scripts/nolints.json` holds no exceptions for it.
    Code written against VCVio's removed discrete API (`SPMF`, `Pr[= x | mx]`, `IsUniformSpec`, …) converts with the codemod and guide in [`docs/agents/probability-migration.md`](docs/agents/probability-migration.md).
    See `docs/reading/denotational-probability-semantics.md`.

11. **Name the reduction in security theorems.** Write `bound ≤ Pr{let b ← exp (myReduction adv)}[b = true]`, never `∃ B, bound ≤ Pr{let b ← exp B}[b = true]`.
    Adversary types such as `X → ProbComp W` carry no resource bound. `Classical.choice` can pick a witness directly.
    Thus the existential form holds for every scheme and passes the axiom sweep.
    The same applies to simulators (`∃ sim ζ, HVZK sim ζ` holds with `ζ := 1`), extractors, and distinguishers.
    If the reduction does not exist yet, use a named `sorry` definition or a warned placeholder instead.
    See [`docs/agents/crypto.md`](docs/agents/crypto.md#name-the-reduction-in-the-theorem-statement).

12. **No global instance may conclude `C spec.Domain` or `C (spec.Range t)` for a generic `spec`.**
    `Domain` and `Range` are reducible. A domain instance is therefore indexed as `C ι`, and a range instance as `C (?spec ?t)`.
    Such an instance becomes a candidate for every `C _` goal with `spec` undetermined.
    Search then invents a specification through `ofFn`.
    It either times out or routes ordinary `DecidableEq`/`Fintype`/`Inhabited` instances through oracle data (#772).
    Write `[DecidableEq ι]` for index equality.
    For answer types, write `[DecidableEq (spec.Range t)]`, `[Fintype (spec.Range t)]`, `[Inhabited (spec.Range t)]`.
    Quantify those hypotheses over `t` only when a statement ranges over arbitrary queries.
    Concrete specifications reduce to their answer types. `VCVioTest/OracleComp/SpecInstanceSearch.lean` guards this.

For the full list, see `docs/agents/gotchas.md`.

## Naming Conventions

Follow Mathlib convention: `{head_symbol}_{operation}_{rhs_form}`.
Examples: `prEvent_bind_eq_lintegral`, `support_pure`, `simulateQ_map`.
Structures use UpperCamelCase: `SecurityGame`, `SymmEncAlg`, `RelTriple`.
Security-notion names may begin with an underscore-separated acronym:
`IND_CPA_Advantage`, `SM_DT_UD_Adversary`, `IND_CPA_OneTime_Game`, `OW_CPA_oracleSpec`.

`scripts/lint.py` accepts a `defsWithUnderscore` finding without a `nolints.json` entry when the following conditions hold.
Each underscored name component starts with an acronym of two or more capitals or digits.
Every later segment except the last starts with a capital.
Security notions, experiments, games, and advantages follow
[`docs/agents/crypto.md`](docs/agents/crypto.md#naming).

## Canonical Examples

- Compact modern crypto proof: `Examples/OneTimePad/Basic.lean`
- ElGamal IND-CPA via the generic one-time DDH lift: `Examples/ElGamal/Basic.lean`
- Schnorr sigma protocol (completeness, soundness, HVZK): `VCVio/Schemes/Schnorr/SigmaProtocol.lean`
- Concrete transcript and commitment walkthroughs: `Examples/Schnorr/Basic.lean`,
  `Examples/Pedersen.lean`
- Oracle computation core: `VCVio/OracleComp/OracleComp.lean`
- Probability lemmas: `VCVio/EvalDist/ProbabilityNotation.lean`, `VCVio/EvalDist/ProbabilityBounds.lean`, `VCVio/OracleComp/EvalDist/Measure.lean`
- Equality in distribution across monads (`mx =ᵈ my`): `VCVio/EvalDist/EvalDistEq.lean`
- SubSpec / coercions: `VCVio/OracleComp/Coercions/SubSpec.lean`
- `QueryImpl` instrumentation primitives (`preInsert` / `postInsert` and their bridge lemmas): `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions/Core.lean`. Prefer these (or their downstream wrappers `withTraceBefore` / `withTrace` / `withCost` / `withLogging`) when wrapping a `QueryImpl` with a per-query side effect, so the generic theory in that file applies.
- DLog / CDH / DDH via HHS: `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`
- Cost model / polynomial time: `VCVio/OracleComp/QueryTracking/CostModel.lean`
- Query cost / weighted expected cost: `VCVio/OracleComp/QueryTracking/QueryCost.lean`, `VCVio/OracleComp/QueryTracking/WriterCost.lean`
- Quantitative realizability, syntactic resource traces, and generic polynomial resource
  certificates:
  `PolyFun/Realizability/Quantitative.lean`,
  `PolyFun/Realizability/Quantitative/Resource.lean`
- Strict backend-relative oracle PPT crypto facade:
  `VCVio/CryptoFoundations/Asymptotics/ComputationalComplexity.lean`
- Proof-bearing oracle-handler closure seam:
  `VCVio/CryptoFoundations/Asymptotics/OracleClosure.lean`
- Conservative PPT certificate lookup:
  `VCVio/CryptoFoundations/Asymptotics/ComplexityTactics.lean`
- Syntactic ElGamal complexity canary:
  `Examples/ElGamal/ComputationalComplexity.lean`
- Optional exact complexitylib machine substrate:
  `VCVioComplexity/VCVioComplexity/Backend/TuringMachine.lean`
- Complexitylib polynomial adapter and end-to-end pure canary:
  `VCVioComplexity/VCVioComplexity/Backend/Polynomial.lean`,
  `VCVioComplexity/VCVioComplexityTest/Backend/PureCanary.lean`
- End-to-end complexitylib canary with one enabled fair-coin query:
  `VCVioComplexity/VCVioComplexityTest/Backend/OracleCanary.lean`
- Asymptotic security games: `VCVio/CryptoFoundations/Asymptotics/Security.lean`
- Negligible function algebra: `VCVio/CryptoFoundations/Asymptotics/Negligible.lean`
- Query enforcement: `VCVio/OracleComp/QueryTracking/Enforcement.lean`
- Seeded (Bellare-Neven) forking lemma: `VCVio/CryptoFoundations/SeededFork.lean`
- Replay-based forking lemma: `VCVio/CryptoFoundations/ReplayFork.lean`
- Independent products of computations: `VCVio/EvalDist/IndepProduct.lean`
- Drawing without replacement and its expected draw count: `VCVio/OracleComp/Constructions/WithoutReplacement.lean`, `ToMathlib/Probability/NegativeHypergeometric.lean`
- Expected values of `ℝ≥0∞`-valued functionals (`wp` and `∫⁻` against `𝒟[mx]`): `VCVio/ProgramLogic/Unary/HoareTriple.lean`
- Fischlin transform: `VCVio/CryptoFoundations/Fischlin/` (`Defs`, `CostAccounting`, `Completeness`, `KnowledgeSoundness`)
- Interaction type tree and path: `PolyFun/Interaction/Basic/TypeTree.lean`
- Two-party roles and strategies: `PolyFun/Interaction/TwoParty/Strategy.lean`
- Two-party composition and factorization: `PolyFun/Interaction/TwoParty/Compose.lean`
- Multiparty local views: `PolyFun/Interaction/Multiparty/Core.lean`
- Concurrent specs and frontiers: `PolyFun/Interaction/Concurrent/Spec.lean`, `PolyFun/Interaction/Concurrent/Frontier.lean`
- Concurrent processes and execution: `PolyFun/Interaction/Concurrent/Process.lean`
- Open systems (interfaces, composition): `PolyFun/Interaction/Open/OpenTheory.lean`
- Open processes (boundary traffic, UC bridge): `PolyFun/Interaction/Open/OpenProcess.lean` (monad-parametric `OpenProcess m Party Δ` with intrinsic `stepSampler` field and `OpenStep.boundaryTrace`)
- Concrete open-theory model: `PolyFun/Interaction/Open/OpenProcessModel.lean` (`openTheory Party m schedulerSampler` threads `TypeTree.Sampler` through `map` / `par` / `wire` / `plug`)
- UC emulation and security: `PolyFun/Interaction/Open/Emulates.lean`
- Computational UC observation layer: `VCVio/Interaction/UC/Computational.lean`
- Per-node samplers as data (`TypeTree.Sampler m tree` = `Decoration (fun X => m X) tree`): `PolyFun/Interaction/Basic/Sampler.lean`
- `TypeTree.Fintype` / `TypeTree.Nonempty` ornaments + canonical uniform sampler: `PolyFun/Interaction/Basic/TypeTreeFintype.lean`, `VCVio/Interaction/UC/Runtime.lean`
- Oracle-aware runtime semantics (monad-parametric process execution, `processSemanticsOracle`): `VCVio/Interaction/UC/Runtime.lean`.
  It takes no `sampler` argument and reads the sampler from `process.stepSampler`.
- Observation-interface `ObservedCompEmulates 0` smoke test: `Examples/OneTimePad/UC.lean`
- Reactive single-use OTP execution and simulation with private environment state:
  `Examples/OneTimePad/Reactive.lean`, `Examples/OneTimePad/Reactive/Security.lean`
- Semantic counterexamples (plaintext leakage, wrong decoding, key reuse, delivery and fuel):
  `Examples/OneTimePad/Reactive/Separation.lean`, `VCVioTest/ReactiveNetworkAdversarial.lean`
- Interaction examples: `PolyFunTest/Interaction/TwoParty/Examples.lean`, `PolyFunTest/Interaction/Multiparty/Examples.lean`, `PolyFunTest/Interaction/Concurrent/Examples.lean`
- Program logic tactics: `VCVio/ProgramLogic/Tactics.lean`
- Program logic tactic walkthroughs: `Examples/ProgramLogic/`
- Generic lattice ring layer: `LatticeCrypto/Ring/Core.lean`, `LatticeCrypto/Ring/Kernel.lean`, `LatticeCrypto/Ring/VectorBackend.lean`, `LatticeCrypto/Ring/Transform.lean`, `LatticeCrypto/Ring/NTTCert.lean` (matrix and structural butterfly-stage certificates), `LatticeCrypto/Ring/Norms.lean`, `LatticeCrypto/Ring/Rounding.lean`
- ML-DSA proof-level IDS: `LatticeCrypto/MLDSA/Scheme.lean`
- ML-DSA FIPS signing layer: `LatticeCrypto/MLDSA/Signature.lean`
- ML-KEM internal deterministic core: `LatticeCrypto/MLKEM/Internal.lean`
- ML-KEM top-level KEM wrapper: `LatticeCrypto/MLKEM/KEM.lean`
- Falcon GPV instantiation: `LatticeCrypto/Falcon/Scheme.lean`
- Lattice hardness assumptions: `LatticeCrypto/HardnessAssumptions/LearningWithErrors.lean`, `LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean`
- Differential and vector tests: `LatticeCryptoTest/`
- Rust verification interop (hax / aeneas): `Interop/Rust/Common.lean`, `Interop/README.md`, `scripts/check-interop-isolation.sh`

## Program Logic Tactics

For new program-logic proofs, import `VCVio.ProgramLogic.Tactics`.
`VCVio.ProgramLogic.Notation` holds the notation. `Tactics.lean` is the canonical
interactive proof mode.

For the tactic reference, proof-mode entry points, and workflow details, see
[`docs/agents/program-logic.md`](docs/agents/program-logic.md). The two
`@[vcspec]` and `@[wpStep]` registries are indexed via
`Lean.Meta.Sym.Pattern` / `Lean.Meta.Sym.DiscrTree`.
`Sym.*` is under active development in core Lean.
See the *Internal Architecture* and *SymM Stability Note* sections of that doc for the churn classes to watch at each toolchain bump.
The `@[wpStep]` rewrites run through `Sym.Simp.mkTheoremFromDecl` and `Sym.simpGoal`.

## Building

```bash
lake exe cache get && lake build
```

`lake build` builds the seven proof libraries (the default targets).
`lake build VCVio` is the fast path for framework-only work.
`./scripts/validate.sh` runs the fast per-PR CI checks locally in CI's order, including the optional `VCVioCslib` facade.
The checks cover the build and warning budget, umbrella check, remaining boundary checks, style linters, and agent-docs checks.
`--lint` adds Batteries' environment linters, one process per proof library as in CI.

`lake lint` runs both source-style and environment checks.
`-- --style-only` and `-- --env-only` select either pass, and `-- --no-build` requires existing proof oleans.
Findings must exactly match `scripts/nolints.json`: obsolete entries and unlisted findings fail.
After you fix findings, `lake lint -- --prune-baseline` safely removes obsolete entries across all eight checked libraries and refuses additions.
PR CI also checks that the baseline only shrinks against the merge base.

`--test` adds `lake test` (the three test libraries, the smoke test, and the SLH-DSA test executables).
`--ffi` adds the native ML-KEM / ML-DSA / Falcon executables to `--test`, and `--axioms` adds the axiom sweep.
The eager-initialization ratchet runs in the default pass, after the boundary ratchets.
It reads the oleans that the build produced.
`--test` runs it a second time over `VCVioTest` and `LatticeCryptoTest`, whose oleans `lake test` builds.

CI runs the timed build on the non-test Lean libraries:
`ToMathlib`, `VCVio`, `VCVioCslib`, `LatticeCrypto`, `Extern`, `HashSig`, `Examples`,
and `VCVioWidgets`. The dormant `Interop` target remains excluded.
Test libraries and test executables are not part of the timed build.
CI only times the smoke module separately with `lake env lean VCVioTest/Smoke.lean`.

CI keeps two caches: `.lake/packages` and the project's own `.lake/build`.
`lean-toolchain` and `lake-manifest.json` determine the key for `.lake/packages`.
Every `main` run saves `.lake/build`, and every run restores it.
Only `main` saves, so pull-request code never publishes a cache that another run loads.
The `Lint` job restores the same caches and builds the changed modules itself, so it runs alongside `Build Project`.

Lake rebuilds a module when the content hash of its source or imports changes.
A restored build therefore only saves work and never changes a verdict.
Lake replays the stored messages of modules it does not rebuild, so the warning budgets still see every warning.
The nightly scheduled run and a manual run with `clean_build` skip the build cache.

An incremental build's wall time depends on what the change invalidated, so the timing report compares modules.
`scripts/module_times.py` keeps the latest `Built <module> (<time>)` for every module in `.lake/build/vcvio-module-times.json`.
That file travels with the build cache.
The report compares the modules that this run rebuilt against those times.
The table's sums before and after estimate clean-build compile time.

After the build, CI runs `./scripts/test-axiomsweep.sh` and then `lake exe axiomsweep --check`.
The sweep accounts for kernel-level axiom/`sorry` use in every declaration in the non-test libraries.
The committed baseline `scripts/axiom_baseline.json` gates its findings.
It fails on *new* `sorryAx` or non-standard-axiom taint.

After you intentionally add or close a `sorry`, run `lake exe axiomsweep --update-baseline` and commit the diff.
`Interop` (the declared TCB) is excluded. The import-isolation gate enforces its boundary instead.

The baseline is an allowlist for `sorryAx` debt only.
Native trust (`native_decide`, which mints per-declaration `._native.` axioms) follows a zero-debt rule.
Anything outside the explicit `grandfatheredNativeTrust` list in `scripts/AxiomSweep.lean` fails `--check`.
An edit to the baseline cannot make it pass, because acceptance would widen the trusted computing base.
The `VCVioAxiomSweepTestFixtures` library carries synthetic taint for the tool's own
tests and is deliberately excluded from every aggregate.

`python3 ./scripts/check-comment-fences.py` checks tracked Lean sources and untracked Lean sources that are not ignored.
It excludes the vendored `third_party/` tree and includes both lakefiles.
The rule is positional: a block comment that begins its line must be the last thing on the line where it ends.
A declaration after the `-/` of its docstring parses, builds and runs.
A reader who scans the left margin does not see that declaration.

Two passes miss this shape for different reasons.
`lake lint -- --style-only` runs Mathlib's four text-based linters, none of which has any notion of a comment.
`linter.style.whitespace` is a separate syntax linter that runs during elaboration under the package's `weak.linter.mathlibStandardSet`.
Its warnings fail CI through the build log and `scripts/check-warning-log.py`.

The whitespace linter rejects a command that does not start at the beginning of a line.
It reports the `/-` and `/-!` forms of this shape but is silent on the `/--` form.
A doc comment is part of the command it documents, so the command starts at the `/--`, at column 0.
Thus the comment-fence gate is the only check that sees the doc-comment form anywhere.
For the other forms, it deliberately repeats the whitespace linter over the seven proof and three test libraries.

In four further places, this gate is the only check that can *fail* on any form of the shape, for three reasons.
Lake elaborates `lakefile.lean` and `VCVioComplexity/lakefile.lean` from `import Lake`, with no Mathlib linter registered.
`Interop/` is not a default target, and no job builds it.
Every pull request builds `scripts/`, but nothing there imports Mathlib.
Thus Lean silently drops the `weak.` option, and the linter is never registered there.
One Mathlib import in one axiom-sweep fixture would change that.

`VCVioComplexity/` explicitly sets `linter.style.whitespace` in its own lakefile, and the blocking `complexity_backend` job builds it.
The linter therefore runs and warns there.
The missing part is the gate: `check-warning-log.py` receives only the proof- and test-library prefixes.
Also, `VCVioComplexity/scripts/test.sh` pipes its log nowhere.

The rule leaves a block comment that opens part-way into a line untouched, however many lines it spans.
Such a comment annotates an expression, a field or a tactic block.
Wrapped field docstrings of that shape are common here.

The positional rule also rejects five shapes that hide nothing.
Four have a comment at column 0 before a term, a structure field, a tactic or a list element.
Lean lets each begin at column 0 when the enclosing command's indentation reaches column 0.
The fifth has a comment at column 0 whose line ends inside a second, still-open comment.
All five are clean Lean, and the fixture matrix asserts their rejection.

The gate does not cover a declaration indented on its own line.
The whitespace linter reports that shape in the built libraries, *unless* a margin docstring precedes it.
With that docstring, nothing reports the shape anywhere.
The gate also misses a comment that starts mid-line, two declarations on one line, and a declaration after a multi-line string's closing quote.
The last case hides a declaration with a different delimiter and could occur in `lakefile.lean`, which uses multi-line strings.

The baseline is zero, with no exception list.
`scripts/test-comment-fences.sh` carries the fixtures, including the shapes that the rule knowingly does not reach.

`./scripts/test-initsweep.sh` and `lake exe initsweep --check` are the companion
gate for what the *binary* does rather than what the kernel accepted. A top-level
constant of non-function type is evaluated when its module is loaded, before any
`main` runs, so

```lean
instance : Fintype limitedPrimitives.Y := inferInstanceAs (Fintype (Bytes 16))
```

builds a `Finset` of `2 ^ 128` vectors at start-up in every executable that imports the module.
It elaborates cleanly and passes the build, the linters, every boundary ratchet and the axiom sweep.

`lake exe initsweep --check` flags a constant when its module initializer evaluates a value that meets either of two conditions.
The value names an enumeration entry point listed in `scripts/InitSweep.lean`, or it names a *builder* of an enumeration class (`Fintype`, `FinEnum`).
The evaluated value can be the constant's own value, because the compiled declaration takes no parameters.
It can also come from an `initialize` body registered for that constant.

A builder is an instance constructor or an instance that takes arguments.
An already-materialized nullary instance such as `Bool.fintype` costs a pointer copy and is deliberately not counted.
The second disjunct makes the check a class test.
The instance that the elaborator would have found (`:= Pi.instFintype`) names none of the entry points but builds the same enumeration.

The sweep also walks compiler-generated declarations that the module initializer assigns beside its constants.
A parameterless *specialization* lifted out of a function is initialized at load and has no environment constant to read.
The sweep tests these declarations by what the functions in their mangled name consume.

If you mark the instance `noncomputable`, its own compiled code disappears, but the compiled auxiliary that carries the enumeration remains.
That auxiliary is the constant that the gate names, so this change does not fix the problem.
A parameter does not reliably fix it either.
`def cardY (_u : Unit) : Nat := Fintype.card T` still enumerates `T` at load, through the specialization that the compiler lifts out of it.
Route the finiteness argument through `Fintype.ofFinite` instead.
Its `Prop`-valued `Finite` argument leaves nothing compiled at all.

The baseline `scripts/init_sweep_baseline.json` lists accepted constant names with a scope, using the allowlist idea of `scripts/axiom_baseline.json`.
It is not a per-library ceiling.
Acceptance of one benign instance costs exactly that name and leaves every other constant of its library at zero.
The baseline holds nine rows.
`scripts/InitSweep.lean` lists what each row does at load, as read from the emitted C.
That list includes the two rows that are not initialized at all.

A row is scoped to one constant under one library.
The same name flagged under another root is still a regression, as is a new entry point for that name.
An additional row is the escape hatch and needs an argument in review.
`lake exe initsweep --update-baseline` writes the row and preserves the rows of libraries that the run did not sweep.

`VCVioInitSweepTestFixtures` carries seven hazard modules, one per route by which module loading can build an enumeration.
It also carries one negative control per clause of the predicate and the baseline's accept / drop / narrow / widen / re-scope / preserve behaviour.
Like the axiom-sweep fixtures, this library stays out of every aggregate.

The gate cannot see how *large* an enumeration is.
It does not inspect values whose size is an argument rather than a type (`List.range n`, `Array.replicate n x`).
`scripts/InitSweep.lean` lists those gaps and the occurrences of each in the current tree.

After adding new `.lean` files: `./scripts/update-lib.sh` (CI's `scripts/check-imports.sh`
fails when a regenerated umbrella would differ from the committed one).

The Lean toolchain and Mathlib must stay in sync (both `v4.35.0`).
The bump procedure is in `CONTRIBUTING.md`. Mathlib's file-length linter is enabled at 1500 lines.
Split files by responsibility before crossing that limit.
Retain an import façade when an existing module path forms part of the public API.

## Further Reading

Before working in a specific area, read the relevant guide in `docs/agents/`:

- **Interaction runtime and UC integration**: [`docs/agents/interaction.md`](docs/agents/interaction.md)
- **Interop with Rust verification frontends (hax, aeneas)**: [`docs/agents/interop.md`](docs/agents/interop.md)
- **LatticeCrypto layout and workflows**: [`docs/agents/lattice.md`](docs/agents/lattice.md)
- **OracleComp / SubSpec / SimSemantics**: [`docs/agents/oracle-comp.md`](docs/agents/oracle-comp.md)
- **Query tracking / weighted cost / expected runtime**: [`docs/agents/query-tracking.md`](docs/agents/query-tracking.md)
- **Honest computational-complexity design and implementation status**:
  [`docs/design/computational-complexity.md`](docs/design/computational-complexity.md)
- **SLH-DSA general-`d` formalization, FIPS 205 conformance, KAT, and security stack plan**:
  [`docs/design/slh-dsa-fips205-generalization.md`](docs/design/slh-dsa-fips205-generalization.md)
- **SLH-DSA implementation status, stale-plan corrections, and remaining slices**:
  [`docs/design/slh-dsa-status-and-roadmap.md`](docs/design/slh-dsa-status-and-roadmap.md)
- **SLH-DSA classical random-oracle bound, its accounting, and leanVM's 127-bit proof**:
  [`docs/design/slh-dsa-classical-rom-bound.md`](docs/design/slh-dsa-classical-rom-bound.md)
- **Probability reasoning (EvalDist, ProbComp)**: [`docs/agents/probability.md`](docs/agents/probability.md)
- **Converting code written against the removed discrete `Pr[…]` API**: [`docs/agents/probability-migration.md`](docs/agents/probability-migration.md)
- **Crypto primitives and reductions**: [`docs/agents/crypto.md`](docs/agents/crypto.md)
- **End-to-end crypto examples**: [`docs/agents/end-to-end-examples.md`](docs/agents/end-to-end-examples.md)
- **Program logic tactics**: [`docs/agents/program-logic.md`](docs/agents/program-logic.md)
- **All notation**: [`docs/agents/notation.md`](docs/agents/notation.md)
- **Proof workflows (game-hopping, reductions)**: [`docs/agents/proof-workflows.md`](docs/agents/proof-workflows.md)
- **Gotchas and troubleshooting**: [`docs/agents/gotchas.md`](docs/agents/gotchas.md)
- **Writing standard for all prose**: [`docs/agents/writing.md`](docs/agents/writing.md), with the
  [vocabulary](docs/agents/writing-vocabulary.md) and the
  [writing workflow](docs/agents/write-technical-prose.md)
- **Module visibility and the PolyFun façade**: [`docs/agents/module-system.md`](docs/agents/module-system.md)
- **Upstream alignment ledger (what Mathlib/core/cslib/PolyFun already own, with verdicts)**:
  [`docs/reading/upstream-alignment.md`](docs/reading/upstream-alignment.md)
