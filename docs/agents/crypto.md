# Crypto Primitives and Reductions

For the `LatticeCrypto/` directory layout, scheme entry points, and proof-vs-concrete split,
see [`docs/agents/lattice.md`](lattice.md).

## Crypto Primitive Structures

### Asymmetric encryption (`AsymmEncAlg`)

```lean
structure AsymmEncAlg (m : Type → Type u) [Monad m] (M PK SK C : Type) where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) → m C
  decrypt : (sk : SK) → (c : C) → m (Option M)
```

### Symmetric encryption (`SymmEncAlg`)

```lean
structure SymmEncAlg (m : Type → Type u) [Monad m] (M K C : Type) where
  keygen : m K
  encrypt : K → M → m C
  decrypt : K → C → m (Option M)
```

### Signatures (`SignatureAlg`)

```lean
structure SignatureAlg (m : Type → Type v) [Monad m] (M PK SK S : Type) where
  keygen : m (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : m S
  verify (pk : PK) (msg : M) (σ : S) : m Bool
```

`sigAlg.runWithSigningOracle pk sk oa` runs `oa : OracleComp (spec + (M →ₒ S)) α` with signing
queries answered under `sk` and `spec` queries passed through. It returns the output together
with the log of signed `(message, signature)` pairs. `MacAlg.runWithTaggingOracle` is the MAC
analogue.

For an end-to-end EUF-CMA reduction worked through the framework (Σ-protocol →
Fiat-Shamir transform → managed-RO NMA → replay forking → DLog), see
[`Examples/Schnorr/Signature.lean`](../../Examples/Schnorr/Signature.lean) and the
[Schnorr signature walkthrough](end-to-end-examples.md#schnorr-signature-euf-cma).
The Schnorr-specific σ-protocol facts that feed in live in
[`Examples/Schnorr/SigmaProtocol.lean`](../../Examples/Schnorr/SigmaProtocol.lean).

### Commitment schemes (`CommitmentScheme`)

```lean
structure CommitmentScheme (PP M C D : Type) where
  setup : ProbComp PP
  commit (pp : PP) (m : M) : ProbComp (C × D)
  verify (pp : PP) (m : M) (c : C) (d : D) : Bool
```

Defined in
[`VCVio/CryptoFoundations/CommitmentScheme.lean`](../../VCVio/CryptoFoundations/CommitmentScheme.lean)
together with `PerfectlyCorrect`, `PerfectlyHiding`, `hidingExp`,
`bindingExp`, and `extractExp`. The standard-model `binding ≤ keyed-CR ≤
birthday` bridge from a `KeyedHashFamily` lives in
[`VCVio/CryptoFoundations/HashCommitment.lean`](../../VCVio/CryptoFoundations/HashCommitment.lean)
as `bindingAdvantage_toCommitment_le_keyedCRAdvantage`.

For an end-to-end ROM proof of binding, extractability, and hiding for the
textbook `Commit(m) = (H(m, s), s)` scheme — exercising `cachingOracle`,
`loggingOracle`, the birthday bound, and identical-until-bad — see
[`Examples/CommitmentScheme.lean`](../../Examples/CommitmentScheme.lean)
and the
[ROM commitment scheme walkthrough](end-to-end-examples.md#rom-commitment-scheme).

### Sigma protocols (`SigmaProtocol`)

```lean
structure SigmaProtocol
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) : ProbComp Resp
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool
  sim (stmt : Stmt) : ProbComp Commit
  extract (chal₁ : Chal) (resp₁ : Resp) (chal₂ : Chal) (resp₂ : Resp) : ProbComp Wit
```

Every `SigmaProtocol` coerces to `IdenSchemeWithAbort` via `toIdenSchemeWithAbort` (wraps `respond` with `some`).

### Identification scheme with aborts (`IdenSchemeWithAbort`)

```lean
structure IdenSchemeWithAbort
    (Stmt Wit Commit PrvState Chal Resp : Type) (rel : Stmt → Wit → Bool) where
  commit (stmt : Stmt) (wit : Wit) : ProbComp (Commit × PrvState)
  respond (stmt : Stmt) (wit : Wit) (prvState : PrvState) (chal : Chal) :
    ProbComp (Option Resp)
  verify (stmt : Stmt) (commit : Commit) (chal : Chal) (resp : Resp) : Bool
```

The key difference from `SigmaProtocol` is that `respond` returns `Option Resp` (abort on `none`).
Used by ML-DSA and the Fiat-Shamir with Aborts transform.

### Key difference: monad-parametric algorithm surfaces

- `SymmEncAlg`, `AsymmEncAlg`, and `SignatureAlg` are plain structures over an abstract monad `m`.
- Instantiate them with `ProbComp`, `OracleComp spec`, `OptionT (OracleComp spec)`, or another monad at the security surface that needs those effects.
- Probability and failure semantics are supplied by the surrounding experiment or semantic class, not by parent classes on the algorithm structure.

### Instantiation pattern

```lean
@[simps!] def myAlg : AsymmEncAlg ProbComp M PK SK C where
  keygen := do ...
  encrypt pk msg := do ...
  decrypt sk c := do ...
```

## Security Experiments

### `BoundedAdversary`

```lean
structure BoundedAdversary {ι : Type u} [DecidableEq ι]
    (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0
```

### Advantage functions

Every advantage is `ℝ≥0∞`-valued. The advantage of a hidden-bit guessing game is the
`Measure.boolBias` of its measure, `absDiff (μ {true}) (μ {false})`, which for a total game is
twice the distance of the success probability from `1 / 2`
(`Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure`). The advantage of a
distinguisher between two worlds is the `Measure.boolDist` of their measures,
`absDiff (μ {true}) (ν {true})`. A search or forgery advantage is a success probability
`𝒟[exp] {true}`. `ENNReal.absDiff` is the extended distance on `ℝ≥0∞`, so no truncated subtraction
occurs; `Measure.toReal_boolDist` and `Measure.toReal_boolBias` give the absolute real difference
when a proof needs real arithmetic. A one-sided gap, such as the difference of two success
probabilities without absolute value, is a real-valued lemma rather than an advantage.

### Random oracle model

An experiment in the random oracle model is an `OracleComp (unifSpec + hashSpec)` computation.
Its handler is `hashSpec.romImpl` in `StateT hashSpec.QueryCache ProbComp`: uniform queries pass
through to `ProbComp`, and hash queries are answered by the lazily sampled random oracle
`hashSpec.randomOracle`, whose cache is the state. Its runtime is `ProbCompRuntime.rom hashSpec`,
which starts from the empty cache; `ProbCompRuntime.rom hashSpec cache` starts from `cache` and
so programs the oracle at the cached points. `romImpl` is reducibly
`unifFwdImpl hashSpec + hashSpec.randomOracle`, so the `roSim` lemmas, stated for
`unifFwdImpl hashSpec + ro` with a general hash handler `ro`, apply to it.

### KEM–DEM hybrid composition

`VCVio.CryptoFoundations.KEMDEM.Measure` defines the preparation, encapsulation, and final
observation games independently of probability. `KEMDEM.bias_compose_le` proves the
composition bound with native measures. Both KEM message branches use `evalDist_kemGame`;
`evalDist_demGame` performs independent-key interchange. Supply a fair coin, a lossless key
sampler, and total Boolean hybrid outputs explicitly. Preparation and encapsulation effects
retain their order. The `ProbCompRuntime` theorem in `KEMDEM.lean` is a compatibility adapter.

`ToMathlib.MeasureTheory.Measure.Bool` provides Boolean event distance and bias algebra.
`Measure.boolBias_bind_coin` requires total branches: missing mass is distinct from returning
`false`, so the assumption cannot be dropped.

### DEM real-or-random IND-CPA

`VCVio.CryptoFoundations.DataEncapMech.RealOrRandom` defines the one-time real-or-random game
`DEMScheme.realOrRandomGame`, which encrypts either the adversary's message or a uniform one.
Both DEM advantages are `boolBias` of a fair hidden-bit game, that is, the distance between the
two branches, so the constants carry no factor from the bias normalization.
`realOrRandomAdvantage_eq_IND_CPA_Advantage` is an exact equality with no runtime hypotheses.
`IND_CPA_Advantage_le_realOrRandomAdvantage_add` bounds the left-or-right advantage by the sum
of two real-or-random advantages and takes the runtime coherence hypotheses of the KEM–DEM
adapter.

### Forking bounds and measure semantics

`VCVio/CryptoFoundations/SeededFork.lean` and `ReplayFork.lean` prove the
seeded and context-fork success bounds through the established `Pr[...]`
surface. `ForkMeasure.lean` states the same final bounds as the Mathlib measure
of the `Option.isSome` event, using the canonical measure semantics induced by
the oracle specification's existing per-query probability interpretation.
These are transport corollaries; the forking arguments remain in the two
original modules.

The stateful Fiat–Shamir chain in `FiatShamir/Sigma/Stateful/Chain.lean` classifies each
logged handler step with the private `ForkStateStep` relation before proving invariants.
Its cache/log preservation lemmas use no sampling assumptions; both whole-run invariant
proofs reuse the same support-case normalization. Preserve the distinction between a fresh
oracle reply and a signing insertion: signing records the message and changes the adversary
cache, while a fresh oracle reply updates both caches and the live query log.

## Hardness Assumptions

### Discrete Log Assumptions (DLog / CDH / DDH)

Requires `[Field F] [Fintype F] [DecidableEq F] [SampleableType F]` and
`[AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]`
plus a fixed generator `g : G`.

Uses additive / EC-style notation: `a • g` means scalar multiplication (textbook `g^a`).

| Problem | Adversary type | Experiment |
|---------|---------------|------------|
| DLog | `DLogAdversary F G` (= `G → G → ProbComp F`) | `dlogExp g adversary` |
| CDH | `CDHAdversary F G` (= `G → G → G → ProbComp G`) | `cdhExp g adversary` |
| DDH | `DDHAdversary F G` (= `G → G → G → G → ProbComp Bool`) | `ddhExp g adversary` |

`CDHAdversary` and `DDHAdversary` carry a phantom `_F` parameter so Lean can infer the scalar field at call sites.

Defined in `VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`.

### Hard Relations

```lean
structure GenerableRelation (X W : Type) (r : X → W → Bool) where
  gen : ProbComp (X × W)
  gen_sound (x : X) (w : W) : (x, w) ∈ support gen → r x w
```

Note: the relation is `r : X → W → Bool` (not `Prop`). If a reduction needs
uniform marginal guarantees, state them as separate hypotheses or structure fields.

## Building a Reduction

A reduction proves: if adversary A breaks scheme S, then adversary B breaks assumption H.

### Blueprint

1. **Define the reduction adversary** that takes a challenge from H and embeds it into S:

```lean
def myReduction (adversary : ...) : DDHAdversary F G := fun g A B T => do
  -- embed DDH challenge (g, A = a•g, B = b•g, T) as scheme parameters
  let result ← adversary ...
  return result
```

2. **Prove the probability identity**: show that the reduction's advantage equals (or bounds) the scheme adversary's advantage.

3. **Key technique**: hybrid arguments for multi-query reductions.

### Name the reduction in the theorem statement

State a reduction theorem for a specific reduction, written as a definition of the source
adversary:

```lean
theorem signature_euf_cma ... :
    eps * (eps / (qH + 1) - challengeSpaceInv F) ≤
      Pr[= true | dlogExp g (dlogReduction F G g M adv qH)]
```

Do not quantify over the target adversary:

```lean
-- Do not write this.
theorem signature_euf_cma ... :
    ∃ reduction : DLogAdversary F G,
      eps * (eps / (qH + 1) - challengeSpaceInv F) ≤ Pr[= true | dlogExp g reduction]
```

The existential form holds for every source adversary, so it says nothing about the scheme.
The reasons are specific to how adversaries are represented here.

- **Adversary types carry no resource bound.** `DLogAdversary F G`, `X → ProbComp W`,
  `PRFScheme.PRFAdversary D R`, and `OracleComp spec α` contain every computation of that type,
  including exhaustive search. Against a computational assumption at concrete parameters, some
  such adversary has advantage `1` or close to it: search recovers a discrete log, an MLWE
  secret, or a PRF key.
- **Lean is classical.** A term may choose a witness with `Classical.choice`, so the unbounded
  adversary does not even need to search. For a `GenerableRelation`, `gen_sound` gives a
  witness for every statement in the support of `gen`, and the reduction
  `fun x => pure (if h : ∃ w, r x w then h.choose else default)` wins `hardRelationExp` with
  probability exactly `1`. Any bound of the form `∃ B, f ≤ Pr[= true | hardRelationExp hr B]`
  with `f ≤ 1` is then provable without looking at the scheme.
- **No existing check catches it.** The vacuous theorem is true, `sorry`-free, and depends only
  on the standard axioms, so `#print axioms` does not flag it. Checking that the hypotheses are
  satisfiable ([gotcha 14](gotchas.md#14-hypothesis-satisfiability-is-a-proof-obligation)) does
  not help either, because the defect is in the conclusion.

The same applies to every object that the security argument requires to be efficient or
independent of a secret:

- simulators: `∃ sim ζ_zk, 0 ≤ ζ_zk ∧ HVZK sim ζ_zk` holds with `ζ_zk := 1`, since
  `tvDist ≤ 1`;
- extractors, distinguishers, collision finders, and preimage finders.

Name each one with a definition (`cmaReduction`, `hvzkSimulatorReal`,
`unlinkToMultiplePRFReduction`) and state the bound for that definition.

A named reduction also makes the next steps possible. Its query count or cost can be proved as
a separate lemma about the same definition. The asymptotic lemmas in
[`VCVio/CryptoFoundations/Asymptotics/Security.lean`](../../VCVio/CryptoFoundations/Asymptotics/Security.lean),
such as `SecurityGame.secureAgainst_of_reduction`, take the reduction as a function
`reduce : Adv → Adv'` with an efficiency hypothesis `isPPT A → isPPT' (reduce A)`. That hypothesis
cannot be stated for an adversary that exists only inside an existential.

When the reduction is not implemented yet, do not fall back to `∃`. Either:

- define it as a `sorry` placeholder and state the bound for that definition, as
  `GPVHashAndSign.reduction` does; or
- leave the theorem as a placeholder whose docstring warns that the statement has no security
  content until a reduction is named, as `FiatShamirWithAbort.euf_cma_bound` does.

`∃` remains appropriate for mathematical objects that the argument does not need to be efficient,
such as a witness in a relation, an index in a support, or a key pair in the image of key
generation.

### Hybrid Argument Pattern

For a hand-written q-query IND-CPA → DDH hybrid proof:

1. Define `HybridGame adversary k`: first `k` queries use real encryption, rest use random
2. `HybridGame 0 = IND-CPA random`, `HybridGame q = IND-CPA real`
3. Per-step reduction: `stepDDHReduction adversary k` maps DDH challenge to hybrid k vs k+1
4. Telescope: `advantage ≤ q * max_per_step_advantage`

`Examples/ElGamal/Basic.lean` currently obtains its q-query bound by instantiating
the generic one-time IND-CPA lift in `VCVio/CryptoFoundations/AsymmEncAlg/INDCPA/GenericLift.lean`.

### Oracle Wiring for Stateful Reductions

Use `StateT` for reductions that need to track state (e.g., query counter, cache):

```lean
def myQueryImpl (challenge : ...) :
    QueryImpl spec (StateT MyState ProbComp) := fun t => do
  let st ← get
  -- branch on state to embed challenge
  ...
```

## Asymptotic Security

Defined in `VCVio/CryptoFoundations/Asymptotics/`.

### Negligible functions (`Negligible.lean`)

```lean
def negligible (f : ℕ → ℝ≥0∞) : Prop := SuperpolynomialDecay atTop (fun x ↦ ↑x) f
```

Closure properties: `negligible_add`, `negligible_const_mul`, `negligible_sum`,
`negligible_of_le`, `negligible_pow_mul`, `negligible_polynomial_mul`.

### `SecurityGame` (`Security.lean`)

`SecurityGame Adv` stores an advantage function rather than an experiment, so the same
meta-theorems apply to success, bias and distinguishing advantages. Build one by giving the
notion's advantage at each security parameter, converting an `ℝ`-valued advantage with
`ENNReal.ofReal`.

```lean
structure SecurityGame (Adv : Type*) where
  advantage : Adv → ℕ → ℝ≥0∞
```

- `SecurityGame.secureAgainst isPPT`: every adversary satisfying `isPPT` has negligible advantage.
- The predicate `isPPT` is abstract — specialize to `PolyQueries` or custom efficiency notions.

### Key reduction/game-hopping lemmas

| Lemma | Use |
|-------|-----|
| `secureAgainst_of_reduction` | Tight reduction: `adv(A) ≤ adv(reduce A)` |
| `secureAgainst_of_poly_reduction` | Polynomial-loss: `adv(A) ≤ p(n) · adv(reduce A)` |
| `secureAgainst_of_close` | Game hop: `adv_g₁(A) ≤ adv_g₂(A) + ε(n)` |
| `secureAgainst_of_hybrid` | Chain of `k` games differing by `ε` each |

## Cost Model

Defined in `VCVio/OracleComp/QueryTracking/CostModel.lean`. Uses `AddWriterT ω` for
additive cost accumulation through `simulateQ`.

```lean
structure CostModel (spec : OracleSpec ι) (ω : Type) [AddCommMonoid ω] where
  queryCost : spec.Domain → ω
```

| Definition | Purpose |
|------------|---------|
| `costDist oa cm` | Joint distribution `(output, totalCost)` |
| `expectedCost oa cm val` | `E[val(cost)]` via `wp` |
| `WorstCaseCostBound oa cm bound` | All paths have cost `≤ bound` |
| `ExpectedCostBound oa cm val bound` | Expected valued cost `≤ bound` |
| `WorstCasePolyTime family cm val` | Worst-case poly bound over security parameter |
| `ExpectedPolyTime family cm val` | Expected poly bound over security parameter |

Key results: `fst_map_costDist` (instrumentation is transparent),
`probEvent_cost_gt_le_expectedCost_div` (Markov's inequality),
`WorstCasePolyTime.toExpectedPolyTime`.

## Common Gotchas

1. **Avoid `guard`**: use `return (b == b')` or `return decide (r x w)` instead. `guard` requires `OptionT` / `Alternative`.

2. **`SymmEncAlg` vs `AsymmEncAlg`**: both are monad-parametric, but symmetric schemes carry a single key type while asymmetric schemes split public and secret keys. Pick the monad at the experiment boundary.

3. **DDH experiment uses `$ᵗ Bool`**: the experiment samples a bit `b`, returns real or random based on `b`, then checks `b == b'`.
