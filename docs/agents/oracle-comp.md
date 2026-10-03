# OracleComp, SubSpec, and SimSemantics

## OracleSpec

An oracle specification maps index types to response types:

```lean
def OracleSpec (ι : Type u) : Type _ := ι → Type v
```

Concretely, `spec t` is the response type at query index `t : ι`. `OracleSpec ι` is the
`B`-component of a polynomial functor with position type `A := ι`; `spec.toPFunctor` packages the
two together, and `OracleSpec.ofPFunctor` is its inverse (both `rfl`-invertible). This is the
connection that makes `OracleComp` a free monad: see [`OracleComp`](#oraclecomp) below.

`OracleSpec` is a parameterized family rather than a structure
alias for `PFunctor`: function application and the `Domain` / `Range` façade
give dependent oracle code useful expected types, while `toPFunctor` exposes
the generic algebra without a data conversion. In particular, `spec₁ + spec₂`
is definitionally the direction family of
`PFunctor.sum spec₁.toPFunctor spec₂.toPFunctor`. The PFunctor coproduct uses
the primitive dependent `Sum.rec`, and the OracleSpec `HAdd` instance is
left at its ordinary `instance_reducible` status. Ranges of nested `.inl` /
`.inr` queries therefore normalize during instance and implicit checking
without forcing the same unfolding during ordinary tactic matching.

When a handler only needs one side of a combined specification, prefer
`QueryImpl.restrictLeft` or `QueryImpl.restrictRight` to an annotated lambda.
The combinators preserve the component handler type explicitly and come with
application lemmas.

| Constructor | Notation | Example |
|-------------|----------|---------|
| Singleton spec | `A →ₒ B` | `Bool →ₒ Fin 6` |
| Empty spec | `[]ₒ` | No oracles |
| Combined specs | `spec₁ + spec₂` | `unifSpec + (M →ₒ C)` |

Required typeclass instances for probability reasoning:

- `[OracleSpec.AnswerMeasure spec]` selects the query measures;
  `[OracleSpec.UniformAnswerMeasure spec]` makes each of them uniform.
- Query answers carry the discrete σ-algebra, so answer types need no measurable-space instance,
  and discrete answer spaces discharge measurability of arbitrary free-program continuations.
- `𝒟[…]` needs a `MeasurableSpace` on the result type; `Pr{…}[…]` observes a `Prop` and needs
  none on intermediate results.

The support (the set of possible outputs), handler composition, instrumentation and query bounds
need no probability interpretation. Finite uniform queries are a sampling specialization, not a
requirement of the measure API.

## OracleComp

Computations with oracle access, defined as a free monad:

```lean
def OracleComp {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type w → Type _ :=
  PFunctor.FreeM spec.toPFunctor
```

### Key API

| Function | Purpose |
|----------|---------|
| `query t` | Issue an oracle query in the ambient monad (resolves to `HasQuery.query`) |
| `spec.query t` | Primitive single-query syntax (returns `OracleQuery spec (spec.Range t)`) |
| `OracleSpec.query t` | Same as `spec.query t` (the `protected` definition's full name) |
| `OracleComp.inductionOn` | Induction: `pure` case + `query_bind` case |
| `OracleComp.construct` | Same but result is `Type*` (not `Prop`) |
| `isPure` | Check if computation is `pure` (no queries) |
| `totalQueries` | Count total oracle queries |

### Checkpoint Placement and Replay

Ordinary program equality does not specify which random choices are shared across resumptions.
[`Examples/ReplayCheckpoint.lean`](../../Examples/ReplayCheckpoint.lean) gives a concrete
counterexample: moving a checkpoint across a fair Boolean draw preserves the program after
erasing the checkpoint, but changes the probability that two resumed outputs agree from `1`
to `1/2`. A replay-preservation argument must retain the checkpoint boundary and its shared state.
[`VCVioTest/ReplayCheckpoint.lean`](../../VCVioTest/ReplayCheckpoint.lean) checks the public
ordinary-execution equality and the distinguishing replay observation together.

### Possible outputs and `MonadAttach`

Use `OracleComp.reachableWhen possibleOutputs oa` when the oracles' answers are restricted: it is
the set of outputs of `oa` when each query `t` is answered only from `possibleOutputs t`. It is
PolyFun's `FreeM.reachableUnder`, the set view of PolyFun's angelic predicate transformer folded
over the free tree with each operation restricted to the allowed answers. The `pure`, query,
bind and monotonicity laws are `reachableWhen_pure`, `reachableWhen_query`, `reachableWhen_bind`
and `reachableWhen_mono`. Use `reachableWhen` rather than the deprecated `supportWhen`.

`support oa` admits every answer, and `reachableWhen_univ_eq_support` identifies it with
`reachableWhen` for the policy that allows every answer. `support` is PolyFun's
`MonadAttach.support`, which VCVio exports under that name. `MonadAttach.CanReturn` certifies
what a computation can return, and the additional `ExactMonadAttach` laws give the familiar
equations of the support for `pure` and bind. Neither fixes a policy for answering queries or an
initial state: for a state monad, reason with an execution indexed by the initial state or with
the handler's semantics, since the support of the flattened computation loses the relation
between initial and final states. The answer-indexed API lives in PolyFun because it is a
property of free programs, independent of VCVio's probability interpretation.

### Key lemmas

| Lemma | Use |
|-------|-----|
| `bind_eq_pure_iff` | `oa >>= ob = pure y ↔ ∃ x, oa = pure x ∧ ob x = pure y` |
| `pure_ne_query` | `pure x ≠ query t >>= f` |

### `query` resolution: `HasQuery.query` (monadic) vs `spec.query` (primitive)

The bare identifier `query` is the `export`ed `HasQuery.query`, so `query t : OracleComp spec _` (or
any `m` with `HasQuery spec m`) returns the result in the ambient monad and supports
`𝒟[(query t : OracleComp spec _)]` directly. Use `spec.query t` (or `OracleSpec.query t`) when you
need the primitive single-query syntax `OracleQuery spec _` for `liftM`, `OracleQuery.cont`,
structural induction, etc. The `OracleSpec.query` definition is `protected`; the dot-notation form
`spec.query t` works regardless.

### Elimination pattern

Prefer `OracleComp.inductionOn` over pattern matching on `PFunctor.FreeM.pure`/`roll`:

```lean
induction oa using OracleComp.inductionOn with
| pure x => ...
| query_bind t oa ih => ...
```

## SubSpec (⊂ₒ)

`spec ⊂ₒ superSpec` means every query in `spec` can be simulated in the larger specification without
changing the distribution.

```lean
class SubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  onQuery    : spec.Domain → superSpec.Domain
  onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t
  liftM_eq_lift :
    ∀ {β} (q : OracleQuery spec β),
      monadLift q = ⟨onQuery q.input, q.cont ∘ onResponse q.input⟩ := by intros; rfl
```

### Lens semantics

`onQuery` and `onResponse` together package a `PFunctor.Lens spec.toPFunctor superSpec.toPFunctor`
(call it `h.toLens`):

| Class field | Lens field |
|-------------|------------|
| `onQuery : spec.Domain → superSpec.Domain` | `toFunA : P.A → Q.A` |
| `onResponse t : superSpec.Range (onQuery t) → spec.Range t` | `toFunB t : Q.B (toFunA t) → P.B t` |

By the Yoneda lemma for polynomial functors this lens data is in bijection with natural
transformations `OracleQuery spec ⟹ OracleQuery superSpec`. The `MonadLift` parent records that
natural transformation; the `liftM_eq_lift` field is the propositional coherence axiom forcing it to
agree with the lens. Concrete `SubSpec` instances spell `monadLift` out *by hand* (rather than
letting it default from the lens data), so that the lifted query reduces fully under `isDefEq` —
this lets pattern-matching equations about lifted queries, such as `liftComp_query`, apply through
their registered automation or explicitly by name.

`SubSpec.toLens` exposes the underlying lens; `SubSpec.trans` is composition of these lenses; Lean's
reflexive `MonadLiftT` instance covers the identity.

#### Why `SubSpec` extends `MonadLift` rather than `PFunctor.Lens`

The fields *are* a lens. We extend `MonadLift` for two pragmatic reasons:

1. **Typeclass synthesis.** Lifting `OracleComp spec α → OracleComp superSpec α` is plumbed through
   the `MonadLift` / `MonadLiftT` mechanism; bridging through `PFunctor.Lens` separately would
   require an instance of the form `PFunctor.Lens A B → MonadLift (Obj A) (Obj B)`, which Lean
   cannot synthesize from `OracleQuery spec` because `OracleQuery` is a `def` (and `def`-headed
   instance heads cannot be matched).
2. **Reducibility under `rw` / `simp`.** A defaulted `monadLift` field becomes opaque to `isDefEq`
   during pattern matching. Hand-written `monadLift` per instance keeps the lifted query fully
   reducible.

### LawfulSubSpec ↔ cartesian lens

`LawfulSubSpec spec superSpec` (notation `spec ˡ⊂ₒ superSpec`) is a `Prop`-valued class over an
instance `[spec ⊂ₒ superSpec]` requiring that **every backward fiber `onResponse t` is a bijection**
(`onResponse_bijective`). This is *exactly* the `PFunctor.Lens.IsCartesian` predicate from
`PolyFun.PFunctor.Lens.Cartesian`:

```lean
def Lens.IsCartesian (l : Lens P Q) : Prop := ∀ a, Function.Bijective (l.toFunB a)
```

The bridge lemma `LawfulSubSpec.toLens_isCartesian` is the one-line statement that the underlying
lens of a `LawfulSubSpec` is cartesian.

A *cartesian* lens is a fiberwise isomorphism over an arbitrary forward map on positions. This is
**strictly weaker** than `PFunctor.Lens.Equiv` (an isomorphism in the lens category), which would
*also* require `onQuery` to be a bijection. We intentionally only require fiberwise bijectivity
because the basic `SubSpec` instances embed a small spec into a larger one (e.g.
`spec₁ ⊂ₒ (spec₁ + spec₂)` with `onQuery = Sum.inl`); these embeddings are essential and would be
ruled out by `Equiv`.

Cartesianness is the precise condition needed to push uniform measures through the lift:
`evalDistEq_liftM_query_uniform` shows that pulling the uniform measure on
`superSpec.Range (onQuery t)` back through `onResponse t` recovers the uniform measure on
`spec.Range t`. Preservation of arbitrary weighted answer measures is a separate contract: the class
`OracleSpec.SubSpec.PreservesAnswerMeasure` states it once for an inclusion, and
`evalDist_liftComp_of_evalDistEq` takes it per query.

### When you need SubSpec

When lifting `OracleComp spec α` to `OracleComp superSpec α` (e.g., a sub-computation uses fewer
oracles than the enclosing computation).

### Structural lemmas (require `[MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]`)

| Lemma | Signature |
|-------|-----------|
| `liftComp_pure` | `liftComp (pure x) superSpec = pure x` |
| `liftComp_bind` | `liftComp (mx >>= my) superSpec = liftComp mx superSpec >>= ...` |

### Measure lemmas (`VCVio/OracleComp/Coercions/SubSpec/Measure.lean`)

An inclusion whose translated queries are distributed as the originals is
`[OracleSpec.SubSpec.PreservesAnswerMeasure spec superSpec]`, a `Prop` class on top of
`[spec ⊂ₒ superSpec]` and an `AnswerMeasure` on each specification. Lawful inclusions between
uniform specifications (`[spec ˡ⊂ₒ superSpec]`, `[OracleSpec.UniformAnswerMeasure _]` on both)
and the two inclusions into a sum `spec₁ + spec₂` are instances. The program logic's
`Spec.liftComp` rules and `wp_liftComp` are stated on it, so a lift into a sum needs no uniform
answers.

| Lemma | Signature |
|-------|-----------|
| `evalDist_liftComp` | `𝒟[liftComp mx superSpec] = 𝒟[mx]` for a measure-preserving inclusion |
| `evalDistEq_liftComp` | `liftComp mx superSpec =ᵈ mx` for a measure-preserving inclusion |
| `evalDist_liftComp_uniform` | `𝒟[liftComp mx superSpec] = 𝒟[mx]` for a lawful inclusion between uniform specifications |
| `evalDistEq_liftComp_uniform` | `liftComp mx superSpec =ᵈ mx` for a lawful inclusion between uniform specifications |
| `evalDist_liftComp_of_evalDistEq` | `𝒟[liftComp mx superSpec] = 𝒟[mx]` for arbitrary `AnswerMeasure`s, given that each lifted query is `=ᵈ` the original |

## QueryImpl and simulateQ

### QueryImpl

`QueryImpl` maps each oracle input to a monadic response:

```lean
@[reducible] def QueryImpl (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)
```

This is definitionally `PFunctor.Handler m spec.toPFunctor`, recorded by
`QueryImpl.eq_handler`. The source definition retains the oracle-shaped
dependent function because it gives Lean better expected-type information for
polymorphic query code; the PolyFun theorem makes clear that the same object
can interpret any free program over the interface, not only oracle-specific
syntax.

Constructors:

| Constructor | Use |
|-------------|-----|
| `QueryImpl.id spec` | Identity (returns queries unchanged) |
| `QueryImpl.id' spec` | Identity lifted to `OracleComp` |
| `QueryImpl.ofLift spec m` | From `MonadLift` instance |
| `QueryImpl.ofFn f` | From pure function `f : (t : Domain) → Range t` |
| `impl.liftTarget n` | Lift impl from `m` to `n` via `MonadLiftT` |
| `spec.passthrough + impl` | Handle `spec'` with `impl`; pass `spec` queries through |

To simulate only some of a computation's oracles, `spec.passthrough + impl` handles `spec'` with
`impl` and answers each `spec` query by issuing the same query in `impl`'s target monad, which
must lift `OracleComp spec`. `spec.passthrough` is not itself a `QueryImpl`: rewrite with
`QueryImpl.passthrough_add` before applying `QueryImpl.add_apply_*` or `simulateQ_add_*`.

### simulateQ

Substitutes every `query t` in a computation with `impl t`:

```lean
def simulateQ [Monad r] (impl : QueryImpl spec r) (mx : OracleComp spec α) : r α
```

**Universal property.** `simulateQ impl` is the *unique* monad morphism `OracleComp spec →ᵐ r` that
agrees with `impl` on queries. Internally it is `PFunctor.FreeM.mapM impl`, i.e. the fold of the
free-monad syntax tree into `r`. Every way of "running" an `OracleComp` in another monad factors
through `simulateQ`.

**Handler vs denotation.** The target monad `r` determines how `simulateQ impl` reads:

- `r` effectful (`StateT`, `WriterT`, `OptionT`, another `OracleComp`, `IO`, …) — `simulateQ impl`
  is an **effect handler**: caching, logging, query counting, lazy sampling, simulating a hash
  oracle, embedding one game in a richer oracle context.
- `r` semantic (`SetM`, `Finset`) — `simulateQ impl` is a **denotation**; `support` agrees with the
  fold into `SetM` that admits every answer.

So "operational vs denotational" is not a primitive split for monad-valued interpretations: both are
`simulateQ` parameterized by the target monad. The measure semantics is the one exception, because
`Measure α` needs a `MeasurableSpace α` and is not a Lean monad (see [Output measures and
support](#output-measures-and-support) below).

### Key lemmas (all `@[simp, grind =]`)

| Lemma | Statement |
|-------|-----------|
| `simulateQ_pure` | `simulateQ impl (pure x) = pure x` |
| `simulateQ_bind` | `simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x)` |
| `simulateQ_query` | `simulateQ impl (liftM q) = q.cont <$> (impl q.input)` |
| `simulateQ_map` | `simulateQ impl (f <$> mx) = f <$> simulateQ impl mx` |
| `simulateQ_id'` | `simulateQ (QueryImpl.id' spec) mx = mx` |

### QueryImpl composition

```lean
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m

infixl : 65 " ∘ₛ " => QueryImpl.compose
```

Key lemma: `simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa)`

### Wrapping a QueryImpl with a per-query side effect (`preInsert` / `postInsert`)

**Prefer these combinators (or their downstream wrappers) over hand-rolling a new `QueryImpl`**
whenever the wrapper has the shape "for each query, run a side effect and then delegate to a base
implementation". They are defined in
`VCVio/OracleComp/SimSemantics/QueryImpl/Constructions/Core.lean`:

```lean
def preInsert  (so : QueryImpl spec m) (nx : spec.Domain → n α) :
    QueryImpl spec n
def postInsert (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α) :
    QueryImpl spec n
```

| | `preInsert` | `postInsert` |
|---|---|---|
| Side effect runs | **before** the handler | **after** the handler |
| Sees the response? | No | Yes (the response is passed to `nx`) |
| If the handler fails | Side effect still happens | Side effect skipped |

`QueryImpl.Constructions.Core` owns the induction principles
(`simulateQ_preInsert.induct` / `simulateQ_postInsert.induct`), projection equations
(`proj_simulateQ_preInsert`, `proj_simulateQ_postInsert`), and support/finite-support laws.
The projection equations transport output measures and events directly by equality. Query-bound
transfer lives in `QueryBound.lean`. Define instrumentation through these combinators, so that
the generic theory of supports and observations applies without wrapper-specific proofs.

#### Already in the repo (use these directly when applicable)

| Wrapper | File | Built on |
|---|---|---|
| `withTraceBefore` (response-independent monoid trace) | `QueryTracking/Tracing/Core.lean` | `preInsert` |
| `withTrace` (response-dependent monoid trace) | `QueryTracking/Tracing/Core.lean` | `postInsert` |
| `withTraceAppendBefore` / `withTraceAppend` (`Append`-flavoured) | `QueryTracking/Tracing/Core.lean` | `preInsert` / `postInsert` |
| `withCost`, `withCounting` | `QueryTracking/CountingOracle/Core.lean` | `withTraceBefore` |
| `withAddCost`, `withUnitCost` | `QueryTracking/WriterCost.lean` | `withCost` |
| `withLogging` | `QueryTracking/LoggingOracle/Core.lean` | `withTraceAppend` |
| `appendInputLog` (StateT input log) | `QueryTracking/LoggingOracle/Core.lean` | `preInsert` |

If a new wrapper looks like one of these, add it as a small specialization rather than starting from
`fun t => ...` from scratch.

#### When `preInsert` / `postInsert` is *not* the right shape

The combinators assume the underlying handler **always runs**. They are not the right tool when the
wrapper's control flow is conditional on external state or on the would-be response — for instance:

- **Cache-on-hit logic** (`withCaching` in `CachingOracle.lean`): a cache hit replaces the query
  body entirely.
- **Fallback-style seeding** (`withPregen` in `SeededOracle.lean`): consumes a pre-generated value
  when available, otherwise queries.
- **Budget gating** (`enforceOracle` in `Enforcement.lean`): if the budget is exhausted, returns
  `default` and skips the handler.
- **Game-state handlers** that branch on session state, gating flags, or bad-event flags.

These are genuinely custom and stay as hand-written `QueryImpl` definitions. If you find yourself
reaching for `preInsert` / `postInsert` and discovering that you need to inspect external state to
decide *whether* to query, you are in this category — write the impl directly.

### Output measures and support

For `OracleComp`, `support` is always available. It is the set of possible outputs, PolyFun's
`MonadAttach.support` on the free monad, and `PFunctor.FreeM.support_eq_liftM_univ` identifies it
with the fold into `SetM` that interprets each query by `Set.univ`.

`evalDist` / `𝒟[…]` is the successful-output Mathlib measure. Under
`[OracleSpec.AnswerMeasure spec]` it is definitionally the direct recursive measure fold
`PFunctor.FreeM.denote`, which composes the per-query answer measures with `Measure.bind`;
`PFunctor.FreeM.evalDist_eq_denote` records this (`𝒟[…]` stays the public head; the lemma is a
transport, not a simp rule). A lifted query denotes its answer measure (`evalDist_liftM_query`,
and `evalDist_liftM_query_uniform` for `uniformOn Set.univ` under `UniformAnswerMeasure`), and
`evalDist_apply_univ_eq_one` / `prEvent_true_eq_one` record that oracle computations are lossless.

Events `Pr{…}[…]` are expectations of indicators under the measure interpretation.
`prEvent_eq_evalDist`, `prEvent_eq_evalDist_of_discrete`, and `prEvent_eq_evalDist_singleton`
rewrite an event to the measure of a set as explicit steps. None of them is a default `simp` rule,
so `simp` keeps event goals in the normal form of nested expectations.

There is also a *syntactic* uniform-sampling handler that rewrites queries into `ProbComp` (i.e.
target `OracleComp unifSpec`):

```lean
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t
```

Preservation of the output measure through `uniformSampleImpl` is a **lemma**, not definitional:
`uniformSampleImpl.evalDist_simulateQ : 𝒟[simulateQ uniformSampleImpl oa] = 𝒟[oa]` under
`[OracleSpec.UniformAnswerMeasure spec]`, with `uniformSampleImpl.evalDistEq_simulateQ` for `=ᵈ`
(`VCVio/OracleComp/Constructions/SampleableType/Measure.lean`). The support companions
`uniformSampleImpl.support_simulateQ` and `uniformSampleImpl.finSupport_simulateQ` live in
`VCVio/OracleComp/Constructions/SampleableType/Basic.lean`. For an arbitrary handler,
`evalDist_simulateQ_eq_of_forall` preserves the output measure when each query's implementation
denotes its configured answer measure.

## Enforcement Oracle

Defined in `VCVio/OracleComp/QueryTracking/Enforcement.lean`. Wraps an oracle with a
per-index query budget tracked via `StateT`. Queries exceeding the budget return `default`.

```lean
def OracleSpec.enforceOracle [DecidableEq ι] [∀ t, Inhabited (spec.Range t)] :
    QueryImpl spec (StateT (ι → ℕ) (OracleComp spec))
```

Key result: `enforceOracle.fst_map_run_simulateQ` — if a computation satisfies
`IsPerIndexQueryBound oa qb`, then projecting the output of the enforced run with budget `qb`
recovers `oa` itself, as a program equality, so every output measure and event transfers.

Requires `[DecidableEq ι]` and `[∀ t, Inhabited (spec.Range t)]` (for `default` values).

## Patterns

### Wiring oracle implementations (stateful)

For stateful oracle simulations, use `StateT`:

```lean
def myImpl : QueryImpl spec (StateT MyState ProbComp) := fun t => do
  let st ← get
  -- process query using state
  set newState
  return response
```

Then run with `(simulateQ myImpl computation).run initialState`.
