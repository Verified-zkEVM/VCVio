# Program Logic Tactics and Relational Reasoning

## Current Module Boundary

- Import `VCVio.ProgramLogic.Tactics` for normal proof work. This is the canonical user-facing proof mode.
- The umbrella collects `VCVio.ProgramLogic.Tactics.PrVCGen` (`prvcgen`),
  `VCVio.ProgramLogic.Tactics.Unary` (`prrw`, `exp_norm`, `by_hoare`) and
  `VCVio.ProgramLogic.Tactics.Relational` (`rvcstep`, `rvcgen` and the proof-mode entries).
- `VCVio.ProgramLogic.Notation` provides the core notation and convenience predicates used by
  the tactic surface.

For continuous or otherwise non-discrete denotations, import
`VCVio.ProgramLogic.Relational.Measure`. Its `MeasureProgramLogic.RelWP` uses an almost-everywhere
postcondition under a Mathlib `Measure.Coupling`, and `eRelWP` integrates quantitative
post-expectations with `lintegral`. The `OracleComp` relational logic (`RelTriple`, `CouplingPost`,
`eRelWP`) specializes these to the output measures observed in the discrete structure on each
output type; its sequential rules need finite response types, and its anchoring and bijection
rules for queries need uniform response measures.

## In-Tree Walkthroughs

- `Examples/ProgramLogic/UnaryTriple.lean`: `prvcgen` on quantitative triples: binds, branches,
  loop invariants, and opaque sub-programs through `Spec.ofSupport`.
- `Examples/ProgramLogic/UnaryProbability.lean`: `prvcgen` on probability goals, `prrw`,
  `by_hoare`, and `exp_norm`.
- `Examples/ProgramLogic/Probability.lean`: `prrw` on program equalities.
- `Examples/ProgramLogic/UnaryStep.lean`: expectation equations with `expect_norm` /
  `expect_eval`, `prvcgen` on transformer triples, local `@[spec]` rules, and opaque sub-programs.
- `Examples/ProgramLogic/RelationalStep.lean`: step-by-step relational tactic examples.
- `Examples/ProgramLogic/RelationalDerived.lean`: derived relational patterns and automation examples.
- `Examples/ProgramLogic/ProofMode.lean`: proof-mode entry points and small end-to-end examples.
- `VCVio/ProgramLogic/Relational/Examples.lean`: compact API examples for the relational layer.
- `VCVioTest/ProgramLogic/PrVCGen.lean`, `VCVioTest/ProgramLogic/CoreVCGen.lean`,
  `VCVioTest/ProgramLogic/VCGenNames.lean`: every reading through `prvcgen`, every `@[spec]` rule
  and bridge under a bare `vcgen`, and the tactic names.

## Tactic Quick Reference

### Unary tactics

A statement about the outcomes of one program is a core triple, decomposed by core's `vcgen` with
`@[spec]` rules. An equality between the probabilities of two programs is a program equality, a
game hop. The unary tactics follow that split:

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `prvcgen` | `Pr{…}[p] = c`, `r ≤ Pr{…}[p]`, `Pr{…}[p] ≤ ε`, `0 < Pr{…}[p]`, `∀ x ∈ support oa, p x`, `∃ x ∈ support oa, p x` (also with `𝔼{…}[…]` or `wp⟦oa⟧ g`), or a core triple `⦃ pre ⦄ oa ⦃ post ⦄` | Runs core `vcgen` under the reading of `OracleComp` the goal belongs to (see *`prvcgen`*) |
| `vcgen` | a core triple, in the reading the file's scopes select | Core Lean's VC generator over the `@[spec]` catalogue (see *Core `vcgen` on oracle computations*) |
| `prrw`, `prrw under n`, `prrw congr`, `prrw congr'`, `prrw normalize` | `Pr{…}[…] = Pr{…}[…]`, `𝔼{…}[…] = 𝔼{…}[…]`, `𝒟[oa] {y} = 𝒟[ob] {y}`, `𝒟[oa] = 𝒟[ob]` | One program-equality step: a bind swap or a shared prefix (see *Program equalities*) |
| `simp only [expect_norm, expect_eval]` | `wp⟦oa⟧ g = …` for one program | States an expectation through the unfolding of the program and the values of its draws (see *Exact values*) |
| `exp_norm` | indicator / expectation arithmetic | Normalizes `propInd` and `wp` arithmetic |

`prvcgen` and `prrw` share no leading token with core's `vcgen`, so a bare `vcgen` is always
core's tactic (gotcha 35). The relational counterparts are `rvcstep` / `rvcgen` below.

### Postcondition bounds

For `wp⟦oa⟧ f ≤ wp⟦oa⟧ g`, `gcongr with x hx` exposes `hx : x ∈ support oa` and the
pointwise obligation `f x ≤ g x` (`wp_mono_of_support`). The unrestricted
`MeasureProgramLogic.wp_mono` remains available as a lower-priority fallback. Expectations are
core's `Std.WP.wp` under the measure interpretation, so the same rules apply to raw
`Std.WP.wp` expressions of that interpretation. An event after a common draw is an
expectation over that draw, so `gcongr` descends into `Pr{let x ← mx; …}[…]` as well.
`wp_eq_lintegral` integrates a measurable assertion in the chosen result space;
`wp_eq_lintegral_map` observes an arbitrary assertion without requiring a space on hidden results.

Use `finiteness` for `wp⟦oa⟧ post ≠ ⊤` when the result type is finite and the postcondition is
pointwise finite. An arbitrary quantitative postcondition may still take the value `⊤`.
The regression module `VCVioTest/ProgramLogic/GCongr.lean` checks the support binders and the
explicit raw-WP script, so these examples can be pasted into ordinary-import proofs.

For directional rewriting, explicitly import `Mathlib.Tactic.GRewrite`. With
`h : ∀ x, f x ≤ g x`, `grw [h]` rewrites through `wp` and expectation integrals `∫⁻ x, f x ∂𝒟[oa]`. If `h` is restricted
to `support oa`, the rewrite leaves that support premise as a side goal; `grw [h]; assumption`
closes the direct comparison. `gcongr with x hx` remains useful when the pointwise proof needs
the support fact explicitly. The [generalized-relation investigation](../reading/generalized-relation-automation.md)
compares these tactics with `mono`, equality congruence, and relational VCGen, and records which
candidate registrations are experimental.

### Proof Mode Entry

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `by_equiv` | `g₁ =ᵈ g₂` or `𝒟[g₁] = 𝒟[g₂]` | Enters relational proof mode (`RelTriple`) |
| `game_trans g₂` | `g₁ =ᵈ g₃` | Splits into `g₁ =ᵈ g₂` and `g₂ =ᵈ g₃` |
| `by_dist` | `AdvBound game ε` | Splits into a second game's bound and a `measureETVDist` bound |
| `by_upto bad` | identical-until-bad `measureETVDist` goals | Applies the `simulateQ` up-to-bad bound |
| `by_hoare` | `Pr{let x ← oa}[p x] = ...` | Enters quantitative WP reasoning, including conditional branches |

`by_equiv` enters the coupling-based `RelTriple` shell, so that `rvcstep` / `rvcgen` can keep
decomposing the relational goal.

`by_dist ε` is the explicit variant that fixes the TV-distance contribution to `ε`
before generating the remaining subgoals.

### Relational (pRHL) Tactics

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `rvcstep` | `g₁ =ᵈ g₂`, `𝒟[g₁] = 𝒟[g₂]`, `⟪oa ~ ob \| R⟫`, or `⦃f⦄ oa ≈ₑ ob ⦃g⦄` | Lowers into relational mode if needed, then applies one obvious relational step |
| `rvcstep using t` | same | Supplies the explicit witness needed by the current shape (bind cut relation, bijection, traversal input relation, or simulation state relation) |
| `rvcstep with thm` | same | Force one explicit relational theorem/assumption step |
| `rvcstep left` / `rvcstep right` | raw `VCVio.ProgramLogic.rwp` or folded `VCVio.ProgramLogic.RelTriple` goals | Exposes a controlled one-sided bind step |
| `rvcstep sym` | qualitative `RelTriple` goals | Swaps the two sides and the relational postcondition |
| `rvcstep upto R` | qualitative `RelTriple` goals | Changes the current postcondition to an explicit intermediate relation |
| `rvcstep trans mid` | qualitative `RelTriple` goals | Splits through an explicit intermediate computation using an `EqRel` transport side |
| `rvcstep swap left` / `rvcstep swap right` | qualitative `RelTriple` goals | Commutes two adjacent independent binds on one side through `EqRel` transport |
| `rvcstep swap left using R` / `rvcstep swap right using R` | qualitative `RelTriple` goals | Commutes the binds, then immediately decomposes the aligned residual bind using cut relation `R` |
| `rvcstep?` | same | Performs one relational step and emits a `Try this` script, usually surfacing a needed `using` hint, `with theorem`, or `as ⟨...⟩` clause |
| `rvcgen` | same | Repeats relational VCGen across all current goals until stuck |
| `rvcgen using t` | same | Uses `t` for the first step on the main goal, then continues with ordinary `rvcgen` |
| `rvcgen using [t₁, t₂, ...]` | same | Applies explicit cut hints in sequence, introducing and substituting EqRel continuation equalities between cuts |
| `rvcgen with thm` | same | Uses `thm` for the first step on the main goal, then continues with ordinary `rvcgen` |
| `rvcfinish` | residual relational VCs | Runs the opt-in consequence/search finishing pass |
| `rvcgen!` | same | Runs `rvcgen`, then `rvcfinish` |
| `rvcgen?` | same | Runs `rvcgen` and emits the corresponding explicit script |
| `rel_conseq` | `⟪oa ~ ob \| R'⟫` | Weakens/strengthens postcondition |
| `rel_inline foo` | `⟪... ~ ... \| R⟫` | Unfolds definitions, simplifies |
| `rel_dist` | `⟪oa ~ ob \| EqRel α⟫` | Exits relational mode back to `𝒟[oa] = 𝒟[ob]` in the discrete structure |

### Relational optional arguments

- `rvcstep using R` — on bind goals, provide the intermediate relation explicitly
- `rvcstep using f` — on random/query goals, provide the coupling bijection explicitly.
  On a synchronized bind goal whose left/right scrutinees are uniform samples or queries,
  the same `using f` form is also accepted as a *bijection-coupling bind*: it cuts with
  `R := fun a b => b = f a`, closes the sample subgoal via
  `relTriple_uniformSample_bij` (or `relTriple_query_bij`), and substitutes the equality
  on the continuation, leaving the user with the continuation goal followed by the
  `Function.Bijective f` side condition
- `rvcstep using Rin` — on `List.mapM` / `List.foldlM` goals, provide the input relation
- `rvcstep using R_state` — on `simulateQ` goals, provide the state invariant relation
- `rvcstep with thm` — force one explicit registered/local relational theorem
- `rvcstep as ⟨x₁, x₂, h⟩` — explicitly name the binders introduced by the current step
- `rvcgen using t` / `rvcgen with thm` — use one explicit first hint/theorem, then keep stepping automatically
- `rel_conseq with R` — provide explicit weaker postcondition

### Relational automation

| Tactic | What it does |
|--------|--------------|
| `rvcgen` | Exhaustive relational VCGen over all open goals, with automatic lowering from `=ᵈ` / output-measure equality and cheap leaf closure |
| `rvcfinish` / `rvcgen!` | Opt-in residual search and consequence closing |
| `rel_dist` | Turns `RelTriple oa ob (EqRel α)` into `oa =ᵈ ob` |

**Registered rules**: mark a relational `RelTriple`, `RelWP`, or quantitative
`VCVio.ProgramLogic.RelTriple` theorem with `@[vcspec]` to register it for bounded head-pair
lookup (see *Internal Architecture* below). This is especially useful for automation-oriented
`simulateQ` transport lemmas whose outer computation heads are stable but whose inner invariants or
projection arguments still come from the local context. Registered rules are tiered internally:
plain `rvcstep` / `rvcgen` use default-safe structural and leaf entries, while rules that choose
cuts, bijections, or broad theorem search are reached through `rvcstep with thm`,
`rvcstep using t`, `rvcfinish`, or `rvcgen!`. This keeps ordinary rule ordering stable when new
`@[vcspec]` lemmas are added. A triple of one program is a core `@[spec]` rule, and `@[vcspec]`
rejects it.

**Naming and suggestions**: plain `rvcstep` keeps the stable execution path. `rvcstep?` and
`rvcgen?` run a planner-backed version of the same move and emit a concrete `Try this` script,
typically surfacing an explicit `using ...` hint, `with theorem`, or `as ⟨...⟩` clause that you can
paste back into the proof.

**Bind normalization**: `rvcstep` (and therefore `rvcgen`) runs a best-effort
`simp only [bind_assoc, pure_bind, bind_pure_comp, Functor.map_map, map_pure]` pre-pass on the
relational goal before deciding which structural rule to apply. This flattens nested binds and
strips pure-bind layers so that the bind decomposition rule fires on aligned shapes, and so that
goals that simplify to pure-pure or refl close immediately.

**Augmented leaf closure**: the relational leaf closer (`tryCloseRelGoalImmediate`, plus the
cheap leaf finish at the end of `rvcgen`) tries, in order:
1. `assumption`
2. `relTriple_true _ _` (the postcondition is structurally `fun _ _ => True`, discharged via
   the universal product coupling, since `OracleComp` has no failure mass);
3. `relTriple_post_const ?_; intros; trivial` (the postcondition reduces to a trivially provable
   proposition such as `() = ()` after introduction);
4. `relTriple_refl` / `relTriple_eqRel_of_eq rfl` / `relTriple_pure_pure` /
   quantitative `VCVio.ProgramLogic.RelTriple` pure (canonical reflexive and pure-pure leaves);
5. a `subst_vars`-driven retry of the same closers (resolves syntactically-distinct pure
   values unified by local equality hypotheses);
6. a symmetric `relTriple_pure_pure ∘ symm` step for postconditions written in the swapped
   direction.

Consequence/search closing is opt-in through `rvcfinish` or `rvcgen!`; plain
`rvcgen` keeps to structural steps plus cheap leaf closure so rule-order changes
stay predictable.

**Explicit relational strategies**: `rvcstep sym`, `rvcstep upto R`,
`rvcstep trans mid`, and `rvcstep swap left/right` are strategy commands, not
default automation.
The initial `trans` support is the equality-transport shape: it splits
`⟪oa ~ ob | R⟫` into either `⟪oa ~ mid | EqRel _⟫` / `⟪mid ~ ob | R⟫`
or the dual `⟪oa ~ mid | R⟫` / `⟪mid ~ ob | EqRel _⟫`.
The `swap` variants use that EqRel transport shape with the independent-bind
commutativity lemma, then leave the aligned relational goal. The `using R`
variants immediately take the next aligned bind step with cut relation `R`.
Do not emulate stronger coupling transitivity with broad theorem search until
the full semantic gluing lemma and goal shape are added.

**Pass budget**: exhaustive `rvcgen` runs are bounded by
`set_option vcvio.vcgen.maxPasses <n>`. The default is conservative so large proofs stay
predictable; if you intentionally want a longer exhaustive run, raise the option locally around
that proof.

**Trace output**: set `set_option vcvio.vcgen.traceSteps true` to log the chosen planned step,
goal delta, and any planner alternatives that were previewed while debugging tactic choice.
`vcvio.vcgen.time` reports the time spent in the planner phases, including the search of
`prrw normalize`, and `vcvio.vcgen.traceCachedRules` traces hits and misses in the cache of
backward rules built from `@[vcspec]` entries.

### Handler Normalization

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `handler_step` | handler-heavy `FreeM` / `QueryImpl` / `simulateQ` / transformer goals | Runs one `simp only [handler_nf, handler_simp]` normalization pass to expose the next handler body or run-shape |

`handler_step` is deliberately thin. Use it when a proof is stuck behind
handler combinators such as cache overlays, logging handlers, counting
handlers, or state-transformer maps; then continue with `prvcgen`, `rvcstep`,
`rvcgen`, or direct proof steps.

PolyFun owns the generic `handler_nf` rules for `FreeM`,
`PFunctor.Handler.Stateful`, `StateT`, and standard `WriterT`. VCVio's
`handler_simp` set adds only oracle simulation, query instrumentation,
caching, and local WriterT compatibility equations. Downstream code can use
the two sets independently; `handler_step` composes them in generic-to-specific
order.

## Core `vcgen` on oracle computations

Core's `vcgen` decomposes a core triple
`⦃ pre ⦄ oa ⦃ post ⦄` with the `@[spec]` rules registered for the program's parts and leaves
verification conditions in the assertion lattice. `OracleComp spec` has four readings, one per
kind of statement about its outcomes:

| Reading | Scope | Carrier | `⦃ pre ⦄ oa ⦃ post ⦄` states | Rules |
|---------|-------|---------|-------------------------------|-------|
| structural (necessary) | global instance (`OracleComp.Qualitative`) | `Prop` | every possible output satisfies `post` | `Unary/WP/QualitativeSpecs.lean` |
| angelic (possible) | `OracleComp.Angelic` | `Prop` | some possible output satisfies `post` | `Unary/WP/Angelic.lean` |
| expectation lower bound | `OracleComp.Quantitative` | `ℝ≥0∞` | `pre ≤ wp⟦oa⟧ post` | `Unary/WP/QuantitativeSpecs.lean` |
| expectation upper bound | `OracleComp.Upper` | `ℝ≥0∞ᵒᵈ` | `wp⟦oa⟧ post ≤ pre` | `Unary/WP/Upper.lean` |

The upper-bound reading is PolyFun's `ExactWPMonad.dual` of the expectation reading: the same
interpretation over the order duals, so core's `vcgen`, transformer rules and loop invariants
decompose upper bounds unchanged. The structural reading is the global instance, as core's own
`Prop`-valued instances are for its monads: it needs no probability interpretation, and a bare
triple says that every possible output satisfies the postcondition. Core's assertion types are
output parameters, so one reading is live per program type in a scope: under an expectation scope,
a triple with a `Prop` precondition no longer elaborates, and a triple of one reading cannot be
decomposed with another reading's scope open. Each scoped reading registers its `WPMonad` and a
direct `WP` instance at priority `1100`, and each reading also registers a per-call scope at
priority `1200` (`OracleComp.Qualitative.Dispatch`, `OracleComp.Angelic.Dispatch`,
`OracleComp.Quantitative.Dispatch`, `OracleComp.Upper.Dispatch`), above every reading a file
opens (gotcha 33): `open scoped OracleComp.Upper.Dispatch in vcgen` runs `vcgen` in that reading
whatever the file opens. `Pr{…}[…]`, `𝔼{…}[…]` and `wp⟦oa⟧ g` name the expectation interpretation
explicitly and are unaffected by the scopes. `prvcgen` (below) chooses the reading from the goal.

Triple notation comes from `open scoped Std.WP`. In the expectation reading, `Std.WP.Triple.iff`
unfolds `⦃ pre ⦄ oa ⦃ post ⦄` to `pre ⊑ wp oa post ⊥`, which is `pre ≤ wp⟦oa⟧ post`
(`le_wp_iff_triple`). Core supplies the generic rules (`Std.WP.Triple.intro`, `.le_wp`,
`Std.WP.Spec.pure`, `Std.WP.Triple.bind`, `Std.WP.Triple.entails_wp_of_pre_post`), steps through
binds, `if`, `match` and transformer stacks, and applies triples of sub-programs found among the
hypotheses. `VCVio/ProgramLogic/Unary/HoareTriple.lean` states the quantitative rules that are
passed explicitly: `triple_zero`, the loop unrolling rules (`triple_replicate_succ`,
`triple_list_mapM_cons`, `triple_list_foldlM_cons`), the loop invariant rules
(`triple_replicate_inv`, `triple_replicate`, `triple_list_mapM_inv`, `triple_list_mapM`,
`triple_list_foldlM_inv`, `triple_list_foldlM`), and the event triples
`triple_prEvent_indicator`, `triple_prEvent_eq_one` and `triple_support`. The equations of an
expectation are the generic `MeasureProgramLogic.wp_pure` / `wp_bind` / `wp_map` / `wp_add` /
`wp_const_mul` and PolyFun's `ExactWPMonad.wp_ite` / `wp_dite`; a constant observation of an
oracle computation is `MeasureProgramLogic.wp_const_of_oracle`.

Structural rules (`VCVio/ProgramLogic/Unary/WP/QualitativeSpecs.lean`, namespace
`OracleComp.Qualitative`):

| Program | Rule | Precondition |
|---------|------|--------------|
| `query t` (both spellings) | `Spec.query`, `Spec.monadLift_query` (in `Unary/WP/Qualitative.lean`) | `∀ u, post u` |
| `$ᵗ β` | `Spec.uniformSample` | `∀ x, post x` |
| `$[0..n]` | `Spec.uniformFin` | `∀ i, post i` |
| `oa.replicate n` | `Spec.replicate` | `∀ xs, xs.length = n → (∀ x ∈ xs, x ∈ support oa) → post xs` |
| `liftComp oa superSpec` | `Spec.liftComp` | `wp oa post epost` (continues into `oa`) |
| any `oa` (not registered) | `Spec.ofSupport` | `∀ a ∈ support oa, post a` |

Quantitative rules (`VCVio/ProgramLogic/Unary/WP/QuantitativeSpecs.lean`, namespace
`OracleComp.Quantitative`) state that a lower bound holding for every outcome holds in expectation,
with `Lean.Order.iInf`, which `vcgen` splits into one condition per outcome:

| Program | Rule | Precondition |
|---------|------|--------------|
| `query t` (both spellings) | `Spec.query`, `Spec.monadLift_query` | `⨅ u, post u` |
| `$ᵗ β` | `Spec.uniformSample` | `⨅ x, post x` |
| any `oa` (not registered) | `Spec.ofSupport` | `⨅ a : {a // a ∈ support oa}, post a.1` |
| `$ᵗ β`, finite (not registered) | `Spec.uniformSample_sum` | `(∑ x, post x) / card β` |
| `query t`, uniform (not registered) | `Spec.query_uniform` | `∑ u, (card)⁻¹ * post u` |

`OracleComp.ProgramLogic.triple_const_mul c h` scales a lower-bound triple. Passing it for an
adversary's success bound composes that bound with a later draw, as in
`vcgen [triple_const_mul 2⁻¹ hadv, Spec.uniformSample_sum]`. A hypothesis
`h : ∀ k ∈ support gen, ⦃ r ⦄ f k ⦃ post ⦄` is used by `vcgen [Spec.ofSupport gen]`, which leaves
the support side condition. The quantitative verification conditions are `ℝ≥0∞` inequalities.
`simp` reads core's order as `≤` (PolyFun's `Lean.Order.rel_eq_le`) and `1 ≤ propInd P` as `P`
(`one_le_propInd_iff`).

Bridges:

| Statement | Triple | Lemma |
|-----------|--------|-------|
| `Pr{let x ← mx}[p x] = 1` (uniform answers) | `⦃ True ⦄ mx ⦃ p ⦄` (structural) | `OracleComp.Qualitative.prEvent_eq_one_iff_triple` |
| `𝒟[mx] {true} = 1` (uniform answers; `PerfectlyCorrect`, `PerfectlyComplete`) | `⦃ True ⦄ mx ⦃ (· = true) ⦄` | `evalDist_true_eq_one_iff_triple` |
| `Pr{let x ← mx}[p x] = 0` (uniform answers) | `⦃ True ⦄ mx ⦃ fun x => ¬ p x ⦄` | `prEvent_eq_zero_iff_triple` |
| `Pr{let x ← mx}[p x] = 1` (any answer measures, one direction) | from `⦃ True ⦄ mx ⦃ p ⦄` | `prEvent_eq_one_of_triple` |
| `r ≤ Pr{let x ← oa}[p x]` | `⦃ r ⦄ oa ⦃ predInd p ⦄` (quantitative) | `OracleComp.ProgramLogic.le_prEvent_iff_triple` |
| `r ≤ wp⟦oa⟧ g` | `⦃ r ⦄ oa ⦃ g ⦄` | `le_wp_iff_triple` |

The structural bridges are in `VCVio/ProgramLogic/Unary/WP/Coherence.lean`. For a query with
uniform answers, `simp` averages the expectation in an event's normal form with
`OracleComp.wp_monadLift_query_uniform`.

Angelic rules (`VCVio/ProgramLogic/Unary/WP/Angelic.lean`, namespace `OracleComp.Angelic`) state
that a query or draw can return any value, with precondition `∃ u, post u`:
`Spec.query`, `Spec.monadLift_query`, `Spec.uniformSample`, `Spec.uniformFin`, and `Spec.ofSupport`
(not registered). `vcgen` does not split an existential, so each draw leaves
`∃ u, wp (rest u) post ⊥`; name the witness with `refine ⟨w, ?_⟩` and continue with `prvcgen`
(or `rw [OracleComp.Angelic.wp_iff_triple]` and `vcgen` in the angelic scope). The angelic reading
is not conjunctive.

Upper-bound rules (`VCVio/ProgramLogic/Unary/WP/Upper.lean`, namespace `OracleComp.Upper`):

| Program | Rule | Precondition (read in `ℝ≥0∞`) |
|---------|------|------|
| `query t` (both spellings) | `Spec.query`, `Spec.monadLift_query` | `⨆ u, post u` (core's `Lean.Order.iInf` of the dual) |
| `$ᵗ β`, `$[0..n]` | `Spec.uniformSample`, `Spec.uniformFin` | `⨆ x, post x` |
| any `oa` (not registered) | `Spec.ofSupport` | `⨆ a : {a // a ∈ support oa}, post a.1` |
| `$ᵗ β`, finite (not registered) | `Spec.uniformSample_avg` | `(∑ x, post x) / card β` |
| `query t`, uniform (not registered) | `Spec.query_avg`, `Spec.monadLift_query_avg` | `∑ u, (card)⁻¹ * post u` |

`triple_add_frame c h` adds a constant budget to an upper-bound triple and `triple_const_mul`
scales one. The registered rules bound a draw by its largest value: they prove events of
probability zero and bounds that hold on every path. A bound that averages a draw passes the
averaging rule explicitly. A bound that accumulates over steps, such as a union bound over an
adversary's queries, is a potential: the bad event's indicator plus the budget of the remaining
steps, carried by a loop invariant (`Spec.foldlM_list`) or by a ranked handler invariant
(`OracleComp.ProgramLogic.simulateQ_triple_ranked`, which spends one unit of budget per query of a
computation with `IsTotalQueryBound`). `vcgen` then leaves one averaging inequality per step and an
entry condition comparing the initial budget with the bound.

An assertion of the upper-bound reading has type `ℝ≥0∞ᵒᵈ`. Write the precondition as `toDual ε`:
the triple notation elaborates its precondition before it looks up the interpretation, so an
`ℝ≥0∞` precondition selects the carrier `ℝ≥0∞`. Bridges:

| Statement | Triple (upper-bound reading) | Lemma |
|-----------|------------------------------|-------|
| `wp⟦oa⟧ g ≤ ε` | `⦃ toDual ε ⦄ oa ⦃ fun a => toDual (g a) ⦄` | `OracleComp.Upper.wp_le_iff_triple` |
| `Pr{let x ← oa}[p x] ≤ ε` | `⦃ toDual ε ⦄ oa ⦃ fun x => toDual (predInd p x) ⦄` | `OracleComp.Upper.prEvent_le_iff_triple` |
| nested expectations | `toDual (wp⟦oa⟧ g) = wp oa (fun a => toDual (g a)) ⊥` | `OracleComp.Upper.toDual_wp` |
| `0 < Pr{let x ← oa}[p x]` (uniform answers) | `⦃ True ⦄ oa ⦃ p ⦄` (angelic) | `OracleComp.Angelic.prEvent_pos_iff_triple` |
| `∃ x ∈ support oa, p x` | `⦃ True ⦄ oa ⦃ p ⦄` (angelic) | `OracleComp.Angelic.exists_mem_support_iff_triple` |
| `∀ x ∈ support oa, p x` | `⦃ True ⦄ oa ⦃ p ⦄` (structural) | `OracleComp.Qualitative.forall_mem_support_iff_triple` |
| `wp⟦oa⟧ g = 1`, `g ≤ 1` (uniform answers) | `wp oa (fun a => g a = 1) ⊥` (structural) | `OracleComp.Qualitative.wp_eq_one_eq_wp` |
| `0 < wp⟦oa⟧ g` (uniform answers) | `wp oa (fun a => 0 < g a) ⊥` (angelic) | `OracleComp.Angelic.pos_wp_eq_wp` |

The positivity and probability-one bridges need answers of positive mass; the `_of_fullSupport`
forms (`OracleComp.Angelic.pos_wp_iff_of_fullSupport`,
`OracleComp.Qualitative.wp_eq_one_iff_of_fullSupport`) take that hypothesis in place of uniform
answers.

The verification conditions of the upper-bound reading are entailments of `ℝ≥0∞ᵒᵈ`. Read them in
`ℝ≥0∞` with `simp only [OracleComp.Upper.rel_iff, OrderDual.ofDual_toDual,
OracleComp.Upper.ofDual_wp, ofDual_add, …]` before any other simplification: the default `simp`
set distributes `toDual` over arithmetic before it compares the sides, and a term elaborated in
`ℝ≥0∞` but placed in `ℝ≥0∞ᵒᵈ` (a type ascription) is matched against the wrong carrier.

### `prvcgen`

`prvcgen` (`VCVio.ProgramLogic.Tactics.PrVCGen`, in the `VCVio.ProgramLogic.Tactics` umbrella)
classifies a statement about the outcomes of one oracle computation, rewrites it with the bridge
of its reading, and runs core `vcgen` in that reading's per-call scope, with
`experimental.vcgen` set:

| Goal | Reading |
|------|---------|
| `Pr{…}[p] = 1` (uniform answers), `∀ x ∈ support oa, p x` | structural |
| `0 < Pr{…}[p]` (uniform answers), `∃ x ∈ support oa, p x` | angelic |
| `r ≤ Pr{…}[p]`, `Pr{…}[p] ≥ r` | expectation lower bound |
| `Pr{…}[p] ≤ ε`, `Pr{…}[p] = 0` | expectation upper bound |
| `Pr{…}[p] = c` | both bounds, by `le_antisymm` |
| `⦃ pre ⦄ oa ⦃ post ⦄`, or its unfolded form `pre ⊑ wp oa post epost` | the reading of its assertion type |
| an angelic or structural `wp oa post ⊥` | continued in its reading |

`𝔼{…}[g]` and `wp⟦oa⟧ g` stand wherever `Pr{…}[p]` does, and an equation may have the expectation
on either side. A triple is run in the reading of its assertion type: `ℝ≥0∞` for lower bounds,
`ℝ≥0∞ᵒᵈ` for upper bounds, and `Prop` for the structural reading, or the angelic one when the
triple's interpretation is angelic. A state-passing assertion `σ → …` is read by its codomain, so
triples over `StateT`, `ReaderT`, `WriterT`, `OptionT` and `ExceptT` stacks on `OracleComp spec`,
the handler specifications among them, run the same way. A comparison `Pr{A}[p] ≤ Pr{B}[q]` is
read as an upper bound on the left-hand side with the right-hand side as the bound.

Syntax: `prvcgen (config)? [rules]? (invariants · …)? (with step)? (=> tac)?`. The configuration,
rules, invariant alternatives and `with` step go to `vcgen`; `prvcgen => tac` runs `tac` in the
reading's scope in place of `vcgen`, with `vcgen`'s arguments written inside `tac`. The goal's
metavariables are instantiated first, since `vcgen` matches programs syntactically.

**Rules and hypotheses.** `vcgen` uses the `@[spec]` rules registered for the program's parts, the
rules in brackets, and the triples of sub-programs among the hypotheses, each rule in the reading
its triple is stated in. A program opaque to `vcgen`, such as an `@[irreducible]` definition, takes
a triple tagged `@[spec]` or `@[local spec]`, or one passed for a single call as
`prvcgen [rule]`. A hypothesis about an event is used once it is stated as a triple:
`triple_prEvent_eq_one` turns `Pr{let x ← oa}[p x] = 1` into
`⦃ 1 ⦄ oa ⦃ fun x => if p x then 1 else 0 ⦄`, and `le_prEvent_iff_triple` / `le_wp_iff_triple`
turn lower bounds into triples.

**Opaque sub-programs.** `Spec.ofSupport oa`, in each reading's namespace
(`OracleComp.Quantitative.Spec.ofSupport`, `OracleComp.Upper.Spec.ofSupport`,
`OracleComp.Qualitative.Spec.ofSupport`, `OracleComp.Angelic.Spec.ofSupport`), bounds `oa` by its
continuation's precondition over its support. With `h : ∀ x ∈ support oa, ⦃ r ⦄ f x ⦃ post ⦄`,
`prvcgen [OracleComp.Quantitative.Spec.ofSupport oa, h]` proves `⦃ r ⦄ (oa >>= f) ⦃ post ⦄` up to
the support membership, which it leaves. With `prvcgen (errorOnMissingSpec := false)`, a program
without a rule is left as a verification condition stating its weakest precondition,
`pre ≤ wp oa k`, whose continuation `k` holds the rest of the program;
`simp only [expect_norm, le_refl]` closes it when `pre` is that expectation.

**Loops.** A loop takes an invariant: `List.foldlM` through core's rule, as
`prvcgen invariants · fun _ _ s => I s`, and `replicate` and `List.mapM` through the rules of
`Unary/HoareTriple.lean` passed explicitly, as `prvcgen [triple_replicate_inv hstep]`
(`triple_replicate_inv`, `triple_replicate`, `triple_list_mapM_inv`, `triple_list_foldlM_inv` and
their consequence forms). A loop equation in brackets, such as `prvcgen [replicate_zero]`, unfolds
the loop for `vcgen`.

**Verification conditions.** The structural reading leaves the postcondition at each possible
output. The angelic reading leaves `∃ u, wp (rest u) post ⊥` at each draw; name the witness with
`refine ⟨w, ?_⟩` and run `prvcgen` again. The conditions of the expectation readings are read back
into `ℝ≥0∞` (`Lean.Order.rel_eq_le`; `OracleComp.Upper.rel_iff`, `OrderDual.ofDual_toDual`,
`OracleComp.Upper.ofDual_wp`, `ofDual_add`, …), and those that the range of an indicator settles or
that are reflexive are closed (`propInd_le_one`, `one_le_propInd_iff`, `le_refl`). Name the values a
condition is stated over with `rename_i`.

**Equations.** `= 0` is the upper bound alone. `= 1` uses the structural bridge when uniform answers
are available: its conditions are the event itself at every possible output, and the structural
catalogue (including the handler specifications) is the largest; without uniform answers it
splits. Any other `= c` splits into the upper bound and the lower bound. Both halves receive the
invariants, the `with` step and the tail; each keeps the rules stated in its reading (read off the
carrier of the rule's triple), and definitions to unfold go to both. Where the split works:

- **Settled outright.** Every-outcome rules (`= 0`, `= 1`, an expectation constant on every path),
  and a loop invariant or handler potential that pins the value exactly, written without a carrier
  ascription so that each half elaborates it in its own carrier:
  `prvcgen [count] invariants · fun _ suff c => ↑c + ↑suff.length`.
- **Sums left for `simp`.** With the averaging rules of both readings
  (`prvcgen [OracleComp.Upper.Spec.uniformSample_avg, OracleComp.Quantitative.Spec.uniformSample_sum]`)
  each half ends in a sum whose continuation `vcgen` did not enter; `simp` on the normal form
  evaluates it, as for `Pr{let b ← $ᵗ Bool}[b = true] = 1 / 2`.
- **Refused.** An equation between the probabilities of two programs is a program equality, a
  game hop: `prvcgen` fails and points to `prrw` (see *Program equalities* below), the couplings
  `rvcstep` / `rvcgen`, and the `=ᵈ` lemmas.

**Adding rules for a reading.** State the rule as a triple of that reading, in its namespace, with
the precondition built from lattice connectives so that `vcgen` continues through it (gotcha 36):
`Lean.Order.iInf` for every outcome in the lower-bound reading and the largest outcome in the
upper-bound reading (whose `iInf` is the supremum in `ℝ≥0∞`), `∀` in the structural reading, and
`∃` (which `vcgen` does not split) in the angelic reading. Register it with `@[spec]` when it holds
for every call of the program; pass it explicitly (`prvcgen [rule]`) when it needs a hypothesis or
ends the descent, as the averaging rules do.

Known limits:

- **Sums stop `vcgen`.** `vcgen` splits only lattice connectives (`⊓`, `⇨`, `⌜·⌝`, `⊤`,
  `Lean.Order.iInf`). A precondition written with `∑`, `if`, or `∧` becomes a verification
  condition, and `vcgen` does not descend into the programs inside it. Exact values of queries and
  draws are therefore computed by `simp` on the normal form of `Pr{…}[…]` (see *Exact values*
  below), and the exact rules serve only for the last draw. Rules meant to be stepped through
  state their preconditions with lattice connectives. `Lean.Order.iInf` needs a `Type`-indexed
  binder, so a support condition is indexed by the subtype `{a // a ∈ support oa}`.
- **Event normal forms.** `Pr{…}[…]` elaborates to its normal form, nested expectations over each
  draw, so `le_prEvent_iff_triple` matches only an event of a named program. A lower bound on
  the normal form of an inline program is read by `le_wp_iff_triple`, and `vcgen` steps through
  the nested expectations.
- **Structure-literal projections.** `vcgen` does not reduce a projection of a structure literal
  (`{ keygen := …, … }.keygen`); it reports "no spec found". Use `dsimp only` first, or unfold with
  the `@[simps]` projection lemmas.
- **Invariant bullets.** In `vcgen … invariants · I`, the following `·` bullets are read as further
  invariants. Address the verification conditions with `case vc1 => …` instead.
- **Sum handlers.** A query to `impl₁ + impl₂` at `.inl t` has value type
  `(spec₁ + spec₂).Range (.inl t)`. `vcgen` does not unfold the sum while matching, so
  `QueryImpl.Spec.add_inl` / `add_inr` (`Unary/HandlerSpecs.lean`) route the query to the
  component at the component's value type. A handler defined as a sum is unfolded in the same
  call, as in `vcgen [myHandler, componentHandler]`. The rules match only when the handler's
  specification is spelled `spec₁ + spec₂` up to reducible unfolding. A combined specification
  introduced by a plain `def` (`def MySpec := spec₁ + spec₂`) hides the sum. For such a
  specification, declare it `abbrev`, or `change` the goal to the component's program and value
  type.
- **Generic monads.** A lemma over a generic `[MonadAttach m] [LawfulMonadAttach m]` installs the
  structural reading with `letI := MonadAttach.toWPMonadDemonic (m := m)` in its statement.
  `attribute [local instance] MonadAttach.toWPMonadDemonic` also selects it for `StateT σ m`,
  which pre-empts core's transformer instances.

## Program equalities (`prrw`)

An equality between the probabilities of two programs is a game hop, not a triple of one program.
`prrw` (`VCVio.ProgramLogic.Tactics.Unary`) proves the ones where the programs differ by the order
of independent draws or agree after a shared prefix. It works on `Pr{…}[…] = Pr{…}[…]`,
`𝔼{…}[…] = 𝔼{…}[…]`, applied masses `𝒟[oa] {y} = 𝒟[ob] {y}`, and output measures
`𝒟[oa] = 𝒟[ob]`. Every form first brings both sides of an event or expectation equation into the
normal form of `Pr{…}[…]` and `𝔼{…}[…]` (`simp only [expect_norm]`), and those of an output-measure
equation into plain bind chains (`map_eq_bind_pure_comp`, `bind_assoc`).

| Tactic | What it does |
|--------|--------------|
| `prrw` | Rewrites one top-level swap of two adjacent independent binds |
| `prrw under n` | Rewrites one swap under `n` shared bind prefixes, on either side |
| `prrw congr` | Reduces a shared first bind to its continuations on the support of the shared program, introducing the value and `hx : x ∈ support mx` |
| `prrw congr'` | Reduces a shared first bind for every value, without a support hypothesis |
| `prrw normalize` | Searches bounded sequences of swaps and congruence steps, sized by the bind depth of the goal, for one that closes the equality |
| `… as ⟨x, …⟩` | On `prrw`, `prrw under n`, `prrw congr`, `prrw congr'`: names the values the step introduces; `prrw congr as ⟨x, hx, y, hy⟩` and `prrw congr' as ⟨x, y⟩` reduce one shared bind per name group |

Swaps use `OracleComp.wp_swap` on events and expectations, descending through the nested
expectations of the normal form, and `OracleComp.evalDist_bind_bind_swap` on output measures
(countable answer types), or their `_of_uniform` forms under `IsUniformMeasureSpec`. Congruence uses
`wp_congr_of_support`, `OracleComp.evalDist_bind_apply_congr_of_support` and
`OracleComp.evalDist_bind_congr_of_support`, leaving the continuations on the structural support
of the shared prefix.

Choosing a form:

- **One swap, then continue or close**: `prrw`; a goal that the rewrite makes reflexive closes.
- **The swap sits below shared outer binds**: `prrw under n`.
- **The programs share a prefix**: `prrw congr`, or `prrw congr'` when the continuations agree for
  every value; `as ⟨…⟩` peels several shared binds at once.
- **The sequence of steps is not obvious**: `prrw normalize`, which fails unless it closes the goal.
- **Beyond these steps**: peel the shared prefix with `prrw congr` and continue by hand, relate the
  programs by a coupling (`by_equiv`, `rvcstep` / `rvcgen`), or use the `=ᵈ` lemmas.

A point mass `Pr{let y ← oa}[y = x]` is the event `(· = x)`, and `Pr{…}[…]` elaborates to nested
expectations `wp⟦mx⟧ fun x => wp⟦my x⟧ (predInd p)`, so a draw is swapped by rewriting under the
expectations it is nested in; `prrw under n` does so through `conv`, and gotcha 11 gives the manual
form.

```lean
-- Pr{let x ← mx >>= fun a => my >>= fun b => f a b}[x = z]
--   = Pr{let x ← my >>= fun b => mx >>= fun a => f a b}[x = z]
prrw

-- h : ∀ x ∈ support mx, Pr{let y ← f x}[q y] = Pr{let y ← g x}[q y]
-- ⊢ Pr{let y ← mx >>= f}[q y] = Pr{let y ← mx >>= g}[q y]
prrw congr
exact h _ ‹_›

-- h : ∀ x y, Pr{let r ← f x y}[q r] = Pr{let r ← g x y}[q r], with two shared binds
prrw congr' as ⟨x, y⟩
exact h x y
```

## Exact values (`expect_norm`, `expect_eval`)

An equation between one program's expectation and its value is proved by simplification.
`simp only [expect_norm]` brings an expectation into the normal form that `𝔼{…}[…]` and
`Pr{…}[…]` elaborate to (see [`probability.md`](probability.md)). The simp set `expect_eval`
(registered in `VCVio/EvalDist/ProbabilityNotation/Attr.lean`, its lemmas tagged in
`VCVio/ProgramLogic/Unary/HoareTriple.lean`) continues with the unfolding of loops
(`OracleComp.replicate_zero`, `OracleComp.replicate_succ_bind`, `List.mapM_nil`, `List.mapM_cons`,
`List.foldlM_nil`, `List.foldlM_cons`), the value of a query or a uniform draw (`wp_query`,
`wp_liftM_query`, `wp_HasQuery_query`, `wp_uniformSample`), and `le_refl`, so
`simp only [expect_norm, expect_eval]` proves equations such as

```lean
wp⟦oa >>= f⟧ g = wp⟦oa⟧ fun x => wp⟦f x⟧ g
wp⟦oa.replicate (n + 1)⟧ post = wp⟦oa⟧ fun x => wp⟦oa.replicate n⟧ fun xs => post (x :: xs)
wp⟦(query t : OracleComp spec _)⟧ post = ∫⁻ u, post u ∂OracleSpec.IsMeasureSpec.toMeasure t
```

and, through `le_refl`, the matching inequalities. An equation whose value is not an expectation,
such as `wp⟦pure x⟧ post = post x`, is also a `prvcgen` goal, split into its two bounds. `simp` on
the normal form averages finite uniform draws and uniform queries (`prEvent_uniformSample`,
`wp_uniformSample_eq_sum`, `OracleComp.wp_monadLift_query_uniform`), as for
`Pr{let b ← $ᵗ Bool}[b = true] = 1 / 2`. `wp_simulateQ_eq` and `wp_liftComp`
(`Unary/SimulateQ.lean`) carry an expectation across a simulation that answers each query in
distribution as the query itself, and across a lift to a larger specification.

## Relational Infrastructure

### RelTriple (pRHL coupling)

```lean
abbrev RelPost (α β : Type) := α → β → Prop
def EqRel (α : Type) : RelPost α α := fun x y => x = y

-- ⟪oa ~ ob | R⟫
abbrev RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop
```

Key rules:

| Rule | Use |
|------|-----|
| `relTriple_pure_pure` | Both sides are `pure`, prove `R a b` |
| `relTriple_bind` | Decompose bind on both sides |
| `relTriple_refl` | Same computation → `EqRel` |
| `relTriple_eqRel_of_eq` | Definitionally equal → `EqRel` |
| `relTriple_eqRel_of_evalDistEq` | Equal in distribution (`=ᵈ`) → `EqRel` |
| `relTriple_query` | Same query → `EqRel` on response |
| `relTriple_query_bij` | Same query with bijection `f` → `fun a b => f a = b` |
| `relTriple_uniformSample_bij` | Uniform sampling with bijection |
| `relTriple_if` | Synchronized conditional |
| `relTriple_post_mono` | Weaken postcondition |
| `evalDistEq_of_relTriple_eqRel` | Extract `oa =ᵈ ob` from an `EqRel` triple; `evalDist_eq_of_relTriple_eqRel` gives the output measures in any structure |
| `prEvent_eq_of_relTriple_eqRel` | Equal event probabilities from `EqRel` triple |
| `prEvent_le_of_relTriple` | Event inequality from an implication along the coupling |

### Relational simulateQ

For oracle simulation with state invariants:

```lean
relTriple_simulateQ_run :
  (∀ t s₁ s₂, R_state s₁ s₂ → RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
    (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)) →
  R_state s₁ s₂ →
  RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
    (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)
```

### Handler `@[spec]` catalog (`Unary/HandlerSpecs.lean`)

Per-call core triples `⦃ pre ⦄ handler t ⦃ post ⦄` under the structural reading
(`open scoped OracleComp.Qualitative`), tagged `@[spec]` so core `vcgen` composes them through
multi-query handler programs:

| Handler | Spec | Postcondition |
|---------|------|---------------|
| `cachingOracle` | `cachingOracle_triple` | `cache₀ ≤ cache' ∧ cache' t = some v` (shared live-query + cache-monotonicity) |
| `seededOracle` | `seededOracle_triple` | branch on `seed t`: `nil → no-op`, `cons u us → pop head` |
| `loggingOracle` | `loggingOracle_triple` | `log' = log₀ ++ [⟨t, v⟩]` (always extend the log) |
| `countingOracle` | `countingOracle_triple` | `toAdd qc' = qc₀ + QueryCount.single t` (additive writer via the monoid bridge) |
| `costOracle` | `costOracle_triple` | `s' = s₀ * costFn t` for arbitrary `[Monoid ω]` |

The `WriterT`-based handlers read their log as accumulated state: `WriterT.AppendWP`
(`ToMathlib/Control/WriterT/WP.lean`) for the list log of `loggingOracle`, and PolyFun's
`WriterT.MonoidWP` for the monoid logs of `countingOracle` and `costOracle`. The support readings
`triple_stateT_iff_forall_support`, `triple_writerT_iff_forall_support` and
`triple_writerT_iff_forall_support_monoid` are in `Unary/HandlerSpecs.lean`.

Core `vcgen` on handler programs:

- Core registers no rule for `StateT.mk`; `triple_stateT_mk` supplies it (`seededOracle`).
- A query reaches `vcgen` as `MonadLift.monadLift (MonadLiftT.monadLift q)` once `liftM q`
  unfolds, and `HasQuery.query t` is not unfolded; `Spec.monadLift_query` and `Spec.query` in
  `Unary/WP/Qualitative.lean` are stated in those forms.
- A ghost argument that only a non-equational precondition determines is passed explicitly:
  `vcgen [cachingOracle_triple _ cache₀]`. Equational ghosts (`seed = seed₀`) unify.
- `vcgen … with` takes a single `grind`-mode step.
- A sum handler `impl₁ + impl₂` is stepped by `QueryImpl.Spec.add_inl` / `add_inr` after a case
  split on the query index; see *Core `vcgen` on oracle computations* above.

### Whole-program invariant preservation (`SimSemantics/PreservesInv.lean`)

Support-based invariant-preservation over `simulateQ`, for both the
state-transformer and writer-transformer models:

| Definition | Shape | Meaning |
|------------|-------|---------|
| `QueryImpl.PreservesInv` | `σ → Prop` | every `(impl t).run σ₀` keeps the state invariant |
| `QueryImpl.WriterPreservesInv` | `ω → Prop` under `[Monoid ω]` | every `(impl t).run` step keeps `s₀ * w` satisfying `Inv` |
| `QueryImpl.WriterPreservesInv.of_mul_closed` | — | canonical builder: `Q` closed under `*` and holding on per-query increments yields `WriterPreservesInv` |
| `OracleComp.simulateQ_run_preservesInv` | — | lift per-query `PreservesInv` to whole simulation |
| `OracleComp.simulateQ_run_writerPreservesInv` | — | writer analogue |

Core-triple whole-program lifts (`Unary/HandlerSpecs.lean`), by induction on the program with
`Std.WP.Triple.pure` and `Std.WP.Triple.bind`:

| Theorem | Shape |
|---------|-------|
| `simulateQ_triple_preserves_invariant` | `StateT` version, for every reading of the handler's monad |
| `simulateQ_triple_ranked` | `StateT` invariant ranked by a query budget, one unit per query of an `IsTotalQueryBound` computation (a union bound under `OracleComp.Upper`) |
| `simulateQ_writerT_triple_preserves_invariant` | `WriterT` (monoid, `WriterT.MonoidWP`) version |
| `simulateQ_writerT_append_triple_preserves_invariant` | `WriterT` (append log such as `QueryLog`, `WriterT.AppendWP`) version |

The handler may target any oracle world: `QueryImpl spec (StateT σ (OracleComp spec'))` covers
the handlers of security games, which answer into `ProbComp`.

`WriterPreservesInv` is the canonical invariant-preservation API for
writer-based handlers like `countingOracle`/`costOracle`. Typical use:
pick `Inv s := s ≤ B` (cost-budget) or `Inv s := s ∈ Submonoid.S` (stays
in a submonoid).

Worked examples in `HandlerSpecs.lean`:

| Example | What it shows |
|---------|---------------|
| `simulateQ_cachingOracle_preserves_cache_le` | Whole-simulation cache monotonicity for `cachingOracle` (`StateT`) |
| `simulateQ_cachingLoggingOracle_preserves_cache_le` / `..._log_prefix` | Stacked `StateT` handler preserves each component's invariant |
| `simulateQ_countingOracle_preserves_le` | Whole-simulation count monotonicity for `countingOracle` via the `WriterT` lift with `I qc := qc₀ ≤ Multiplicative.toAdd qc` |
| `simulateQ_costOracle_preserves_submonoid` | Submonoid closure: if `costFn t ∈ S` for every `t`, the accumulated cost stays in `S` |

### Unary-to-relational handler lift (`Relational/HandlerFromUnary.lean`)

If each handler has a core triple spec (proved by core `vcgen` or a `@[spec]` lemma), you do not
have to assemble per-call `RelTriple`s by hand. The lift converts unary handler specs plus a
synchronization condition into a whole-program `RelTriple`:

```lean
relTriple_simulateQ_run_of_triples :
  (∀ t s, ⦃ fun s' => s' = s ⦄ impl₁ t ⦃ fun a s' => Q₁ t s a s' ⦄) →
  (∀ t s, ⦃ fun s' => s' = s ⦄ impl₂ t ⦃ fun a s' => Q₂ t s a s' ⦄) →
  (hsync : Q₁ ∧ Q₂ ⇒ output equality + R_state preservation) →
  R_state s₁ s₂ →
  RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
    (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)
```

Projection and bridge variants:

| Variant | Use when |
|---------|----------|
| `relTriple_simulateQ_run_of_triples` | Full `(value, state)` postcondition (`StateT`) |
| `relTriple_simulateQ_run'_of_triples` | Only `EqRel α` on projected outputs (`StateT`) |
| `relTriple_simulateQ_run_of_impl_eq_triple` | Two handlers agreeing on `Inv`; preservation spec is a core triple; conclude `EqRel (α × σ)` |
| `relTriple_simulateQ_run_writerT` | Whole-program `WriterT` coupling from per-query `RelTriple`s plus a monoid-congruence hypothesis on the accumulated writers |
| `relTriple_simulateQ_run_writerT'` | Output-projection of `relTriple_simulateQ_run_writerT` (drops the writer component, yielding `EqRel α` on outputs) |
| `relTriple_simulateQ_run_writerT_of_impl_eq` | `WriterT` analogue of `relTriple_simulateQ_run_of_impl_eq_preservesInv`: two handlers with identical `.run` outputs yield `EqRel (α × ω)` on whole simulations |
| `relTriple_simulateQ_run_writerT_of_triples` | `WriterT` handler-level whole-program lift from unary triples (monoid variant) |
| `relTriple_simulateQ_run_writerT'_of_triples` | Output-projection of `relTriple_simulateQ_run_writerT_of_triples` |
| `relTriple_run_of_triple` | Per-call product coupling for `StateT` |
| `relTriple_run_writerT_of_triple` | Per-call product coupling for `WriterT` (`Append` variant, e.g. `loggingOracle`) |
| `relTriple_run_writerT_of_triple_monoid` | Per-call product coupling for `WriterT` (`Monoid` variant, e.g. `countingOracle`, `costOracle`) |
| `support_preservesInv_of_triple` | Convert core-triple preservation into `support`-based preservation consumed by `SimulateQ.lean` (`StateT`) |
| `writerPreservesInv_of_triple` | `WriterT` analogue: produces `QueryImpl.WriterPreservesInv impl Inv` from a per-query core triple |

Whenever the handler's invariant-preservation proof already lives as a
core triple, prefer `relTriple_simulateQ_run_of_impl_eq_triple` over
the raw `relTriple_simulateQ_run_of_impl_eq_preservesInv` — the bridge
saves you from re-expressing the preservation as a `support`-based
quantifier.

### Identical Until Bad

```lean
measureETVDist_simulateQ_run'_le_prEvent_bad :
  (∀ t s, ¬bad s → ∀ q, Pr{let z ← (impl₁ t).run s}[q z ∧ ¬bad z.2] =
    Pr{let z ← (impl₂ t).run s}[q z ∧ ¬bad z.2]) →
  (bad monotone for impl₁ and impl₂) →
  measureETVDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
    ≤ Pr{let z ← (simulateQ impl₁ oa).run s₀}[bad z.2]
```

The handlers need only agree on good-to-good steps, so they may disagree on the step that sets
a bad flag; `_of_run_eq` and `_of_evalDistEq` take agreement off bad input states instead. No
measurable structure is needed on the state.

### eRHL (quantitative relational logic)

```lean
-- ⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄
VCVio.ProgramLogic.RelTriple pre oa ob post Lean.Order.bot Lean.Order.bot
-- definitionally unfolds to:
pre ≤ eRelWP oa ob post

-- ⟪c₁ ≈[ε] c₂ | R⟫
def ApproxRelTriple (ε : ℝ≥0∞) (oa ob : ...) (R : RelPost α β) : Prop :=
  1 - ε ≤ eRelWP oa ob (RelPost.indicator R)
```

Uniform samples and queries coupled by a bijection `f` have coupled expectation at least the unary
expectation `wp ($ᵗ α) (fun a => post a (f a))`; a `pure` side collapses `eRelWP` to the unary `wp`
of the other side.

pRHL is the special case where `ε = 0` (exact coupling). On equality,
`approxRelTriple_eqRel_iff_etvDist_le` identifies `ApproxRelTriple ε` with a total variation bound
`ε` between the output measures, through the maximal coupling of
`ToMathlib/MeasureTheory/Measure/Coupling/Maximal.lean`.

### Design target

eRHL is the design target for relational program logic in this repo. When extending the
logic, build the quantitative `ℝ≥0∞` foundation first, then recover pRHL and apRHL as
special cases via indicator postconditions. Do not add a pRHL-only layer that bypasses
the quantitative foundation.

The current tactic UX is still pRHL-flavored because the interactive proof shell is
`RelTriple`. That is intentional: exact coupling is the most ergonomic step-through mode
today, even though the semantic design target remains eRHL-first.

Before changing the eRHL / pRHL / apRHL design, consult
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25)).
Treat the published paper as the authoritative source for the intended relational WP
design. For the historical pRHL lineage behind exact coupling, see
[PRHL14](../../REFERENCES.md#prhl14).

## Game-Hopping Proof Skeleton

```lean
theorem my_security : g₁ =ᵈ gₙ := by
  game_trans g₂
  · by_equiv            -- g₁ =ᵈ g₂ via coupling
    rvcstep using R
    · rvcstep using f
      · exact hf
      · intro x
        exact hR x
    · intro a b hab
      rvcgen
  · game_trans g₃       -- g₂ =ᵈ gₙ
    · ...
    · ...
```

## Common Pitfalls

1. **`prrw normalize` closes the goal or fails**: use `prrw`, `prrw under n` or `prrw congr`
   when you want one rewrite step and intend to continue (gotcha 11).

2. **Import `VCVio.ProgramLogic.Tactics`**: tactics are defined there. If a file only imports `VCVio.ProgramLogic.Notation`, add/change the import.

3. **`game_rule` simp set**: many tactics use `simp only [game_rule]` internally. Ensure relevant `@[simp]` lemmas are in scope.

4. **`rvcstep using R`**: when Lean can't infer the witness for the current relational shape
   (bind cut, bijection, traversal input relation, or simulation invariant), provide it explicitly.

## Internal Architecture (`Sym`-backed Registry)

### Why `Lean.Meta.Sym.*`?

The relational planner needs to ask "given this `RelTriple` or `RelWP` goal, which registered
rules could fire?" *fast*, and without the cost or surprises of `isDefEq` unfolding. Core Lean has
been building a dedicated symbolic toolkit under `Lean.Meta.Sym` precisely for this: `Sym.Pattern`
records a de Bruijn-encoded skeleton of the indexed sub-expression together with its normalizing
preprocess (`preprocessType` unfolds reducible abbreviations, beta/zeta/eta-reduces, and
elaborates universes); `Sym.DiscrTree` is a thin wrapper over `Lean.Meta.DiscrTree` whose insertion
keys come from those preprocessed patterns and whose lookup is the pure structural `getMatch`.
Building on `Sym.Pattern` + `Sym.DiscrTree` gives the registry the same pattern preprocessing and
lookup cost profile as core's own tactics. Unary rules are core `@[spec]` theorems, which Lean
indexes itself for `vcgen` and `prvcgen`.

**Key alignment invariant**: `Sym.DiscrTree.getMatch` is purely structural, so
goal-side query terms must expose the same oracle-wrapper shapes as the pattern
side. The registry query functions therefore route the extracted computation
through `symMatchKey` (`Tactics/Common/Core.lean`), which recursively unfolds
only `OracleComp`, `OracleQuery`, and `OracleSpec.toPFunctor`. This targeted
normalization is necessary because `OracleComp` is a reducible alias of
`PFunctor.FreeM`, while deliberately avoiding `Sym.preprocessType`: applying
that declaration-oriented preprocessing to terms can unfold reducible user
programs and panic when a matcher contains loose de Bruijn variables. Without
the targeted unfolding, lookup can silently return no candidates (symptom: a
registered `@[vcspec]` rule never fires in `rvcstep` / `rvcgen` while applying it by hand works).

### The `@[vcspec]` registry

`VCVio/ProgramLogic/Tactics/Common/Registry.lean` defines `@[vcspec]`, which registers relational
rules: `RelTriple`, quantitative `VCVio.ProgramLogic.RelTriple`, `RelWP`, and raw relational
weakest-precondition bounds `pre ≤ VCVio.ProgramLogic.rwp oa ob post …`. Each is indexed by a
`Sym.Pattern` on the left computation `oa`, with a secondary `rightHead?` filter on the head
constant of the right computation. A theorem whose conclusion is a triple of one program fails to
register, with an error pointing to core `@[spec]`.
Each entry carries a `SpecProof` (reusing the core-Lean type from `Lean.Elab.Tactic.Do.SpecAttr`)
so origins can be distinguished between a global declaration, a local hypothesis, or a raw term.
Priorities are parsed from the attribute's optional priority argument (`@[vcspec (prio := 200)]`)
and follow the standard Lean convention: higher priority entries are tried first within the same
candidate pool. `Tactics/Common/Backward.lean` builds and caches the backward rule of each entry.

### Dispatch flow

1. **Relational VC-gen** (`VCVio/ProgramLogic/Tactics/Relational/Internals.lean`): on a
   `RelTriple` / `RelWP` / quantitative `VCVio.ProgramLogic.RelTriple` goal, the planner extracts
   the two computations, `whnfReducible`s them, asks the registry for candidate `VCSpecEntry`s via
   `getRegisteredRelationalVCSpecEntries`, filters by `kind` and `spec.compPattern`, previews each
   candidate through `runRelationalVCSpecRule` (which calls the
   `runRVCGenStepWithTheoremDirect` applicator), and picks the best plan.
2. **Unary rules**: `prvcgen` and core `vcgen` consult the core `@[spec]` catalogue, which Lean
   indexes itself; the handler specifications (`loggingOracle`, `cachingOracle`, …) are among
   its rules.
3. **Program equalities**: `prrw` applies fixed swap and congruence laws
   (`Tactics/Unary/Internals/ProbEq.lean`) and consults no registry.

### Extending the rule sets

| Want to add… | Tag it with | Expected shape |
|--------------|-------------|----------------|
| A unary rule usable by `prvcgen` / `vcgen` | `@[spec]` (or `@[local spec]`) | A core triple `⦃ pre ⦄ oa ⦃ post ⦄` of the reading it belongs to (see *Adding rules for a reading*) |
| A relational lemma usable by `rvcstep` / `rvcgen` | `@[vcspec]` | `RelTriple oa ob R`, `RelWP oa ob post`, or quantitative `VCVio.ProgramLogic.RelTriple pre oa ob post Lean.Order.bot Lean.Order.bot` |
| An evaluation equation for exact values | `@[expect_eval]` | `wp⟦comp⟧ post = …`, or one unfolding of a loop combinator |

## SymM Stability Note and Future Proof Repair

`Lean.Meta.Sym.*` is still under active development in core Lean. The APIs the `@[vcspec]`
registry depends on (`Sym.Pattern`, `Sym.DiscrTree`, `Sym.insertPattern`, `Sym.getMatch`,
`Sym.mkPatternFromDeclWithKey`, and `SpecProof` in `Lean.Elab.Tactic.Do.SpecAttr`) are all used by
core's `mvcgen` and `vcgen` too, so their direction is broadly stable, but none of them carry a
compat-preservation promise yet. Expect the following classes of churn each time we bump the
toolchain:

- **Signature changes on `Sym.mkPatternFromDeclWithKey`**. If the selector
  signature changes (e.g. becomes `Expr → MetaM (Pattern × α)` instead of
  `Expr → MetaM (Expr × α)`), update `buildVCSpecEntry` in `Registry.lean` to match.
- **`Sym.Pattern` preprocessing behaviour**. If the default reducibility
  used by `preprocessType` shifts (e.g. stops unfolding certain abbreviations
  or starts unfolding more), the "folded vs unfolded head" helpers
  (`headIsOneOf`, `relTripleBodyParts?`, `relWpBodyParts?`, `rawRelWpBodyParts?` in
  `Registry.lean`) may need to grow new cases. All of these live in its
  `Preprocessed-body head matchers` section.
- **`SpecProof` variants**. We only use `.global` today. If core splits or
  merges variants, `VCSpecEntry.declName?` plus the matching `MetaM` inserts need to be adjusted.
- **`registerSimpleScopedEnvExtension` purity**. `addEntry` is pure today
  and the registry relies on that; if it changes, the attribute handler already
  computes its patterns inside `MetaM` before calling `.add`, so the fix is to
  thread the `MetaM` result differently, not to restructure the registry.

The compensating design choices are: keep `Sym`-aware logic contained to the registry module
(`Registry.lean`, with `symMatchKey` in `Common/Core.lean`), and prefer the structural `getMatch`
over `isDefEq`.

### Core WP and the symbolic rewriter boundary

Lean v4.35 provides lattice-generic `Std.WP.WPMonad`, `Triple`, transformer
instances, and `vcgen`. The unary carriers in `Unary/WP/` consume these directly:

- Universal structural reachability is the core instance of `OracleComp spec`
  (`OracleComp.Qualitative.instWP`): `wp oa post ⊥`, core triples and `vcgen` read every possible
  output without opening a scope, and with no probability interpretation.
- `open scoped OracleComp.Quantitative` selects expectation in `ℝ≥0∞` under
  `[OracleSpec.IsMeasureSpec spec]` (`OracleComp.Quantitative.instWP`), so `wp oa post ⊥`, core
  triples and `vcgen` read expectations, with lower-bound triples.
- `open scoped MeasureProgramLogic.Quantitative` selects measure-backed expectation
  for any lawful monad with `LawfulEvalDistSemantics`. Besides its `WPMonad`, it registers the
  interpretation as a direct `WP` instance (`wpInst`) at priority `1050`, which outranks core's
  own direct `Prop` instances for monads such as `Option` and `Id` while the scope is open, and is
  outranked by the reading scopes of `OracleComp` (gotcha 33). Its module is
  `VCVio.ProgramLogic.Unary.WP.Measure`.
- `open scoped OracleComp.Angelic` selects existential structural reachability.
- `open scoped OracleComp.Upper` selects the expectation over the order duals `ℝ≥0∞ᵒᵈ`
  (`ExactWPMonad.dual`), whose triples are upper bounds.
- `open scoped OracleComp.Probabilistic` selects the restricted algebra on `Set.Iic 1`.
- The `Dispatch` sub-scopes of the structural, angelic, expectation and upper-bound readings
  register each at priority `1200`, with a direct `WP` instance, for per-call use by `prvcgen`.

Core's assertion carriers are output parameters, so instance search reads a program's
interpretation off its type alone and one interpretation is live per program type. The scoped
readings take precedence over the quantitative instance where they are opened. Support facts do
not need a second interpretation: the quantitative one consumes them through `MonadAttach`
(`wp_mono_of_support`, `wp_congr_of_support`), as core's own specifications pair `MonadAttach`
with any `WPMonad`. Core also documents how to keep several readings of one monad live at once:
a type synonym carrying its own instance, selected by the program's type (core's tests use
`HeapM` and `TickT`). A structural reading of oracle computations on such a synonym, with its own
global instance, is the route for running `vcgen` over `Prop` assertions on oracle computations;
VCVio does not define one yet. Quantitative expectation does not provide a general structural
reachability certificate. The probability-one coherence theorems state their additional uniformity
assumptions.

Use `open scoped Std.WP` for core triple notation.

The coupling interface `VCVio.ProgramLogic.RelWP` is local to VCVio and shares core's
assertion lattices. Its three carriers in `Relational/WP/` also use explicit scopes
(`OracleComp.Rel.Quantitative`, `.Qualitative`, `.Probabilistic`). Core has no relational program
logic and none is planned; its `WP` class accepts non-monadic program types, so a
product-program interpretation can let core `vcgen` walk two programs in lockstep, but choosing
which side to step and which coupling to use remains `rvcgen`'s job.
`Relational/FromUnary.lean` takes its unary premises as core triples under the structural
reading.

Core `vcgen` and `prvcgen` consume the core `@[spec]` catalogue, and the coupling tactics
`rvcgen` / `rvcstep` consume `@[vcspec]`. Generic transformer WP comes from core and PolyFun's
WriterT interpretation; VCVio retains its probability rules and existing transformer equality
lemmas. The scoped `WriterT.MonoidWP` interpretation uses multiplication; append-based logs use
`WriterT.toWPMonad` with explicit operations.

The handler specifications are core triples under the structural reading, proved and composed
by core `vcgen` (`Unary/HandlerSpecs.lean`), and the UC runtime's triples are core triples too
(`Interaction/UC/WP.lean`). Nothing in the built libraries uses core's older `Std.Do` stack;
`Interop/` (not built) keeps its `mvcgen` code until its own migration.

Core `vcgen` is experimental in v4.35 and warns unless acknowledged: the package acknowledges it
once in `lakefile.lean` (`experimental.vcgen`), `prvcgen` sets it for its own call so that
downstream files need nothing, and `VCVioTest/ProgramLogic/CoreWP.lean` pins the diagnostic with
the option off. `mvcgen` is deprecated in favour of `vcgen`, so program-level reasoning uses core
`Std.WP` triples. Exception postconditions form stacks written `EStack⟨A, B⟩` (values
`estack⟨a, b⟩`); an `OptionT` layer contributes `Unit → Pred`, an `ExceptT ε` layer `ε → Pred`.

For the next release, track the
[`WP.trans` renames](https://github.com/leanprover/lean4/pull/15171), the move of `vcgen`'s syntax
to `Std.WP.Tactic` with the deprecation of the `Std.Do` proof mode
([#15290](https://github.com/leanprover/lean4/pull/15290)), and exception-channel frames
([#15067](https://github.com/leanprover/lean4/pull/15067)), alongside the
[upstream roadmap](https://lean-lang.org/fro/roadmap/y4-1/).
