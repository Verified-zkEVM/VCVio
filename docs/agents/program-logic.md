# Program Logic Tactics and Relational Reasoning

## Current Module Boundary

- Import `VCVio.ProgramLogic.Tactics` for normal proof work. This is the canonical user-facing proof mode.
- Internally the tactic implementation is split into `VCVio.ProgramLogic.Tactics.Unary` and
  `VCVio.ProgramLogic.Tactics.Relational`; the umbrella import is still the intended default.
- `VCVio.ProgramLogic.Notation` provides the core notation and convenience predicates used by
  the tactic surface.
- Prefer the step-through tactics from `Tactics` for new proofs.
- `VCVio.ProgramLogic.Unary.StdDoBridge` is a narrow unary bridge for almost-sure correctness in the `.pure`
  `Std.Do` view. It is not the main engine for quantitative or relational VCGen.

For continuous or otherwise non-discrete denotations, import
`VCVio.ProgramLogic.Relational.Measure`. Its `MeasureProgramLogic.RelWP` uses an almost-everywhere
postcondition under a Mathlib `Measure.Coupling`, and `eRelWP` integrates quantitative
post-expectations with `lintegral`. The `OracleComp` relational logic (`RelTriple`, `CouplingPost`,
`eRelWP`) specializes these to the output measures observed in the discrete structure on each
output type; its sequential rules need finite response types, and its anchoring and bijection
rules for queries need uniform response measures.

## In-Tree Walkthroughs

- `Examples/ProgramLogic/UnaryStep.lean`: unary `vcstep` / `vcgen` examples.
- `Examples/ProgramLogic/RelationalStep.lean`: step-by-step relational tactic examples.
- `Examples/ProgramLogic/RelationalDerived.lean`: derived relational patterns and automation examples.
- `Examples/ProgramLogic/ProofMode.lean`: proof-mode entry points and small end-to-end examples.
- `VCVio/ProgramLogic/Relational/Examples.lean`: compact API examples for the relational layer.

## Tactic Quick Reference

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

### Optional arguments

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

### Quantitative VCGen (`vcgen`)

`vcgen` is the primary unary tactic for new proofs. It accepts both `Triple` goals and
probability goals, automatically lowering `Pr{...}[...]` events into the quantitative engine.

| Tactic | What it does |
|--------|--------------|
| `vcgen` | Exhaustively decomposes a `Triple` or probability goal with spec-aware stepping, loop invariant auto-detection, and support/indicator leaf closure |
| `vcstep` | One step: probability lowering → bind → conditional → match → loop → leaf |
| `vcstep?` | Performs one step and emits the corresponding explicit script, often surfacing `as ⟨...⟩`, `using cut`, `inv I`, or `with theorem` |
| `vcgen?` | Runs `vcgen` and emits the planned step replay across each pass |
| `vcstep using cut` | Explicit intermediate postcondition for a bind step |
| `vcstep with thm` | Force one explicit unary theorem/assumption step |
| `vcstep as ⟨x, hx⟩` | Explicit names for binders introduced by the current step |
| `vcstep inv I` | Explicit loop invariant for `replicate`/`foldlM`/`mapM` |
| `vcstep rw` | One explicit top-level bind-swap rewrite on a probability equality |
| `vcstep rw under n` | One bind-swap rewrite under `n` shared outer bind prefixes |
| `vcstep rw normalize` | Run the bounded probability-equality planner explicitly |
| `vcstep rw congr` | Expose one or more shared binds plus their support hypotheses |
| `vcstep rw congr'` | Expose one or more shared binds without support hypotheses |
| `exp_norm` | Normalize indicator (`propInd`) and expectation (`wp`) arithmetic |

**Probability-goal handling**: `vcgen` and `vcstep` automatically handle four
classes of probability goals:

1. **`Pr{...}[...] = 1` lowering** → rewrites into `Triple` form for structural decomposition:
   - `Pr{let x ← oa}[p x] = 1` → `Triple 1 oa (fun x => 𝟙⟦p x⟧)`; a singleton output
     `Pr{let y ← oa}[y = x]` is the event `p := (· = x)`

2. **Lower-bound event goals** → stay inside unary VCGen by reusing the same `Triple` shell:
   - `r ≤ Pr{let x ← oa}[p x]` / `Pr{let x ← oa}[p x] ≥ r` → `Triple r oa (fun x => 𝟙⟦p x⟧)`

3. **Probability equalities** (`Pr{...}[...]`, applied `𝒟[...]` masses, or output measures):
   - Plain `vcstep` first normalizes common `map`/`bind` surface syntax (`map_eq_bind_pure_comp`,
     `bind_assoc`), then preview-selects the best bounded swap/congruence plan from the fast path
   - `vcstep rw` performs exactly one top-level bind-swap rewrite
   - `vcstep rw under n` rewrites one swap beneath `n` shared outer bind prefixes
   - `vcstep rw normalize` runs the deeper bounded planner used for explicit suggestions
   - `vcstep rw congr` / `vcstep rw congr'` expose one or more shared binds explicitly
   - Swaps use `OracleComp.wp_swap` on events and expectations
     and `OracleComp.evalDist_bind_bind_swap` on output measures (countable responses), or their
     `_of_uniform` variants; a swap under shared draws descends through the expectations of the
     event's normal form. Congruence uses `wp_congr_of_support` /
     `OracleComp.evalDist_bind_apply_congr_of_support`, leaving the continuations on the
     structural support of the shared prefix

4. **Other general `Pr{...}[...]` goals** → rewrite to raw `wp` form and keep stepping structurally
   when a `wp` rule applies. On an already-lowered raw-`wp` goal, `vcstep?` / `vcgen?`
   will explicitly note that they are continuing in raw `wp` mode.

**Loop invariants**: `vcgen` auto-detects `replicate`, `List.foldlM`, and `List.mapM`
in `Triple` goals and applies matching invariant hypotheses from context.
Use `vcstep inv I` to provide an explicit invariant.

**Support-sensitive leaf closure**: `vcgen` final pass tries `triple_support`,
`triple_propInd_of_support` and `triple_prEvent_eq_one`
in addition to the standard `triple_pure`, `triple_zero`, and consequence search.

**Naming and suggestions**: plain `vcstep` / `rvcstep` keep the stable execution path.
The `?` variants run a planner-backed version of the same next move and emit a concrete
`Try this` script, typically surfacing an explicit `using ...` hint, `inv I`, `with theorem`,
or `as ⟨...⟩` clause that you can paste back into the proof. On probability-equality goals the
planner may emit a grouped multi-step replay when the best explanation is an explicit rewrite chain.

**Opt-in unary lookup**: mark a unary `Triple` or raw `wp` theorem with `@[vcspec]` to register it for
bounded head-symbol lookup. This is intentionally narrow: after the built-in structural step and
explicit hint opportunities, `vcstep` / `vcgen` consult only `@[vcspec]` theorems whose
computation head matches the current goal. Use `vcstep with myLemma` when you want to force
one specific theorem/assumption step manually.

**Opt-in relational lookup**: mark a relational `RelTriple`, `RelWP`, or quantitative
`VCVio.ProgramLogic.RelTriple` theorem with `@[vcspec]` to register it for the analogous bounded
head-pair lookup on the relational side.
This is especially useful for automation-oriented `simulateQ` transport lemmas whose outer
computation heads are stable but whose inner invariants or projection arguments still come from
the local context. Relational registered rules are tiered internally:
plain `rvcstep` / `rvcgen` use default-safe structural and leaf entries, while
rules that choose cuts, bijections, or broad theorem search are reached through
`rvcstep with thm`, `rvcstep using t`, `rvcfinish`, or `rvcgen!`.
This keeps ordinary rule ordering stable when new `@[vcspec]` lemmas are added.

### Handler Normalization

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `handler_step` | handler-heavy `FreeM` / `QueryImpl` / `simulateQ` / transformer goals | Runs one `simp only [handler_nf, handler_simp]` normalization pass to expose the next handler body or run-shape |

`handler_step` is deliberately thin. Use it when a proof is stuck behind
handler combinators such as cache overlays, logging handlers, counting
handlers, or state-transformer maps; then continue with `vcstep`, `rvcstep`,
`rvcgen`, or direct proof steps.

PolyFun owns the generic `handler_nf` rules for `FreeM`,
`PFunctor.Handler.Stateful`, `StateT`, and standard `WriterT`. VCVio's
`handler_simp` set adds only oracle simulation, query instrumentation,
caching, and local WriterT compatibility equations. Downstream code can use
the two sets independently; `handler_step` composes them in generic-to-specific
order.

**Opt-in `wp`-rewrite lookup**: mark an equational rewrite of shape
`wp⟦comp⟧ post = …` with `@[wpStep]` to extend the inner `wp`-stepping driver
(`runWpStepRules`). The driver indexes registered rules by the path of `comp`
in a `Lean.Meta.Sym`-backed discrimination tree: pattern construction goes
through `Lean.Meta.Sym.mkPatternFromDeclWithKey`, which preprocesses the rule's
LHS (unfolding reducibles, beta/zeta/eta normalizing) and turns universally
quantified arguments into de Bruijn pattern variables, while
`Lean.Meta.Sym.insertPattern` automatically wildcards proof / instance
positions in the discrimination-tree key. Lookup at dispatch time is the pure
`Lean.Meta.Sym.DiscrTree.getMatch` after a `withReducible whnf` on the goal's
`comp` to align with the preprocessed patterns. Each match is then tried via
`rw`, falling back to `simp only`. The default registry already covers
`wp_pure`, `wp_bind`, `wp_ite`, `wp_dite`, `wp_map`, the `replicate` / `mapM`
/ `foldlM` families, `wp_query`, `wp_uniformSample`, and the `simulateQ` /
`liftComp` transport rules, so user-authored `wp` lemmas slot into the same
dispatch without further wiring.

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

**Pass budget**: exhaustive `vcgen` / `rvcgen` runs are bounded by
`set_option vcvio.vcgen.maxPasses <n>`. The default is conservative so large proofs stay
predictable; if you intentionally want a longer exhaustive run, raise the option locally around
that proof.

**Trace output**: set `set_option vcvio.vcgen.traceSteps true` to log the chosen planned step,
goal delta, and any planner alternatives that were previewed while debugging tactic choice.

### Raw WP Tactics

Raw `wp` goals (`_ ≤ wp _ _`) now use the same unary entrypoints rather than a separate tactic
family. `vcstep` performs one decomposition step and `vcgen` keeps stepping exhaustively.


### Probability Equality Control

All probability-equality control now lives under `vcstep`.

| Tactic | What it does |
|--------|--------------|
| `vcstep` | Fast dispatcher for common probability-equality steps: syntax normalization, swap, congruence, and bounded compositions chosen by preview |
| `vcstep rw` | Rewrites one top-level bind swap without trying to close the goal |
| `vcstep rw under n` | Rewrites one bind swap under `n` shared outer bind prefixes on one side |
| `vcstep rw normalize` | Runs the bounded probability-equality planner explicitly, without broadening plain `vcstep` |
| `vcstep rw congr` | Reduces `Pr{let y ← mx >>= f₁}[q y] = Pr{let y ← mx >>= f₂}[q y]` to a pointwise goal, auto-introducing `x` and `hx : x ∈ support mx`; the explicit `as ⟨...⟩` form can peel multiple shared binds at once |
| `vcstep rw congr'` | Same, but without the support restriction; the explicit `as ⟨...⟩` form can peel multiple shared binds at once |

### Automation

| Tactic | What it does |
|--------|--------------|
| `rvcgen` | Exhaustive relational VCGen over all open goals, with automatic lowering from `=ᵈ` / output-measure equality and cheap leaf closure |
| `rvcfinish` / `rvcgen!` | Opt-in residual search and consequence closing |
| `rel_dist` | Turns `RelTriple oa ob (EqRel α)` into `oa =ᵈ ob` |

## Probability Equality Guide

### What plain `vcstep` handles

On probability equalities, plain `vcstep` already tries the common bind-swap and
bind-congruence patterns:

1. **Direct event equalities**: `Pr{let z ← mx >>= ... >>= ...}[q z] = Pr{let z ← my >>= ... >>= ...}[q z]`
2. **Nested bounded rewrites**: automatically peels small shared-bind prefixes and prefers a
   closing swap/congruence plan when one is available
3. **Surface `map` wrappers**: normalizes the common `map_eq_bind_pure_comp` / `bind_assoc` shape
   before searching for swaps or congruence

### When to use the explicit `rw` subcommands

- **Need to keep going after a swap**: use `vcstep rw`
- **Need to swap below shared outer binds**: use `vcstep rw under n`
- **Need the bounded planner to choose a swap/congruence chain now**: use `vcstep rw normalize`
- **Need to expose one or more common outer binds with support information**: use `vcstep rw congr`
- **Need the support-free congruence variant**: use `vcstep rw congr'`
- **Need the full explicit replay for a bounded nested swap**: use `vcstep?`
- **Need a deeper swap than the current bounded automation knows**: peel outer layers manually, or
  use `vcstep?` to see the best bounded replay the planner found before finishing the rest by hand

### Key insight: events vs output measures

The underlying bind-swap lemmas are `OracleComp.prEvent_bind_bind_swap` for events and
`OracleComp.evalDist_bind_bind_swap` for output measures. A point mass `Pr{let y ← oa}[y = x]` is the event
`(· = x)`, and `Pr{…}[…]` elaborates its final draw as a map, so the `vcstep`
probability-equality machinery normalizes with `map_eq_bind_pure_comp` / `bind_assoc` before
matching either shape.

### Patterns

**Standalone swap**:
```lean
vcstep
```

**Rewrite one swap and continue**:
```lean
vcstep rw
```

**Rewrite under one shared bind**:
```lean
vcstep rw under 1
```

**Run the bounded probability-equality planner explicitly**:
```lean
vcstep rw normalize
```

**Expose one common bind with support information**:
```lean
vcstep rw congr
exact h _ ‹_›
```

**Expose one common bind without support information**:
```lean
vcstep rw congr'
rename_i x
```

**Expose two shared binds explicitly at once**:
```lean
vcstep rw congr' as ⟨x, y⟩
```

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

`vcgen` on handler programs:

- Core registers no rule for `StateT.mk`; `triple_stateT_mk` supplies it (`seededOracle`).
- A query reaches `vcgen` as `MonadLift.monadLift (MonadLiftT.monadLift q)` once `liftM q`
  unfolds, and `HasQuery.query t` is not unfolded; `Spec.monadLift_query` and `Spec.query` in
  `Unary/WP/Qualitative.lean` are stated in those forms.
- A ghost argument that only a non-equational precondition determines is passed explicitly:
  `vcgen [cachingOracle_triple _ cache₀]`. Equational ghosts (`seed = seed₀`) unify.
- `vcgen … with` takes a single `grind`-mode step.

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
| `simulateQ_triple_preserves_invariant` | `StateT` version |
| `simulateQ_writerT_triple_preserves_invariant` | `WriterT` (monoid) version |

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

If each handler has a core triple spec (proved by `vcgen` or a `@[spec]` lemma), you do not have
to assemble per-call `RelTriple`s by hand. The lift converts unary handler specs plus a synchronization
condition into a whole-program `RelTriple`:

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

1. **Plain `vcstep` may close or progress a probability equality goal**: use
   `vcstep rw` / `vcstep rw under n` when you specifically want a rewrite and
   intend to continue.

2. **Import `VCVio.ProgramLogic.Tactics`**: tactics are defined there. If a file only imports `VCVio.ProgramLogic.Notation`, add/change the import.

3. **`game_rule` simp set**: many tactics use `simp only [game_rule]` internally. Ensure relevant `@[simp]` lemmas are in scope.

4. **`rvcstep using R`**: when Lean can't infer the witness for the current relational shape
   (bind cut, bijection, traversal input relation, or simulation invariant), provide it explicitly.

5. **`StdDoBridge` is deliberately narrow**: use it for unary almost-sure `.pure` `Std.Do` experiments, not as the default path for quantitative or relational proofs.

## Internal Architecture (`Sym`-backed Registries)

### Why `Lean.Meta.Sym.*`?

The planner needs to ask "given this `wp⟦comp⟧ post` or `Triple pre comp post`
goal, which registered rules could fire?" *fast*, and without the cost or
surprises of `isDefEq` unfolding. Core Lean has been building a dedicated
symbolic toolkit under `Lean.Meta.Sym` precisely for this: `Sym.Pattern`
records a de Bruijn-encoded skeleton of the indexed sub-expression together
with its normalizing preprocess (`preprocessType` unfolds reducible
abbreviations, beta/zeta/eta-reduces, and elaborates universes); `Sym.DiscrTree`
is a thin wrapper over `Lean.Meta.DiscrTree` whose insertion keys come from
those preprocessed patterns and whose lookup is the pure structural
`getMatch`. Core also ships a `Sym.Simp.Theorems` bundle (discrimination-tree
+ `Sym.Simp.Theorem` records) that core's own Sym-based `vcgen` consumes
(`Lean.Elab.Tactic.Do.Internal`); we do not consume it today (see *Future
`vcgen` bridge (deferred)* below) but
`Sym.Simp.mkTheoremFromDecl` lets us reconstruct it on demand from the
`@[wpStep]` registry when VCVio's symbolic proof-application bridge is
implemented and validated.

Building on `Sym.Pattern` + `Sym.DiscrTree` means our registries share the
same pattern preprocessing and lookup cost profile as future core tactics,
and the migration to `Sym.Simp.*`-driven rewriting is a localised follow-up
in two registry files rather than a framework rewrite.

**Key alignment invariant**: `Sym.DiscrTree.getMatch` is purely structural, so
goal-side query terms must expose the same oracle-wrapper shapes as the pattern
side. All registry query functions therefore route the extracted computation
through `symMatchKey` (`Tactics/Common/Core.lean`), which recursively unfolds
only `OracleComp`, `OracleQuery`, and `OracleSpec.toPFunctor`. This targeted
normalization is necessary because `OracleComp` is a reducible alias of
`PFunctor.FreeM`, while deliberately avoiding `Sym.preprocessType`: applying
that declaration-oriented preprocessing to terms can unfold reducible user
programs and panic when a matcher contains loose de Bruijn variables. Without
the targeted unfolding, lookup can silently return no candidates (symptom:
`vcstep` reports "no matching rule applied" while the corresponding manual
rewrite works).

### Registries and what they index

| File | Attribute | Role |
|------|-----------|------|
| `VCVio/ProgramLogic/Tactics/Common/Registry.lean` | `@[vcspec]` | Unary and relational `Triple` / `RelTriple` / `RelWP` / quantitative `VCVio.ProgramLogic.RelTriple` rules, indexed by a `Sym.Pattern` on the computation slot (`oa` for unary, `oa` with a secondary `rightHead?` filter for relational) |
| `VCVio/ProgramLogic/Tactics/Common/WpStepRegistry.lean` | `@[wpStep]` | Equational `wp⟦comp⟧ post = …` rewrites, indexed by a `Sym.Pattern` on `oa` and consulted by `runWpStepRules` via `TacticM` rewriting (`rw` then `simp only`). The `Sym.Simp.Theorem` bundle for an eventual `SymM`-side rewriter is *not* eagerly built; `Sym.Simp.mkTheoremFromDecl` can rebuild it on demand from `getAllWpStepEntries` |

Each entry carries a `SpecProof` (reusing the core-Lean type from
`Lean.Elab.Tactic.Do.SpecAttr`) so origins can be distinguished between a
global declaration, a local hypothesis, or a raw term. Priorities are parsed
from the attribute's optional priority argument (`@[vcspec (prio := 200)]`).

### Dispatch flow

1. **Unary / relational VC-gen** (`VCVio/ProgramLogic/Tactics/Unary/Internals.lean`,
   `VCVio/ProgramLogic/Tactics/Relational/Internals.lean`): on a `Triple`/`wp`/`RelTriple`/`RelWP`/quantitative
   `VCVio.ProgramLogic.RelTriple`
   goal, the planner extracts the computation slot(s), `whnfReducible`s them,
   asks the registry for candidate `VCSpecEntry`s via
   `getRegisteredUnaryVCSpecEntries` / `getRegisteredRelationalVCSpecEntries`,
   filters by `kind` and `spec.compPattern`, previews each candidate (via the
   shared `runUnaryVCSpecRule` / `runRelationalVCSpecRule` helpers which call
   the `runVCGenStepWithTheoremDirect` / `runRVCGenStepWithTheoremDirect`
   applicators), and picks the best plan.
2. **`wp`-rewrite driver** (`VCVio/ProgramLogic/Tactics/Common/WpStepDispatch.lean`): on any goal
   containing `wp _ _`, `runWpStepRules` pulls the `oa` argument out of the
   first matching `wp` application, `whnfReducible`s it, asks
   `getRegisteredWpStepEntries` for hits on the `oa`-keyed `Sym.DiscrTree`,
   and tries each via `rw` then `simp only` until one lands.
3. **Handler `@[spec]` rules**: unary handlers (`loggingOracle`,
   `cachingOracle`, …) use core `Std.WP` triples and the `@[spec]` catalogue
   directly; those are indexed by Lean itself and consumed by core `vcgen`.

### Extending the registries

| Want to add… | Tag it with | Expected shape |
|--------------|-------------|----------------|
| A unary Triple lemma usable by `vcstep` / `vcgen` | `@[vcspec]` | `Triple pre oa post` or raw `wp⟦oa⟧ post ≥ pre` |
| A relational lemma usable by `rvcstep` / `rvcgen` | `@[vcspec]` | `RelTriple oa ob R`, `RelWP oa ob post`, or quantitative `VCVio.ProgramLogic.RelTriple pre oa ob post Lean.Order.bot Lean.Order.bot` |
| A `wp`-driven equational rewrite | `@[wpStep]` | `wp⟦comp⟧ post = …` (exact head: core's `wp`) |

Priorities (`@[vcspec (prio := 200)]`, `@[wpStep (prio := 200)]`) follow the
standard Lean convention: higher priority entries are tried first within the
same candidate pool.

## SymM Stability Note and Future Proof Repair

`Lean.Meta.Sym.*` is still under active development in core Lean. The APIs
we depend on today (`Sym.Pattern`, `Sym.DiscrTree`, `Sym.insertPattern`,
`Sym.getMatch`, `Sym.mkPatternFromDeclWithKey`, and `SpecProof` in
`Lean.Elab.Tactic.Do.SpecAttr`) are all used by core's `mvcgen` and `vcgen`
too, so their direction is broadly stable, but none of them carry a
compat-preservation promise yet. Expect the following classes of churn each
time we bump the toolchain:

- **Signature changes on `Sym.mkPatternFromDeclWithKey`**. If the selector
  signature changes (e.g. becomes `Expr → MetaM (Pattern × α)` instead of
  `Expr → MetaM (Expr × α)`), update `buildVCSpecEntry` /
  `buildWpStepEntry` in `Registry.lean` / `WpStepRegistry.lean` to match.
- **`Sym.Pattern` preprocessing behaviour**. If the default reducibility
  used by `preprocessType` shifts (e.g. stops unfolding certain abbreviations
  or starts unfolding more), the "folded vs unfolded head" helpers
  (`headIsOneOf`, `tripleBodyParts?`, `relTripleBodyParts?`, etc. in
  `Registry.lean`) may need to grow new cases. All of these live in a
  clearly-marked `Preprocessed-body head matchers` section.
- **`Sym.Simp.Theorem` field renames / `mkTheoremFromDecl` moves**. We do
  *not* call `mkTheoremFromDecl` today (the dispatcher works off the
  `Sym.DiscrTree` alone). When the deferred `vcgen`/`SymM` bridge lands,
  this is where we'll need to pick the bundle back up; until then this
  churn class is no-op for us.
- **`SpecProof` variants**. We only use `.global` today. If core splits or
  merges variants, `VCSpecEntry.declName?` / `WpStepEntry.declName?` plus
  the matching `MetaM` inserts need to be adjusted.
- **`registerSimpleScopedEnvExtension` purity**. `addEntry` is pure today
  and we rely on that in both registries; if it changes, the attribute
  handlers already compute their patterns inside `MetaM` before calling
  `.add`, so the fix is to thread the `MetaM` result differently, not to
  restructure the registry.

The compensating design choices are: keep `Sym`-aware logic contained to the
registry modules (`Registry.lean`, `WpStepRegistry.lean`), prefer the
structural `getMatch` over `isDefEq`, and keep an explicit `TacticM`
fallback path (`rw` / `simp only`) so failures in any single `Sym` lookup
stage degrade gracefully.

### Core WP and the symbolic rewriter boundary

Lean v4.35 provides lattice-generic `Std.WP.WPMonad`, `Triple`, transformer
instances, and `vcgen`. The unary carriers in `Unary/WP/` consume these directly:

- Expectation in `ℝ≥0∞` is the core instance of `OracleComp spec` under
  `[OracleSpec.IsMeasureSpec spec]` (`OracleComp.Quantitative.instWP`), so `wp oa post ⊥`,
  core triples and `vcgen` read expectations without opening a scope.
- `open scoped MeasureProgramLogic.Quantitative` selects measure-backed expectation
  for any lawful monad with `LawfulEvalDistSemantics`. Besides its `WPMonad`, it registers the
  interpretation as a direct `WP` instance (`wpInst`), which outranks core's own direct `Prop`
  instances for monads such as `Option` and `Id` while the scope is open (gotcha 33). Its module is
  `VCVio.ProgramLogic.Unary.WP.Measure`.
- `open scoped OracleComp.Qualitative` selects universal structural reachability.
- `open scoped OracleComp.Probabilistic` selects the restricted algebra on `Set.Iic 1`.

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

VCVio's probability/coupling tactics continue to consume `@[vcspec]` and `@[wpStep]`.
Core `vcgen` consumes the core `@[spec]` catalogue. Generic transformer WP comes from
core and PolyFun's WriterT interpretation; VCVio retains its probability rules and
existing transformer equality lemmas. The scoped `WriterT.MonoidWP` interpretation
uses multiplication; append-based logs use `WriterT.toWPMonad` with explicit operations.

The handler specifications are core triples under the structural reading, proved and composed
by core `vcgen` (`Unary/HandlerSpecs.lean`); `Unary/StdDoBridge.lean` remains a narrow bridge to
core's older `Std.Do` SPred API. Replacing the probability tactic's `rw` dispatcher with `Sym.Simp` needs a
separate proof-application adapter and evidence from the existing automation tests.

Core `vcgen` is experimental in v4.35: a module that calls it acknowledges this with
`set_option experimental.vcgen true`, and `VCVioTest/ProgramLogic/CoreWP.lean` pins the
diagnostic once. `mvcgen` is deprecated in favour of `vcgen`, so program-level reasoning uses core
`Std.WP` triples. Exception postconditions form stacks written `EStack⟨A, B⟩` (values
`estack⟨a, b⟩`); an `OptionT` layer contributes `Unit → Pred`, an `ExceptT ε` layer `ε → Pred`.

For the next release, track the
[`WP.trans` renames](https://github.com/leanprover/lean4/pull/15171), the move of `vcgen`'s syntax
to `Std.WP.Tactic` with the deprecation of the `Std.Do` proof mode
([#15290](https://github.com/leanprover/lean4/pull/15290)), and exception-channel frames
([#15067](https://github.com/leanprover/lean4/pull/15067)), alongside the
[upstream roadmap](https://lean-lang.org/fro/roadmap/y4-1/).
