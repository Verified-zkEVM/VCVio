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

- `Examples/ProgramLogic/UnaryStep.lean`: unary `pvcstep` / `pvcgen` examples.
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

### Quantitative VCGen (`pvcgen`)

VCVio's unary tactics are `pvcgen` and `pvcstep`, the probabilistic counterparts of the relational
`rvcgen` and `rvcstep`. Core Lean's `vcgen` is a separate tactic under its own name: it walks
`Std.WP` triples of any program type through the core `@[spec]` catalogue and leaves verification
conditions in the assertion lattice, and it is the tool for `Prop`-valued triples such as the
handler specifications under `OracleComp.Qualitative` (see *Handler `@[spec]` catalog* below).
`pvcgen` / `pvcstep` add what core does not provide: lowering of `Pr{…}[…]` goals, quantitative
`wp` and expectation reasoning, bind-swap and congruence on probability equalities, oracle-query
and `simulateQ` rules, support and indicator leaf closure, and the `@[vcspec]` / `@[wpStep]`
registries. Both are in scope after `import VCVio`; a bare `vcgen` always elaborates core's
tactic, which `VCVioTest/ProgramLogic/VCGenNames.lean` pins.

`pvcgen` is the primary unary tactic for new proofs. It accepts core triples
`⦃ pre ⦄ oa ⦃ post ⦄` (`Std.WP.Triple oa pre post ⊥`, from `open scoped Std.WP`) and
probability goals, automatically lowering `Pr{...}[...]` events into the quantitative engine.
For `OracleComp` the triple reads expectations: `Std.WP.Triple.iff` unfolds it to
`pre ⊑ wp oa post ⊥`, which is `pre ≤ wp⟦oa⟧ post`. Core supplies the generic rules
(`Std.WP.Triple.intro`, `.le_wp`, `Std.WP.Spec.pure`, `Std.WP.Triple.bind`,
`Std.WP.Triple.entails_wp_of_pre_post`); `Unary/HoareTriple.lean` adds the quantitative
ones (`triple_conseq`, `triple_bind_wp`, `triple_zero`, `triple_ite`, `triple_dite`, the
`replicate` / `List.foldlM` / `List.mapM` stepping and invariant rules, and the event triples
`triple_prEvent_indicator`, `triple_prEvent_eq_one`, `triple_support`).

| Tactic | What it does |
|--------|--------------|
| `pvcgen` | Exhaustively decomposes a core triple or probability goal with spec-aware stepping, loop invariant auto-detection, and support/indicator leaf closure |
| `pvcstep` | One step: probability lowering → bind → conditional → match → loop → leaf |
| `pvcstep?` | Performs one step and emits the corresponding explicit script, often surfacing `as ⟨...⟩`, `using cut`, `inv I`, or `with theorem` |
| `pvcgen?` | Runs `pvcgen` and emits the planned step replay across each pass |
| `pvcstep using cut` | Explicit intermediate postcondition for a bind step |
| `pvcstep with thm` | Force one explicit unary theorem/assumption step |
| `pvcstep as ⟨x, hx⟩` | Explicit names for binders introduced by the current step |
| `pvcstep inv I` | Explicit loop invariant for `replicate`/`foldlM`/`mapM` |
| `pvcstep rw` | One explicit top-level bind-swap rewrite on a probability equality |
| `pvcstep rw under n` | One bind-swap rewrite under `n` shared outer bind prefixes |
| `pvcstep rw normalize` | Run the bounded probability-equality planner explicitly |
| `pvcstep rw congr` | Expose one or more shared binds plus their support hypotheses |
| `pvcstep rw congr'` | Expose one or more shared binds without support hypotheses |
| `exp_norm` | Normalize indicator (`propInd`) and expectation (`wp`) arithmetic |

**Probability-goal handling**: `pvcgen` and `pvcstep` automatically handle four
classes of probability goals:

1. **`Pr{...}[...] = 1` lowering** → rewrites into triple form for structural decomposition:
   - `Pr{let x ← oa}[p x] = 1` → `⦃ 1 ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄`; a singleton output
     `Pr{let y ← oa}[y = x]` is the event `p := (· = x)`

2. **Lower-bound event goals** → stay inside unary VCGen by reusing the same triple shell:
   - `r ≤ Pr{let x ← oa}[p x]` / `Pr{let x ← oa}[p x] ≥ r` → `⦃ r ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄`

3. **Probability equalities** (`Pr{...}[...]`, applied `𝒟[...]` masses, or output measures):
   - Plain `pvcstep` first normalizes common `map`/`bind` surface syntax (`map_eq_bind_pure_comp`,
     `bind_assoc`), then preview-selects the best bounded swap/congruence plan from the fast path
   - `pvcstep rw` performs exactly one top-level bind-swap rewrite
   - `pvcstep rw under n` rewrites one swap beneath `n` shared outer bind prefixes
   - `pvcstep rw normalize` runs the deeper bounded planner used for explicit suggestions
   - `pvcstep rw congr` / `pvcstep rw congr'` expose one or more shared binds explicitly
   - Swaps use `OracleComp.wp_swap` on events and expectations
     and `OracleComp.evalDist_bind_bind_swap` on output measures (countable responses), or their
     `_of_uniform` variants; a swap under shared draws descends through the expectations of the
     event's normal form. Congruence uses `wp_congr_of_support` /
     `OracleComp.evalDist_bind_apply_congr_of_support`, leaving the continuations on the
     structural support of the shared prefix

4. **Other general `Pr{...}[...]` goals** → rewrite to raw `wp` form and keep stepping structurally
   when a `wp` rule applies. On an already-lowered raw-`wp` goal, `pvcstep?` / `pvcgen?`
   will explicitly note that they are continuing in raw `wp` mode.

**Loop invariants**: `pvcgen` auto-detects `replicate`, `List.foldlM`, and `List.mapM`
in triple goals and applies matching invariant hypotheses from context.
Use `pvcstep inv I` to provide an explicit invariant.

**Support-sensitive leaf closure**: `pvcgen` final pass tries `triple_support`,
`triple_propInd_of_support` and `triple_prEvent_eq_one`
in addition to the standard `Std.WP.Spec.pure`, `triple_zero`, and consequence search.

**Naming and suggestions**: plain `pvcstep` / `rvcstep` keep the stable execution path.
The `?` variants run a planner-backed version of the same next move and emit a concrete
`Try this` script, typically surfacing an explicit `using ...` hint, `inv I`, `with theorem`,
or `as ⟨...⟩` clause that you can paste back into the proof. On probability-equality goals the
planner may emit a grouped multi-step replay when the best explanation is an explicit rewrite chain.

**Opt-in unary lookup**: mark a unary core triple or raw `wp` theorem with `@[vcspec]` to register it for
bounded head-symbol lookup. This is intentionally narrow: after the built-in structural step and
explicit hint opportunities, `pvcstep` / `pvcgen` consult only `@[vcspec]` theorems whose
computation head matches the current goal. Use `pvcstep with myLemma` when you want to force
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
handlers, or state-transformer maps; then continue with `pvcstep`, `rvcstep`,
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

**Pass budget**: exhaustive `pvcgen` / `rvcgen` runs are bounded by
`set_option vcvio.vcgen.maxPasses <n>`. The default is conservative so large proofs stay
predictable; if you intentionally want a longer exhaustive run, raise the option locally around
that proof.

**Trace output**: set `set_option vcvio.vcgen.traceSteps true` to log the chosen planned step,
goal delta, and any planner alternatives that were previewed while debugging tactic choice.

### Raw WP Tactics

Raw `wp` goals (`_ ≤ wp _ _`) now use the same unary entrypoints rather than a separate tactic
family. `pvcstep` performs one decomposition step and `pvcgen` keeps stepping exhaustively.


### Probability Equality Control

All probability-equality control now lives under `pvcstep`.

| Tactic | What it does |
|--------|--------------|
| `pvcstep` | Fast dispatcher for common probability-equality steps: syntax normalization, swap, congruence, and bounded compositions chosen by preview |
| `pvcstep rw` | Rewrites one top-level bind swap without trying to close the goal |
| `pvcstep rw under n` | Rewrites one bind swap under `n` shared outer bind prefixes on one side |
| `pvcstep rw normalize` | Runs the bounded probability-equality planner explicitly, without broadening plain `pvcstep` |
| `pvcstep rw congr` | Reduces `Pr{let y ← mx >>= f₁}[q y] = Pr{let y ← mx >>= f₂}[q y]` to a pointwise goal, auto-introducing `x` and `hx : x ∈ support mx`; the explicit `as ⟨...⟩` form can peel multiple shared binds at once |
| `pvcstep rw congr'` | Same, but without the support restriction; the explicit `as ⟨...⟩` form can peel multiple shared binds at once |

### Automation

| Tactic | What it does |
|--------|--------------|
| `rvcgen` | Exhaustive relational VCGen over all open goals, with automatic lowering from `=ᵈ` / output-measure equality and cheap leaf closure |
| `rvcfinish` / `rvcgen!` | Opt-in residual search and consequence closing |
| `rel_dist` | Turns `RelTriple oa ob (EqRel α)` into `oa =ᵈ ob` |

## Probability Equality Guide

### What plain `pvcstep` handles

On probability equalities, plain `pvcstep` already tries the common bind-swap and
bind-congruence patterns:

1. **Direct event equalities**: `Pr{let z ← mx >>= ... >>= ...}[q z] = Pr{let z ← my >>= ... >>= ...}[q z]`
2. **Nested bounded rewrites**: automatically peels small shared-bind prefixes and prefers a
   closing swap/congruence plan when one is available
3. **Surface `map` wrappers**: normalizes the common `map_eq_bind_pure_comp` / `bind_assoc` shape
   before searching for swaps or congruence

### When to use the explicit `rw` subcommands

- **Need to keep going after a swap**: use `pvcstep rw`
- **Need to swap below shared outer binds**: use `pvcstep rw under n`
- **Need the bounded planner to choose a swap/congruence chain now**: use `pvcstep rw normalize`
- **Need to expose one or more common outer binds with support information**: use `pvcstep rw congr`
- **Need the support-free congruence variant**: use `pvcstep rw congr'`
- **Need the full explicit replay for a bounded nested swap**: use `pvcstep?`
- **Need a deeper swap than the current bounded automation knows**: peel outer layers manually, or
  use `pvcstep?` to see the best bounded replay the planner found before finishing the rest by hand

### Key insight: events vs output measures

The underlying bind-swap lemmas are `OracleComp.prEvent_bind_bind_swap` for events and
`OracleComp.evalDist_bind_bind_swap` for output measures. A point mass `Pr{let y ← oa}[y = x]` is the event
`(· = x)`, and `Pr{…}[…]` elaborates its final draw as a map, so the `pvcstep`
probability-equality machinery normalizes with `map_eq_bind_pure_comp` / `bind_assoc` before
matching either shape.

### Patterns

**Standalone swap**:
```lean
pvcstep
```

**Rewrite one swap and continue**:
```lean
pvcstep rw
```

**Rewrite under one shared bind**:
```lean
pvcstep rw under 1
```

**Run the bounded probability-equality planner explicitly**:
```lean
pvcstep rw normalize
```

**Expose one common bind with support information**:
```lean
pvcstep rw congr
exact h _ ‹_›
```

**Expose one common bind without support information**:
```lean
pvcstep rw congr'
rename_i x
```

**Expose two shared binds explicitly at once**:
```lean
pvcstep rw congr' as ⟨x, y⟩
```

## Core `vcgen` on oracle computations

Core's `vcgen` (`set_option experimental.vcgen true`) decomposes a core triple
`⦃ pre ⦄ oa ⦃ post ⦄` with the `@[spec]` rules registered for the program's parts and leaves
verification conditions in the assertion lattice. `OracleComp spec` has four readings, one per
kind of statement about its outcomes:

| Reading | Scope | Carrier | `⦃ pre ⦄ oa ⦃ post ⦄` states | Rules |
|---------|-------|---------|-------------------------------|-------|
| structural (necessary) | `OracleComp.Qualitative` | `Prop` | every possible output satisfies `post` | `Unary/WP/QualitativeSpecs.lean` |
| angelic (possible) | `OracleComp.Angelic` | `Prop` | some possible output satisfies `post` | `Unary/WP/Angelic.lean` |
| expectation lower bound | global instance | `ℝ≥0∞` | `pre ≤ wp⟦oa⟧ post` | `Unary/WP/QuantitativeSpecs.lean` |
| expectation upper bound | `OracleComp.Upper` | `ℝ≥0∞ᵒᵈ` | `wp⟦oa⟧ post ≤ pre` | `Unary/WP/Upper.lean` |

The upper-bound reading is PolyFun's `ExactWPMonad.dual` of the expectation reading: the same
interpretation over the order duals, so core's `vcgen`, transformer rules and loop invariants
decompose upper bounds unchanged. Core's assertion types are output parameters, so one reading is
live per program type in a scope: under the structural scope, a triple with an `ℝ≥0∞`
precondition no longer elaborates, and a triple of one reading cannot be decomposed with another
reading's scope open. Each reading also registers a per-call scope at priority `1200`
(`OracleComp.Qualitative.Dispatch`, `OracleComp.Angelic.Dispatch`,
`OracleComp.Quantitative.Dispatch`, `OracleComp.Upper.Dispatch`), above every reading a file
opens, with a direct `WP` instance as well (gotcha 33): `open scoped OracleComp.Upper.Dispatch in
vcgen` runs `vcgen` in that reading whatever the file opens. `Pr{…}[…]` is unaffected by the
scopes. `prvcgen` (below) chooses the reading from the goal.

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
classifies a statement about the outcomes of an oracle computation, rewrites it with the bridge of
its reading, and runs core `vcgen` in that reading's per-call scope:

| Goal | Reading |
|------|---------|
| `Pr{…}[p] = 1` (uniform answers), `∀ x ∈ support oa, p x` | structural |
| `0 < Pr{…}[p]` (uniform answers), `∃ x ∈ support oa, p x` | angelic |
| `r ≤ Pr{…}[p]`, `Pr{…}[p] ≥ r` | expectation lower bound |
| `Pr{…}[p] ≤ ε`, `Pr{…}[p] = 0` | expectation upper bound |
| `Pr{…}[p] = c` | both bounds, by `le_antisymm` |
| an angelic or structural `wp oa post ⊥` | continued in its reading |

`𝔼{…}[g]` and `wp⟦oa⟧ g` stand wherever `Pr{…}[p]` does, and an equation may have the expectation
on either side. `prvcgen [rules] invariants … with step` forwards its arguments to `vcgen`;
`prvcgen => tac` runs `tac` in the reading's scope in place of `vcgen`. The verification
conditions of the expectation readings are read back into `ℝ≥0∞`, and those that the range of an
indicator settles are closed. A comparison `Pr{A}[p] ≤ Pr{B}[q]` is read as an upper bound on the
left-hand side with the right-hand side as the bound.

Equations. `= 0` is the upper bound alone. `= 1` uses the structural bridge when uniform answers
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
  game hop: `prvcgen` fails and points to `pvcstep` / `pvcgen`, the couplings `rvcstep` / `rvcgen`,
  and the `=ᵈ` lemmas.

Adding rules for a reading: state the rule as a triple of that reading, in its namespace, with
the precondition built from lattice connectives so that `vcgen` continues through it (gotcha 36):
`Lean.Order.iInf` for every outcome in the lower-bound reading and the largest outcome in the
upper-bound reading (whose `iInf` is the supremum in `ℝ≥0∞`), `∀` in the structural reading, and
`∃` (which `vcgen` does not split) in the angelic reading. Register it with `@[spec]` when it holds
for every call of the program; pass it explicitly (`prvcgen [rule]`) when it needs a hypothesis or
ends the descent, as the averaging rules do. A rule is picked up by `prvcgen` in the reading its
triple is stated in.

Known limits:

- **Sums stop `vcgen`.** `vcgen` splits only lattice connectives (`⊓`, `⇨`, `⌜·⌝`, `⊤`,
  `Lean.Order.iInf`). A precondition written with `∑`, `if`, or `∧` becomes a verification
  condition, and `vcgen` does not descend into the programs inside it. Exact values of queries and
  draws are therefore computed by `simp` on the normal form of `Pr{…}[…]`, and the exact rules
  serve only for the last draw. Rules meant to be stepped through state their preconditions with
  lattice connectives. `Lean.Order.iInf` needs a `Type`-indexed binder, so a support condition is
  indexed by the subtype `{a // a ∈ support oa}`.
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

1. **Plain `pvcstep` may close or progress a probability equality goal**: use
   `pvcstep rw` / `pvcstep rw under n` when you specifically want a rewrite and
   intend to continue.

2. **Import `VCVio.ProgramLogic.Tactics`**: tactics are defined there. If a file only imports `VCVio.ProgramLogic.Notation`, add/change the import.

3. **`game_rule` simp set**: many tactics use `simp only [game_rule]` internally. Ensure relevant `@[simp]` lemmas are in scope.

4. **`rvcstep using R`**: when Lean can't infer the witness for the current relational shape
   (bind cut, bijection, traversal input relation, or simulation invariant), provide it explicitly.

5. **`StdDoBridge` is deliberately narrow**: use it for unary almost-sure `.pure` `Std.Do` experiments, not as the default path for quantitative or relational proofs.

## Internal Architecture (`Sym`-backed Registries)

### Why `Lean.Meta.Sym.*`?

The planner needs to ask "given this `wp⟦comp⟧ post` or `⦃ pre ⦄ comp ⦃ post ⦄`
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
`pvcstep` reports "no matching rule applied" while the corresponding manual
rewrite works).

### Registries and what they index

| File | Attribute | Role |
|------|-----------|------|
| `VCVio/ProgramLogic/Tactics/Common/Registry.lean` | `@[vcspec]` | Unary core `Std.WP.Triple` and relational `RelTriple` / `RelWP` / quantitative `VCVio.ProgramLogic.RelTriple` rules, indexed by a `Sym.Pattern` on the computation slot (`oa` for unary, `oa` with a secondary `rightHead?` filter for relational) |
| `VCVio/ProgramLogic/Tactics/Common/WpStepRegistry.lean` | `@[wpStep]` | Equational `wp⟦comp⟧ post = …` rewrites, indexed by a `Sym.Pattern` on `oa` and consulted by `runWpStepRules` via `TacticM` rewriting (`rw` then `simp only`). The `Sym.Simp.Theorem` bundle for an eventual `SymM`-side rewriter is *not* eagerly built; `Sym.Simp.mkTheoremFromDecl` can rebuild it on demand from `getAllWpStepEntries` |

Each entry carries a `SpecProof` (reusing the core-Lean type from
`Lean.Elab.Tactic.Do.SpecAttr`) so origins can be distinguished between a
global declaration, a local hypothesis, or a raw term. Priorities are parsed
from the attribute's optional priority argument (`@[vcspec (prio := 200)]`).

### Dispatch flow

1. **Unary / relational VC-gen** (`VCVio/ProgramLogic/Tactics/Unary/Internals.lean`,
   `VCVio/ProgramLogic/Tactics/Relational/Internals.lean`): on a `Std.WP.Triple`/`wp`/`RelTriple`/`RelWP`/quantitative
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
| A unary triple lemma usable by `pvcstep` / `pvcgen` | `@[vcspec]` | `⦃ pre ⦄ oa ⦃ post ⦄` or raw `wp⟦oa⟧ post ≥ pre` |
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

VCVio's probability/coupling tactics (`pvcgen`, `pvcstep`, `rvcgen`, `rvcstep`) consume
`@[vcspec]` and `@[wpStep]`. Core `vcgen` consumes the core `@[spec]` catalogue. Generic
transformer WP comes from core and PolyFun's WriterT interpretation; VCVio retains its
probability rules and existing transformer equality lemmas. The scoped `WriterT.MonoidWP`
interpretation uses multiplication; append-based logs use `WriterT.toWPMonad` with explicit
operations.

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
