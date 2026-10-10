# Converting Downstream Code to Measure-Based Probability

VCVio's probability semantics are Mathlib measures: `𝒟[mx]` is the output measure of a
computation and `Pr{x ← mx}[p x]` is the mass of an event. The discrete surface —
`SPMF`, `evalSPMF`/`𝒮[…]`, `probOutput`/`probEvent`/`probFailure` with the `Pr[…]` notation, and
the classes that interpret them — is deprecated and is being removed. This guide is the
conversion path for code that builds on VCVio. Most of it is mechanical: find the legacy form in
the tables below, write the native form, and use the symptom table for what remains.

For proof strategies (bind congruence, common-prefix bounds, coupling, total variation) see the
*Standard proof conversion* table in `docs/design/measure-conversion-roadmap.md`. The design
record is `docs/reading/denotational-probability-semantics.md`.

## Quick path

1. Repin VCVio.
2. Run the codemod over your sources, from the VCVio checkout Lake placed in your project:
   `python3 .lake/packages/VCVio/scripts/migrate-native-probability.py <source directories>`
   (`--dry-run` prints the diff instead of writing). It rewrites what the tables below convert
   mechanically: legacy events and `let` items in `Pr{…}`, `GameEquiv` and `≡ₚ`, oracle
   answer-type binders, the spec classes, renamed declarations, and imports of removed modules.
   Every site it leaves is reported as `path:line:` with the entry of this guide that converts
   it; for the most used discrete lemmas the report names the native analogue.
3. Build. Work through the reported sites and the remaining errors with the *Symptoms* table.
4. Check that definitions fix their σ-algebras (see *Semantic contract*).

The codemod is textual: it never needs a build and is idempotent, so it can be rerun after a
further repin. It does not convert proofs; a proof that computed with `probOutput` sums, `SPMF`
equalities or `tvDist` follows the *Standard proof conversion* table of the roadmap.

## Notation and definitions

| Legacy | Native |
|---|---|
| `Pr[p \| mx]` | `Pr{x ← mx}[p x]` |
| `Pr[= x \| mx]` | `Pr{mx}[= x]`; or `𝒟[mx] {x}` when the output has measurable singletons |
| `Pr[⊥ \| mx]` | `1 - Pr{_ ← mx}[True]`; identically `0` for `OracleComp` |
| `Pr{let x ← mx}[p x]` | `Pr{x ← mx}[p x]`; the `let` form still parses, and items are separated by `;` |
| `evalSPMF mx`, `𝒮[mx]` | `𝒟[mx]` |
| `tvDist mx my` | `measureETVDist mx my`; `Measure.etvDist` on measures |
| `expectedValue mx f` | `∫⁻ x, f x ∂𝒟[mx]` |
| `NeverFail mx` | nothing on `OracleComp`; `IsProbabilityMeasure 𝒟[mx]` for failing monads |
| `RelTriple'` | `RelTriple` |
| `GameEquiv g₁ g₂`, `g₁ ≡ₚ g₂`, `letI : MeasurableSpace α := ⊤; 𝒟[g₁] = 𝒟[g₂]` | `g₁ =ᵈ g₂` (`EvalDistEq`); `EvalDistEq.of_evalDist_eq` and `evalDistEq_iff_evalDist_eq` relate it to output measures |

## Classes and binders

| Legacy | Native |
|---|---|
| `[IsProbabilitySpec spec]` | `[OracleSpec.IsMeasureSpec spec]` |
| `[IsUniformSpec spec]` | `[OracleSpec.IsUniformMeasureSpec spec]`, plus `[Fintype (spec.Range t)]` where a cardinality appears |
| `[∀ t, MeasurableSpace (spec.Range t)]`, `[∀ t, DiscreteMeasurableSpace (spec.Range t)]` | delete them: answer measures live on the discrete σ-algebra |
| `OracleSpec.addRangeMeasurableSpace`, `OracleSpec.addRangeDiscreteMeasurableSpace` | delete them; no replacement is needed |
| `IsUniformSpec.ofFintypeInhabited spec` | `IsUniformMeasureSpec.ofFiniteNonempty spec`, as a local instance; it needs only `Finite` and `Nonempty` answers |
| `PFunctor.IsProbabilitySpec`, `PFunctor.IsUniformSpec` | `PFunctor.IsMeasureSpec`, `PFunctor.IsMeasureSpec.uniformOfFiniteNonempty` |
| `EvalDistCompatible`, `DiscreteEvalDistCompatible` | operational support lemmas and the `𝒟` equations; no class |

`unifSpec` and `coinSpec` carry global uniform measure instances. For a concrete specification
whose answer types are abstract, such as `unifSpec + (Unit →ₒ Chal)` with `[Fintype Chal]
[Inhabited Chal]`, declare
`local instance : IsUniformMeasureSpec (Unit →ₒ Chal) := .ofFiniteNonempty _` on the component
once per file. The sum then gets its instance from `IsUniformMeasureSpec.add`. Do not declare an
instance on the sum itself, since it would compete with that one.

## Query and handler laws

| Legacy | Native |
|---|---|
| `evalDist_liftM_query : 𝒟[liftM (query t)] = toMeasure t` | `evalDist_liftM_query` gives `(toMeasure t).trim le_top` in any measurable structure on the answer; `MeasureTheory.trim_eq_self` removes the trim under `⊤` (including `Bool`, `Fin n`) |
| `simp [evalDist_liftM_query, toMeasure_singleton]` for `𝒟[liftM (query t)] {u}` | `simp` with the simp lemmas `evalDist_liftM_query_apply` and `IsUniformMeasureSpec.toMeasure_singleton` |
| `evalDist_liftM_query_eq_uniformOn_top` | `evalDist_liftM_query_uniform`, in any measurable structure; `evalDist_liftM_unifSpec_query` and `evalDist_liftM_coinSpec_query` for the built-in specifications |
| `evalDist_simulateQ_run_congr_of_forall` | `evalDist_simulateQ_run_congr` with `=ᵈ` step facts; `evalDistEq_simulateQ_run` for the equality in distribution itself |
| `evalDist_liftComp_of_evalDist`, `wp_liftComp_of_evalDist` | `evalDist_liftComp_of_evalDistEq`, `wp_liftComp_of_evalDistEq` |
| per-query hypotheses `𝒟[impl t] = 𝒟[liftM (query t)]` or `𝒟[(h q).run s] = 𝒟[(h' q).run s]` (`evalDist_simulateQ_congr`, `wp_simulateQ_eq`, `wp_simulateQ_run'_eq`, `evalDist_simulateQ_run'_eq_of_forall`, `MeasureDistEquiv.of_step`, `of_step_bij`, `parSum_congr`) | the same statements with `=ᵈ`, which need no measurable space on answers or states |

To reuse an existing per-query measure equality `h` proved for an arbitrary measurable structure,
supply `fun q s => by let : MeasurableSpace (spec.Range q × σ) := ⊤; exact
EvalDistEq.of_evalDist_eq (h q s)`. Restating the step lemma with `=ᵈ` is better: its
statement then needs no measurable space at all.

## Lemma names

Native lemmas keep the legacy name with the probability head replaced:

| Legacy name part | Native name part | Example |
|---|---|---|
| `probEvent_` | `prEvent_` | `le_probEvent_isSome_contextFork` → `le_prEvent_isSome_contextFork` |
| `probOutput_` | `prEvent_` or `evalDist_` | `IND_CPA_Game_probOutput_eq_branch` → `IND_CPA_Game_evalDist_eq_branch` |
| `evalSPMF_` | `evalDist_` | `evalSPMF_simulateQ_run_congr` → `evalDist_simulateQ_run_congr` |
| `tvDist_` | `measureETVDist_` | `tvDist_simulateQ_le_probEvent_bad` → `measureETVDist_simulateQ_run'_le_prEvent_bad` |

Other renames: `AdvBound.of_tvDist` → `AdvBound.of_measureETVDist` (and `AdvBound` takes an
`ℝ≥0∞` bound); root `evalDist_uniformSample` → `SampleableType.evalDist_uniformSample`;
`relTriple_eqRel_of_evalSPMF_eq` → `relTriple_eqRel_of_evalDistEq`;
`evalSPMF_eq_of_relTriple_eqRel` → `evalDistEq_of_relTriple_eqRel`; in the identical-until-bad
family `_plus_probEvent_bad` → `_add_prEvent_bad` (for example
`advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv_preserved`) and `tvDist_simulateQ_…` →
the `measureETVDist_simulateQ_run…` twins in `Relational/SimulateQ/UntilBad.lean`.

Statements of equality in distribution now use `=ᵈ`:
- `prEvent_congr_of_evalDist_eq mx my h p` → `(EvalDistEq.of_evalDist_eq h).prEvent_eq p`;
- `evalDist_bind_congr_of_evalDist_eq mx my h f` → `((EvalDistEq.of_evalDist_eq h).bind_left f).evalDist_eq`;
- `evalDist_map_congr_of_evalDist_eq mx my h f` → `((EvalDistEq.of_evalDist_eq h).map f).evalDist_eq`;
- lemmas named `…_of_evalDist_eq` whose hypothesis was a discrete measure equality become
  `…_of_evalDistEq`, e.g. `relTriple_of_evalDistEq_left`, `support_eq_of_evalDistEq`,
  `measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq`;
- lemmas whose conclusion was one become `evalDistEq_…`, e.g. `evalDistEq_generateSeed_of_countEq`,
  `evalDistEq_of_forall_prEvent_eq_output`, `SampleableType.evalDistEq_uniformSample_vector_succ`;
- `AdvBound.of_gameEquiv` → `AdvBound.of_evalDistEq`.

## Converted theorem families

These families changed statement shape as well as names. The codemod renames the declarations;
callers restate the hypotheses they supply.

| Family | Legacy statement | Native statement |
|---|---|---|
| `SigmaProtocol.HVZK`, `IdenSchemeWithAbort.HVZK` | `ζ_zk : ℝ` with `0 ≤ ζ_zk`, and `tvDist real sim ≤ ζ_zk` | `ζ_zk : ℝ≥0∞`, and `measureETVDist real sim ≤ ζ_zk` on the discrete transcript σ-algebra; the nonnegativity hypothesis goes |
| `PerfectHVZK` | `𝒮[real] = 𝒮[sim]` | `real =ᵈ sim`; `perfectHVZK_iff_hvzk_zero` relates it to `HVZK … 0` |
| `simCommitPredictability` | `Pr[= c₀ \| Prod.fst <$> simT x] ≤ β` | `Pr{t ← simT x}[t.1 = c₀] ≤ β` |
| Fiat–Shamir CMA-to-NMA loss (`euf_cma_to_nma`, `euf_cma_bound`) | `ENNReal.ofReal (qS * ζ_zk)` | `qS * ζ_zk` |
| Charged steps of the per-query slack bounds (`expectedQuerySlack`, `advantage_le_expectedQuerySlack_add_prEvent_bad` and its variants) | `ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤ ε s` | `letI : MeasurableSpace (E.Range t × σ × Bool) := ⊤; measureETVDist … ≤ ε s` |
| Uncharged steps of the same bounds | `∀ p, (h₀ t).run p = (h₁ t).run p` | `∀ s, (h₀ t).run (s, false) = (h₁ t).run (s, false)`: only good states are compared |
| `expectedQuerySlack` step | `∑'`-weighted continuation | the unary expectation `wp` of the continuation |

The Fiat–Shamir extraction bounds `nma_to_hard_relation_bound`, `euf_nma_bound` and
`euf_cma_bound` no longer take the extractor-failure hypothesis `hss_nf`, which holds for every
`OracleComp`; drop that argument at call sites. Their conclusions and `Fork.advantage` are
`Pr{…}[= true]` events.

For an aborting identification scheme whose loss is a real-valued formula, keep `ζ_zk : ℝ` and
pass `ENNReal.ofReal ζ_zk` to `HVZK`, as `FiatShamirWithAbort.euf_cma_bound` does.

## Modules

| Removed module | Import instead |
|---|---|
| `VCVio.OracleComp.QueryTracking.LoggingOracle` | `VCVio.OracleComp.QueryTracking.LoggingOracle.Core` |
| `VCVio.OracleComp.QueryTracking.CountingOracle` | `VCVio.OracleComp.QueryTracking.CountingOracle.Core` |
| `VCVio.OracleComp.QueryTracking.Tracing` | `VCVio.OracleComp.QueryTracking.Tracing.Core` |
| `VCVio.OracleComp.SimSemantics.QueryImpl.Constructions` | `VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core` |
| `VCVio.OracleComp.SimSemantics.StateT.Basic` | `VCVio.OracleComp.SimSemantics.StateT.Basic.Native` |
| `VCVio.OracleComp.Coercions.Add` | `VCVio.OracleComp.Coercions.Add.Basic` |
| `VCVio.OracleComp.Constructions.Fork` | `VCVio.OracleComp.Constructions.Fork.Basic` |
| `VCVio.CryptoFoundations.ForkMeasure` | `VCVio.CryptoFoundations.ReplayFork`, `VCVio.CryptoFoundations.SeededFork` |
| `VCVio.CryptoFoundations.SymmEncAlg.MeasureCompatibility` | `VCVio.CryptoFoundations.SymmEncAlg` |
| `VCVio.EvalDist.TVDist`, `VCVio.EvalDist.MeasureTVDist` | `VCVio.EvalDist.MeasureTVDist.Basic` (with `.Bind` and `.Event` for composition rules) |
| `VCVio.EvalDist.TVDist.Positivity` | `VCVio.EvalDist.MeasureTVDist.Positivity` (`positivity` on `measureTVDist`) |
| `VCVio.ProgramLogic.Relational.SimulateQ.Epsilon` | `VCVio.ProgramLogic.Relational.SimulateQ.UntilBad` |
| `VCVio.StateSeparating.DistEquiv` | `VCVio.StateSeparating.MeasureDistEquiv` |
| `VCVio.StateSeparating.Advantage` | `VCVio.StateSeparating.Advantage.Measure` |
| `VCVio.EvalDist.Monad.Disagreement` | `VCVio.EvalDist.Monad.Disagreement.Measure` |
| `VCVio.EvalDist.Instances.FinRatPMF`, `ToMathlib.ProbabilityTheory.FinRatPMF.PMF` | `ToMathlib.ProbabilityTheory.FinRatPMF.Measure` |
| `VCVio.EvalDist.Instances.ReaderT` | `VCVio.EvalDist.MeasureSemantics` (`readerTKernel`) |
| `VCVio.EvalDist.Defs.Semantics` | `VCVio.EvalDist.MeasureSemantics` |
| `ToMathlib.ProbabilityTheory.Coupling`, `ToMathlib.ProbabilityTheory.OptimalCoupling` | `ToMathlib.MeasureTheory.Measure.Coupling`, `ToMathlib.MeasureTheory.Measure.Coupling.Maximal` |
| `VCVio.ProgramLogic.Relational.Measure.Oracle` | `VCVio.ProgramLogic.Relational.Basic` |
| `VCVio.ProgramLogic.Relational.SimulateQ.Basic` | `VCVio.ProgramLogic.Relational.SimulateQ.Coupling`, `VCVio.ProgramLogic.Relational.SimulateQ.UntilBad` |
| `VCVio.ProgramLogic.Relational.WP.Coherence` | `VCVio.ProgramLogic.Relational.WP.Quantitative` |
| `VCVio.Prelude` | the modules it re-exported, e.g. `VCVio.Prelude.Core` |

A removed module may have re-exported legacy hubs; add the imports the build then asks for.
`import VCVio.Native` is a PMF-free entry point for the native foundations.

## Symptoms

| Symptom | Fix |
|---|---|
| failed to synthesize `OracleSpec.IsMeasureSpec spec` | add the binder from *Classes and binders*, or the local instance for a concrete specification |
| failed to synthesize `MeasurableSpace (spec.Range t)` inside a proof | `let : MeasurableSpace (spec.Range t) := ⊤` (use `let`, not `letI`, in a proposition-valued goal); in a statement, state the fact with `=ᵈ` or `Pr{…}[…]`, or take `{_ : MeasurableSpace (spec.Range t)}` |
| `rw`/`simp` does not find a query law such as `evalDist_liftM_query_apply` when the answer type appears reduced (`Bool` rather than `spec.Range t`) | name the specification: `evalDist_liftM_query_apply (spec := S) t hs` |
| two instances for a sum specification disagree (e.g. a local `IsUniformMeasureSpec (A + B)`) | declare the local instance on the components and let `IsMeasureSpec.add` build the sum |
| failed to synthesize `MeasurableSingletonClass α` for `𝒟[mx] {x}` | state the event as `Pr{mx}[= x]` |
| `rw` fails on a `𝒟[…]` term whose measurable-space instance is equal but spelled differently (e.g. Mathlib's `Fin` instance against a local `⊤`) | close with `exact`, `.trans` or `convert`, which unify up to definitional equality |
| a goal shows `(toMeasure t).trim le_top` | `MeasureTheory.trim_eq_self` when the answer's measurable space is `⊤` by definition; otherwise evaluate measurable sets with `evalDist_liftM_query_apply` or `trim_measurableSet_eq` |
| two events that should agree differ only in how their binds and maps are arranged | `simp only [prEvent_norm]` brings both into the normal form of `Pr{…}[…]` |
| a lemma about `Pr{y ← mx >>= f}[q y]` no longer matches after `simp` pushed the event into the bind | apply the lemma before `simp`, or state it for `prEvent (mx >>= g)` with `g : α → m Prop` |
| a proof relied on `Pr{…}[…]` unfolding to `𝒟[… >>= fun x => pure …] {True}` | `simp only [prEvent_def, map_eq_bind_pure_comp, Function.comp_def]` recovers that form; better, use the laws keyed on `prEvent` |
| `simp [prEvent_def]` loops | `simp` rewrites `𝒟[mx] {True}` back to `prEvent mx`; use `rw [prEvent_def]` or `simp only` |
| `rw` does not find an event lemma whose selector's type depends on an implicit argument | supply that argument, e.g. the query index: `rw [prEvent_liftM_query_eq_card_div t]` |
| `simp only [f]` leaves a partially applied predicate `f a b` in an event | the event selector is eta-reduced; `unfold f` instead |
| an event selector `p ∘ f` does not match `fun x => p (f x)` | the selector is eta-reduced; `simp only [Function.comp_def]` |
| an event computation that destructures its input (`let (a, b) ← mx` in a `do` block) stays in bind form, so `prEvent_mono` does not apply | `prEvent_bind_mono_of_support _ _ _ fun ⟨a, b⟩ _ => prEvent_pure_mono h`, or `prEvent_bind_congr_of_support` for equalities |
| `prEvent_le_one mx p` no longer applies | it takes the event computation alone: `prEvent_le_one _` |
| `simp` leaves `Pr{a ← mx; b ← f a}[True]` (or `[False]`) on `OracleComp` | `simp` pushes the constant selector into the binds; `simp [-map_bind]` keeps it outside, where `OracleComp.prEvent_true_eq_one` and `prEvent_false` apply |
| laws about `pure` (`prEvent_pure`, `map_pure`) do not fire on `pure v` written with an `OracleComp` ascription | that `pure` elaborates through `PFunctor.FreeM.instPure` rather than the monad; `erw [prEvent_pure]`, or state the term through the `do` block that produced it |
| measurability hypotheses of the `_ae` and `lintegral` event laws | they take the map form `Measurable fun x => 𝒟[p <$> f x]` |
| an event transported between monads (`ProbComp` and `OracleComp spec`) | take `.prEvent_eq p` of an equality in distribution such as `uniformSampleImpl.evalDistEq_simulateQ` or `OracleComp.evalDistEq_liftComp_uniform` |
| `x ∈ support mx ↔ 0 < mass` needs a uniform specification | use `mem_support_iff_evalDist_singleton_pos_of_fullSupport` with a full-support hypothesis for other answer measures |
| probability one from reachability | `prEvent_eq_one_of_forall_mem_support`; the converse `prEvent_eq_one_iff` needs uniform answers |
| heartbeat timeout on raw `PFunctor.FreeM` terms | normalize with `FreeM.bind_eq_bind`, `FreeM.map_eq_map`, `FreeM.pure_eq_pure`, or state the helper at the `OracleComp` level |
| deprecation warning `VCVio retiring probability API: use …` | follow the named replacement |

## Semantic contract

- **Fix σ-algebras inside definitions.** A definition stated with `𝒟[…]` depends on the
  measurable space its caller supplies; under `⊥` an equality of measures says nothing. Security
  definitions state equality in distribution with `=ᵈ`, which needs no measurable space, as
  `SymmEncAlg.ciphertextRowsEqualAt` does. A definition about the measures themselves puts
  `letI : MeasurableSpace α := ⊤` inside, as `PerfectlyHiding` and `SymmEncAlg.perfectSecrecyAt`
  do.
- **Events need no measurable space; singletons do.** `Pr{…}[…]` works on any output type,
  while `𝒟[mx] {x}` needs measurable singletons.
- **Support is operational.** `support mx` is the set of structurally reachable outputs. It
  coincides with the positive-mass outputs only when every answer has positive mass, which the
  uniform specifications provide.
- **Discrete answers.** `OracleSpec` answer measures live on the discrete σ-algebra, so
  oracle programs carry no measurable-space hypotheses on answers. Continuous answer measures
  belong at the `PFunctor.FreeM` level, where `PFunctor.IsMeasureSpec` takes any measurable
  structure.
