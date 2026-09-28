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

1. Repin VCVio and fix imports of removed modules (see *Modules*).
2. Replace legacy notation, classes and lemma names using the tables below.
3. Build. Work through the remaining errors with the *Symptoms* table.
4. Check that definitions fix their σ-algebras (see *Semantic contract*).

## Notation and definitions

| Legacy | Native |
|---|---|
| `Pr[p \| mx]` | `Pr{x ← mx}[p x]` |
| `Pr[= x \| mx]` | `Pr{mx}[= x]`; or `𝒟[mx] {x}` when the output has measurable singletons |
| `Pr[⊥ \| mx]` | `1 - Pr{_ ← mx}[True]`; identically `0` for `OracleComp` |
| `evalSPMF mx`, `𝒮[mx]` | `𝒟[mx]` |
| `tvDist mx my` | `measureETVDist mx my`; `Measure.etvDist` on measures |
| `expectedValue mx f` | `∫⁻ x, f x ∂𝒟[mx]` |
| `NeverFail mx` | nothing on `OracleComp`; `IsProbabilityMeasure 𝒟[mx]` for failing monads |
| `RelTriple'` | `RelTriple` |
| `GameEquiv g₁ g₂` | same name; it means `letI : MeasurableSpace α := ⊤; 𝒟[g₁] = 𝒟[g₂]` |

## Classes and binders

| Legacy | Native |
|---|---|
| `[IsProbabilitySpec spec]` | `[∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)] [OracleSpec.IsMeasureSpec spec]` |
| `[IsUniformSpec spec]` | the same binders with `[OracleSpec.IsUniformMeasureSpec spec]`, plus `[Fintype (spec.Range t)]` where a cardinality appears |
| `IsUniformSpec.ofFintypeInhabited spec` | `IsUniformMeasureSpec.ofFiniteNonempty spec`, as a local instance; it needs only `Finite` and `Nonempty` answers |
| `PFunctor.IsProbabilitySpec`, `PFunctor.IsUniformSpec` | `PFunctor.IsMeasureSpec`, `PFunctor.IsMeasureSpec.uniformOfFiniteNonempty` |
| `EvalDistCompatible`, `DiscreteEvalDistCompatible` | operational support lemmas and the `𝒟` equations; no class |

`unifSpec` and `coinSpec` carry global uniform measure instances. For a concrete specification
whose answer types are abstract, such as `unifSpec + (Unit →ₒ Chal)` with `[Fintype Chal]
[Inhabited Chal]`, declare the answer σ-algebras (`fun _ => ⊤`), their discreteness and
`IsUniformMeasureSpec.ofFiniteNonempty _` as local instances once per file.

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
`relTriple_eqRel_of_evalSPMF_eq` → `relTriple_eqRel_of_evalDist_eq`;
`evalSPMF_eq_of_relTriple_eqRel` → `evalDist_eq_of_relTriple_eqRel`.

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
| failed to synthesize `MeasurableSpace (spec.Range t)` or `OracleSpec.IsMeasureSpec spec` | add the binders from *Classes and binders*, or the local instances for a concrete specification |
| failed to synthesize `MeasurableSingletonClass α` for `𝒟[mx] {x}` | state the event as `Pr{mx}[= x]` |
| `rw` fails on a `𝒟[…]` term whose measurable-space instance is equal but spelled differently (e.g. Mathlib's `Fin` instance against a local `⊤`) | close with `exact`, `.trans` or `convert`, which unify up to definitional equality |
| two events that should agree differ only in how their binds and maps are arranged | `simp only [prEvent_norm]` brings both into the normal form of `Pr{…}[…]` |
| a lemma about `Pr{y ← mx >>= f}[q y]` no longer matches after `simp` pushed the event into the bind | apply the lemma before `simp`, or state it for `prEvent (mx >>= g)` with `g : α → m Prop` |
| a proof relied on `Pr{…}[…]` unfolding to `𝒟[… >>= fun x => pure …] {True}` | `simp only [prEvent_def, map_eq_bind_pure_comp, Function.comp_def]` recovers that form; better, use the laws keyed on `prEvent` |
| `simp [prEvent_def]` loops | `simp` rewrites `𝒟[mx] {True}` back to `prEvent mx`; use `rw [prEvent_def]` or `simp only` |
| `rw` does not find an event lemma whose selector's type depends on an implicit argument | supply that argument, e.g. the query index: `rw [prEvent_liftM_query_eq_card_div t]` |
| `simp only [f]` leaves a partially applied predicate `f a b` in an event | the event selector is eta-reduced; `unfold f` instead |
| measurability hypotheses of the `_ae` and `lintegral` event laws | they take the map form `Measurable fun x => 𝒟[p <$> f x]` |
| an event transported between monads (`ProbComp` and `OracleComp spec`) | with `let : MeasurableSpace α := ⊤`, rewrite both sides by `prEvent_eq_evalDist_of_discrete` and use a measure equation such as `uniformSampleImpl.evalDist_simulateQ` or `OracleComp.evalDist_liftComp_uniform` |
| `x ∈ support mx ↔ 0 < mass` needs a uniform specification | use `mem_support_iff_evalDist_singleton_pos_of_fullSupport` with a full-support hypothesis for other answer measures |
| probability one from reachability | `prEvent_eq_one_of_forall_mem_support`; the converse `prEvent_eq_one_iff` needs uniform answers |
| heartbeat timeout on raw `PFunctor.FreeM` terms | normalize with `FreeM.bind_eq_bind`, `FreeM.map_eq_map`, `FreeM.pure_eq_pure`, or state the helper at the `OracleComp` level |
| deprecation warning `VCVio retiring probability API: use …` | follow the named replacement |

## Semantic contract

- **Fix σ-algebras inside definitions.** A definition stated with `𝒟[…]` depends on the
  measurable space its caller supplies; under `⊥` an equality of measures says nothing. Security
  definitions put `letI : MeasurableSpace α := ⊤` inside, as `GameEquiv`, `PerfectlyHiding` and
  `SymmEncAlg.ciphertextRowsEqualAt` do.
- **Events need no measurable space; singletons do.** `Pr{…}[…]` works on any output type,
  while `𝒟[mx] {x}` needs measurable singletons.
- **Support is operational.** `support mx` is the set of structurally reachable outputs. It
  coincides with the positive-mass outputs only when every answer has positive mass, which the
  uniform specifications provide.
- **Continuous answers.** Oracle answers may carry non-discrete σ-algebras through
  `PFunctor.IsMeasureSpec`; the `OracleSpec` classes above assume discrete answers.
