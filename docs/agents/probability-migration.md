# Converting Downstream Code to Measure-Based Probability

VCVio's probability semantics are Mathlib measures: `𝒟[mx]` is the output measure of a
computation and `Pr{let x ← mx}[p x]` is the mass of an event. Earlier versions also had a discrete
surface — `SPMF`, `evalSPMF`/`𝒮[…]`, `probOutput`/`probEvent`/`probFailure` with the `Pr[…]`
notation, and the classes that interpret them — which has been removed. This guide converts code
written against it. Most of the conversion is mechanical: find the removed form in the tables
below, write its replacement, and use the symptom table for what remains.

For proof strategies (bind congruence, common-prefix bounds, coupling, total variation) see the
*Standard proof conversion* table in `docs/design/measure-conversion-roadmap.md`. The design
record is `docs/reading/denotational-probability-semantics.md`.

## Quick path

1. Repin VCVio.
2. Run the codemod over your sources, from the VCVio checkout Lake placed in your project:
   `python3 .lake/packages/VCVio/scripts/migrate-native-probability.py <source directories>`
   (`--dry-run` prints the diff instead of writing). It rewrites what the tables below convert
   mechanically: legacy events and bare draws in `Pr{…}`, `GameEquiv`, `≡ₚ` and equations of
   output distributions `𝒮[A] = 𝒮[B]`, oracle answer-type binders, the spec classes, renamed
   declarations, imports of removed modules, and `open`s of removed namespaces.
   Every site it leaves is reported as `path:line:` with the entry of this guide that converts
   it; for the most used discrete lemmas the report names the replacement. Pass all of a
   project's sources in one run: a lemma one of them declares under a discrete-style name
   (`probOutput_…`) is the project's own and is not reported at its uses, and a local copy of a
   lemma VCVio replaces is reported once, at its declaration.
3. Build. Work through the reported sites and the remaining errors with the *Symptoms* table.
4. Check that definitions fix their σ-algebras (see *Semantic contract*).

The codemod is textual: it never needs a build and is idempotent, so it can be rerun after a
further repin. It does not convert proofs; a proof that computed with `probOutput` sums, `SPMF`
equalities or `tvDist` follows the *Standard proof conversion* table of the roadmap.

## Notation and definitions

| Removed | Replacement |
|---|---|
| `Pr[p \| mx]`, `probEvent mx p` | `Pr{let x ← mx}[p x]` |
| `Pr[fun (x : τ) => t \| mx]` | `Pr{let x : τ ← mx}[t]`: the codemod keeps the binder's type, so a numeral in the event is read at `τ` rather than at `ℕ` |
| `Pr[= x \| mx]`, `probOutput mx x` | `Pr{let y ← mx}[y = x]`; or `𝒟[mx] {x}` when the output has measurable singletons |
| `Pr[⊥ \| mx]`, `probFailure mx` | `prFail mx` (`1 - Pr{let _ ← mx}[True]`); identically `0` for `OracleComp` |
| `Pr{mx}[= a]` (earlier measure API) | `Pr{let x ← mx}[x = a]` |
| `Pr{x ← mx}[p x]` (a bare draw) | `Pr{let x ← mx}[p x]`: the braces hold an ordinary `do` sequence |
| `evalSPMF mx`, `𝒮[mx]`, `SPMF α` | `𝒟[mx] : Measure α`; `evalDistWithFailure mx : Measure (Option α)` records the failure mass at `none` |
| `tvDist mx my` | `etvDist mx my` (`ℝ≥0∞`, keyed on events, across monads) or `tvDist mx my` (its real form); `measureETVDist mx my` on a chosen σ-algebra, `Measure.etvDist` on measures |
| `expectedValue mx f` | `∫⁻ x, f x ∂𝒟[mx]` |
| `NeverFail mx` | nothing on `OracleComp`; `IsProbabilityMeasure 𝒟[mx]` for failing monads |
| `RelTriple'` | `RelTriple` |
| `spec₁ ++ₒ spec₂` | `spec₁ + spec₂` |
| `GameEquiv g₁ g₂`, `g₁ ≡ₚ g₂`, `𝒮[g₁] = 𝒮[g₂]`, `letI : MeasurableSpace α := ⊤; 𝒟[g₁] = 𝒟[g₂]` | `g₁ =ᵈ g₂` (`EvalDistEq`; the codemod rewrites the first three); `EvalDistEq.of_evalDist_eq` and `evalDistEq_iff_evalDist_eq` relate it to output measures |

## Classes and binders

| Removed | Replacement |
|---|---|
| `[OracleSpec.IsMeasureSpec spec]`, `PFunctor.IsMeasureSpec` | `[OracleSpec.AnswerMeasure spec]`, `PFunctor.AnswerMeasure` (the class carries the answer measures, so it is not an `Is…` mixin) |
| `[OracleSpec.IsUniformMeasureSpec spec]` | `[OracleSpec.UniformAnswerMeasure spec]` |
| `[IsProbabilitySpec spec]` | `[OracleSpec.AnswerMeasure spec]` |
| `[IsUniformSpec spec]` | `[OracleSpec.UniformAnswerMeasure spec]`, plus `[Fintype (spec.Range t)]` where a cardinality appears |
| `[∀ t, MeasurableSpace (spec.Range t)]`, `[∀ t, DiscreteMeasurableSpace (spec.Range t)]` | delete them: answer measures live on the discrete σ-algebra |
| `OracleSpec.addRangeMeasurableSpace`, `OracleSpec.addRangeDiscreteMeasurableSpace` | delete them; no replacement is needed |
| `IsUniformSpec.ofFintypeInhabited spec` | `UniformAnswerMeasure.ofFiniteNonempty spec`, as a local instance; it needs only `Finite` and `Nonempty` answers |
| `PFunctor.IsProbabilitySpec`, `PFunctor.IsUniformSpec` | `PFunctor.AnswerMeasure`, `PFunctor.AnswerMeasure.uniformOfFiniteNonempty` |
| `EvalDistCompatible`, `DiscreteEvalDistCompatible` | operational support lemmas and the `𝒟` equations; no class |
| `[MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]` | `[EvalDistSemantics m] [LawfulEvalDistSemantics m]` |
| `[MonadLiftT m SetM] [LawfulMonadLiftT m SetM]` for `support` | `[MonadAttach m] [ExactMonadAttach m]` |
| `open scoped ProbComp.DiscreteCompatibility` | delete it |

`unifSpec` and `coinSpec` carry global uniform measure instances. For a concrete specification
whose answer types are abstract, such as `unifSpec + (Unit →ₒ Chal)` with `[Fintype Chal]
[Inhabited Chal]`, declare
`local instance : UniformAnswerMeasure (Unit →ₒ Chal) := .ofFiniteNonempty _` on the component
once per file. The sum then gets its instance from `UniformAnswerMeasure.add`. Do not declare an
instance on the sum itself, since it would compete with that one.

## Query and handler laws

| Removed | Replacement |
|---|---|
| `evalDist_liftM_query : 𝒟[liftM (query t)] = toMeasure t` | `evalDist_liftM_query` gives `(toMeasure t).trim le_top` in any measurable structure on the answer; `MeasureTheory.trim_eq_self` removes the trim under `⊤` (including `Bool`, `Fin n`) |
| `simp [evalDist_liftM_query, toMeasure_singleton]` for `𝒟[liftM (query t)] {u}` | `simp` with the simp lemmas `evalDist_liftM_query_apply` and `UniformAnswerMeasure.toMeasure_singleton` |
| `evalDist_liftM_query_eq_uniformOn_top` | `evalDist_liftM_query_uniform`, in any measurable structure; `evalDist_liftM_unifSpec_query` and `evalDist_liftM_coinSpec_query` for the built-in specifications |
| `evalDist_simulateQ_run_congr_of_forall` | `evalDist_simulateQ_run_congr` with `=ᵈ` step facts; `evalDistEq_simulateQ_run` for the equality in distribution itself |
| `evalDist_liftComp_of_evalDist`, `wp_liftComp_of_evalDist` | `evalDist_liftComp_of_evalDistEq`, `wp_liftComp_of_evalDistEq` |
| per-query hypotheses `𝒟[impl t] = 𝒟[liftM (query t)]` or `𝒟[(h q).run s] = 𝒟[(h' q).run s]` (`evalDist_simulateQ_congr`, `wp_simulateQ_eq`, `wp_simulateQ_run'_eq`, `evalDist_simulateQ_run'_eq_of_forall`, `MeasureDistEquiv.of_step`, `of_step_bij`, `parSum_congr`) | the same statements with `=ᵈ`, which need no measurable space on answers or states |

To reuse an existing per-query measure equality `h` proved for an arbitrary measurable structure,
supply `fun q s => by let : MeasurableSpace (spec.Range q × σ) := ⊤; exact
EvalDistEq.of_evalDist_eq (h q s)`. Restating the step lemma with `=ᵈ` is better: its
statement then needs no measurable space at all.

## Lemma names

Replacement lemmas keep the removed name with the probability head replaced:

| Removed name part | Replacement name part | Example |
|---|---|---|
| `open scoped OracleComp.Qualitative` / `.Angelic` / `.Quantitative` | `open scoped OracleComp.Necessary` / `.Possible` / `.Lower` (the readings are named by what a triple states; `OracleComp.Upper` and `.Probabilistic` are unchanged, and the `Dispatch` scopes follow) |
| `open scoped ExpectationWP.Quantitative` | `open scoped ExpectationWP.Lower` |
| `exp_norm` (tactic) | `expect_arith` |
| `simp only [game_rule]`, `@[game_rule]` | `simp only [expect_norm, expect_eval]`; loop unfoldings, values and simulation steps are `@[expect_eval]`, linearity is `@[expect_arith]` |
| `probEvent_` | `prEvent_` | `le_probEvent_isSome_contextFork` → `le_prEvent_isSome_contextFork` |
| `probOutput_` | `prEvent_` or `evalDist_` | `IND_CPA_Game_probOutput_eq_branch` → `IND_CPA_Game_evalDist_eq_branch` |
| `evalSPMF_` | `evalDist_` | `evalSPMF_simulateQ_run_congr` → `evalDist_simulateQ_run_congr` |
| `tvDist_` (bounds stated on `ENNReal.ofReal (tvDist …)`) | `etvDist_` | `tvDist_simulateQ_le_probEvent_bad` → `etvDist_simulateQ_run'_le_prEvent_bad` |

Other renames: `MeasureProgramLogic` → `ExpectationWP` (`measureWP` → `wpMonad`, `toMAlgOrdered`
→ `algebra`; the reading `Quantitative` → `Lower`); `AdvBound.of_tvDist` → `AdvBound.of_etvDist` (and `AdvBound` takes an
`ℝ≥0∞` bound); root `evalDist_uniformSample` → `SampleableType.evalDist_uniformSample`;
`relTriple_eqRel_of_evalSPMF_eq` → `relTriple_eqRel_of_evalDistEq`;
`evalSPMF_eq_of_relTriple_eqRel` → `evalDistEq_of_relTriple_eqRel`; in the identical-until-bad
family `_plus_probEvent_bad` → `_add_prEvent_bad` (for example
`advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv_preserved`) and `tvDist_simulateQ_…` →
the `etvDist_simulateQ_run…` lemmas in `Relational/SimulateQ/UntilBad.lean`;
`wpProp_iff_probEvent_eq_one` → `OracleComp.Necessary.prEvent_eq_one_iff_triple` (a core triple in
the necessary reading in place of the proposition-valued weakest precondition).

The bridges between the two representations have no replacement; state the measure fact
directly:
- `evalDist_apply_singleton` → `prEvent_eq_evalDist_singleton` (read backwards);
- `evalDist_apply_setOf` → `prEvent_eq_evalDist_of_discrete`;
- `evalDist_apply_univ` → `prFail_eq_one_sub_evalDist_univ` or
  `prEvent_true_eq_evalDist_apply_univ`, or `OptionT.evalDist_apply_univ`;
- `probOutput_bind_eq_tsum`, `probEvent_bind_eq_tsum` → `prEvent_bind_eq_lintegral` (with
  `_of_discrete` for a discrete draw), then `lintegral_fintype` for a finite sum.

Statements of equality in distribution now use `=ᵈ`:
- `prEvent_congr_of_evalDist_eq mx my h p` → `(EvalDistEq.of_evalDist_eq h).prEvent_eq p`;
- `evalDist_bind_congr_of_evalDist_eq mx my h f` → `((EvalDistEq.of_evalDist_eq h).bind_left f).evalDist_eq`;
- `evalDist_map_congr_of_evalDist_eq mx my h f` → `((EvalDistEq.of_evalDist_eq h).map f).evalDist_eq`;
- lemmas named `…_of_evalDist_eq` whose hypothesis was a discrete measure equality become
  `…_of_evalDistEq`, e.g. `relTriple_of_evalDistEq_left`, `support_eq_of_evalDistEq`,
  `etvDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq`;
- lemmas whose conclusion was one become `evalDistEq_…`, e.g. `evalDistEq_generateSeed_of_countEq`,
  `evalDistEq_of_forall_prEvent_eq_output`, `SampleableType.evalDistEq_uniformSample_vector_succ`;
- `AdvBound.of_gameEquiv` → `AdvBound.of_evalDistEq`.

Expectation laws have `wp` and `∫⁻` forms: `expectedValue_bind` → `wp_bind` or
`lintegral_evalDist_bind`; `expectedValue_map` → `wp_map` or `lintegral_evalDist_map_of_discrete`;
`expectedValue_mono_of_support` → `wp_mono_of_support`; `expectedValue_ne_top_of_finite` →
`wp_ne_top_of_finite`; `expectedValue_finsetSum` → `wp_finsetSum`; `expectedValue_iSup` →
`lintegral_iSup`; the `WithoutReplacement` length equations → `lintegral_evalDist_length_…`.

Proofs that compute with sums of point masses convert to `VCVio.OracleComp.EvalDist.Sum`. For
oracle computations with finite answer types, `lintegral_evalDist_eq_tsum` identifies
`∫⁻ x, f x ∂𝒟[oa]` with `∑' x, Pr{let y ← oa}[y = x] * f x`, with no countability assumption on
the output type. The sum forms follow from it:
- `probOutput_bind_eq_tsum` → `OracleComp.prEvent_bind_eq_tsum`;
- `tsum_probOutput_eq_one` → `tsum_prEvent_eq_one`, and `tsum_prEvent_le_one`;
- bind, `pure` and map sums → `tsum_prEvent_bind_mul`, `tsum_prEvent_pure_mul`,
  `tsum_prEvent_map_mul`;
- `tsum_prEvent_mul_of_const_on_support` and `tsum_prEvent_mul_le_add_of_le`;
- `tvDist_bind_left_le` → `etvDist_bind_left_le_tsum`, where `etvDist` takes the place of
  `ENNReal.ofReal (tvDist …)`; the algebra of the real form (`tvDist_self`, `tvDist_comm`,
  `tvDist_triangle`, `tvDist_le_one`, `tvDist_map_le`, `tvDist_bind_le`, `tvDist_eq_zero_iff`)
  keeps its names in `EvalDist/EvalDistTV.lean`.

## Converted theorem families

These families changed statement shape as well as names. The codemod renames the declarations;
callers restate the hypotheses they supply.

| Family | Removed statement | Current statement |
|---|---|---|
| `SigmaProtocol.HVZK`, `IdenSchemeWithAbort.HVZK` | `ζ_zk : ℝ` with `0 ≤ ζ_zk`, and `tvDist real sim ≤ ζ_zk` | `ζ_zk : ℝ≥0∞`, and `etvDist real sim ≤ ζ_zk`; the nonnegativity hypothesis goes |
| `PerfectHVZK` | `𝒮[real] = 𝒮[sim]` | `real =ᵈ sim`; `perfectHVZK_iff_hvzk_zero` relates it to `HVZK … 0` |
| `SymmEncAlg.Complete` | `∀ msg, 𝒮[completenessExperiment msg] = PMF.pure (some msg)` | `∀ msg, Pr{let x ← encAlg.completenessExperiment msg}[x = some msg] = 1`; `measureComplete` is the Dirac form under a chosen `ProbabilitySemantics` |
| `CommitmentScheme.PerfectlyHiding`, `TrapdoorExtractor.SetupConsistent`, `DeferredSampling.Factorizes` | equalities of `𝒮[…]` | equalities in distribution `=ᵈ` |
| `simCommitPredictability` | `Pr[= c₀ \| Prod.fst <$> simT x] ≤ β` | `Pr{let t ← simT x}[t.1 = c₀] ≤ β` |
| Fiat–Shamir CMA-to-NMA loss (`euf_cma_to_nma`, `euf_cma_bound`) | `ENNReal.ofReal (qS * ζ_zk)` | `qS * ζ_zk` |
| Charged steps of the per-query slack bounds (`expectedQuerySlack`, `advantage_le_expectedQuerySlack_add_prEvent_bad` and its variants) | `ENNReal.ofReal (tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false))) ≤ ε s` | `etvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ ε s` |
| Uncharged steps of the same bounds | `∀ p, (h₀ t).run p = (h₁ t).run p` | `∀ s, (h₀ t).run (s, false) = (h₁ t).run (s, false)`: only good states are compared |
| `expectedQuerySlack` step | `∑'`-weighted continuation | the unary expectation `wp` of the continuation |
| Rényi divergence of programs (`renyiDiv a mx my`, `PMF.renyiDiv`) | on `SPMF` or `PMF` | `InformationTheory.renyiDiv a 𝒟[mx] 𝒟[my]` on the output measures, with `⊤` fixed on the output inside definitions |
| Rényi bounds | `PMF.renyiDiv_prob_bound`, `renyiDiv_le_of_pointwise_le`, `renyiDiv_prod`, `maxDiv`, `etvDist_le_of_maxDiv`, `etvDist_sq_le_of_renyiDiv` | `measure_rpow_div_renyiDiv_le` (an event `s` instead of a predicate), `renyiDiv_le_of_le_smul` (`μ ≤ c • ν`), `renyiDiv_prod` (absolutely continuous factors), `maxDiv`, `etvDist_le_one_sub_inv_maxDiv`, `etvDist_rpow_two_le_one_sub_inv_renyiDiv` |
| Randomized oracles and executable responders (`ProbHandler`, `ProbResponder.IsExecutable.answerSPMF`, `ofSPMF`, `ofStateQueryImpl`) | `SPMF`-valued, with `𝒮` transport from `ProbComp` handlers | `ProbComp`-valued: `answerComp` whose `𝒟` is the kernel, `ofQueryImpl` from `StateT σ ProbComp`; the run bridge is `rfl`, and the executable layer lives in `Type` |
| `discreteGaussianDist σ μ hσ : PMF ℤ` | pointwise mass | `discreteGaussianMeasure σ μ : Measure ℤ`, with `discreteGaussianMeasure_singleton` and `isProbabilityMeasure_discreteGaussianMeasure` |

The Fiat–Shamir extraction bounds `nma_to_hard_relation_bound`, `euf_nma_bound` and
`euf_cma_bound` no longer take the extractor-failure hypothesis `hss_nf`, which holds for every
`OracleComp`; drop that argument at call sites. Their conclusions and `Fork.advantage` are
`Pr{let x ← …}[x = true]` events.

For an aborting identification scheme whose loss is a real-valued formula, keep `ζ_zk : ℝ` and
pass `ENNReal.ofReal ζ_zk` to `HVZK`, as `FiatShamirWithAbort.euf_cma_bound` does.

## Removed and narrowed statements

Statements of the discrete layer that have no literal counterpart, with what states the same
fact now.

| Removed or narrowed | Current |
|---|---|
| `SymmEncAlg.perfectSecrecyPosteriorEqPriorAt`, `perfectSecrecyJointFactorizationAt` and their `_iff_` lemmas | `perfectSecrecyAt`: they were `perfectSecrecyAt` up to `mul_comm` |
| `SymmEncAlg.perfectSecrecyAtAllPriors`, `perfectSecrecyAtAllPriors_iff_ciphertextRowsEqualAt` | `perfectSecrecyAt` quantifies over the priors `mgen : m M` of mass one; `perfectSecrecyAt_iff_ciphertextRowsEqualAt` (for `ProbComp`) and `ciphertextRowsEqualAt_of_perfectSecrecyAt` (any monad that can draw a two-point prior) give the equivalence |
| `SymmEncAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey`, `ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey`, `perfectSecrecyAt_of_uniformKey_of_uniqueKey` | the same names with the key and encryption laws stated as point masses (`prEvent_perfectSecrecyCipherGivenMsgExperiment_eq_of_uniformKey_of_uniqueKey`); the support form, `ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey_support`, needs uniform oracle answers |
| `SymmEncAlg.MeasureCompatibility.measurePerfectSecrecyAt_iff_ciphertextRowsEqualAt` | `SymmEncAlg.measurePerfectSecrecyAt_iff_ciphertextRowsEqualAt`, whose hypothesis identifies the semantics' rows with `𝒟` |
| `KEMDEM.perfectlyCorrect_composeWithDEM` over `[MonadLiftT m SPMF]` | the same name, generic in any lawful measure semantics, from `Pr{let b ← …}[b = true] = 1` hypotheses; no support or full-mass assumption |
| `ProbResponder.IsExecutable.answerSPMF_unique` | `IsExecutable.answerComp_evalDistEq`: two realizations of one kernel are equal in distribution, and `stepAgainst`, `iterateAgainst` and `transcriptAgainst` are congruent across them |
| Lossy executable responders | none: `IsExecutable.answerComp` is a `ProbComp`, which is lossless; a subprobability kernel stays at the `ProbResponder` level |
| `OracleSpec.probHandler`, `simulateQ_probHandler` (any `IsProbabilitySpec`) | `OracleSpec.uniformHandler`, `simulateQ_uniformHandler`, for sampleable answer types under `UniformAnswerMeasure`; a weighted specification has no canonical `ProbComp` handler |
| The executable layer at `OracleSpec.{u, u}` | `OracleSpec.{0, 0}`: `ProbComp` lives in `Type` |
| `outputRel_rel [Countable α]` | no countability: a `ProbComp` has finitely many outputs |

## Modules

| Removed or renamed module | Import instead |
|---|---|
| `VCVio.ProgramLogic.Unary.WP.Qualitative`, `….QualitativeSpecs` | `VCVio.ProgramLogic.Unary.WP.Necessary`, `….NecessarySpecs` |
| `VCVio.ProgramLogic.Unary.WP.Angelic` | `VCVio.ProgramLogic.Unary.WP.Possible` |
| `VCVio.ProgramLogic.Unary.WP.Quantitative`, `….QuantitativeSpecs` | `VCVio.ProgramLogic.Unary.WP.Lower`, `….LowerSpecs` |
| `VCVio.Prelude.Core` | `VCVio.Prelude.Core` (the `expect_norm`, `expect_eval` and `expect_arith` simp sets) |
| `ToMathlib.ProbabilityTheory.SPMF`, `ToMathlib.Probability.ProbabilityMassFunction.Measure` | nothing; state facts with Mathlib measures |
| `ToMathlib.Probability.ProbabilityMassFunction.Lemmas` | `Mathlib.Probability.Distributions.Uniform` |
| `VCVio.EvalDist.Defs.Basic` | `VCVio.EvalDist.Defs.Measure`, `VCVio.EvalDist.ProbabilityNotation` |
| `VCVio.EvalDist.Defs.AlternativeMonad`, `VCVio.EvalDist.Defs.NeverFails` | `VCVio.EvalDist.Defs.Support.Failure`, `VCVio.EvalDist.ProbabilityNotation` |
| `VCVio.EvalDist.FailureMeasure` | `VCVio.EvalDist.Defs.Measure` (`OptionT.evalDist_eq_dropNone`), `VCVio.EvalDist.WithFailure` |
| `VCVio.EvalDist.Bool`, `VCVio.EvalDist.BitVec`, `VCVio.EvalDist.Option` | `VCVio.EvalDist.Monad.Map`; event laws live in `VCVio.EvalDist.ProbabilityNotation` |
| `VCVio.EvalDist.Fintype` | `VCVio.EvalDist.Monad.Basic` |
| `VCVio.EvalDist.PFunctor` | `VCVio.EvalDist.PFunctorSupport` |
| `VCVio.EvalDist.PFunctorMeasure` | `VCVio.EvalDist.PFunctorMeasure.Core` |
| `VCVio.OracleComp.EvalDist.UniformCompatibility` | `VCVio.OracleComp.EvalDist.Measure`, `VCVio.OracleComp.EvalDist.MeasureSpec` |
| `VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility`, `VCVio.OracleComp.Constructions.SampleableType.NativeMeasure` | `VCVio.OracleComp.Constructions.SampleableType.Measure` |
| `VCVio.Native` | `VCVio.Foundations` |
| `VCVio.OracleComp.SimSemantics.WriterT.Basic` | `VCVio.OracleComp.SimSemantics.WriterT.Core` |
| `VCVio.OracleComp.QueryTracking.LoggingOracle` | `VCVio.OracleComp.QueryTracking.LoggingOracle.Core` |
| `VCVio.OracleComp.QueryTracking.CountingOracle` | `VCVio.OracleComp.QueryTracking.CountingOracle.Core` |
| `VCVio.OracleComp.QueryTracking.Tracing` | `VCVio.OracleComp.QueryTracking.Tracing.Core` |
| `VCVio.OracleComp.SimSemantics.QueryImpl.Constructions` | `VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core` |
| `VCVio.OracleComp.SimSemantics.StateT.Basic.Native` | `VCVio.OracleComp.SimSemantics.StateT.Basic` |
| `VCVio.OracleComp.Coercions.Add` | `VCVio.OracleComp.Coercions.Add.Basic` |
| `VCVio.OracleComp.Constructions.Fork` | `VCVio.OracleComp.Constructions.Fork.Basic` |
| `VCVio.CryptoFoundations.ForkMeasure` | `VCVio.CryptoFoundations.ReplayFork`, `VCVio.CryptoFoundations.SeededFork` |
| `VCVio.CryptoFoundations.SymmEncAlg.MeasureCompatibility` | `VCVio.CryptoFoundations.SymmEncAlg` |
| `VCVio.EvalDist.TVDist`, `VCVio.EvalDist.MeasureTVDist` | `VCVio.EvalDist.MeasureTVDist.Basic` (with `.Bind` and `.Event` for composition rules) |
| `VCVio.EvalDist.TVDist.Positivity` | `VCVio.EvalDist.MeasureTVDist.Positivity` (`positivity` on `measureTVDist`) |
| `VCVio.ProgramLogic.Relational.SimulateQ.Epsilon` | `VCVio.ProgramLogic.Relational.SimulateQ.UntilBad` |
| `VCVio.EvalDist.ExpectationMeasure` | `VCVio.ProgramLogic.Unary.HoareTriple` (`wp`) or `VCVio.EvalDist.Defs.Measure.Core` (`∫⁻` laws) |
| `VCVio.EvalDist.RenyiDivergence`, `ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence`, `ToMathlib.Probability.Divergence.RenyiDiscrete`, `ToMathlib.Probability.ProbabilityMassFunction.RadonNikodym` | `ToMathlib.Probability.Divergence.Renyi` |
| `ToMathlib.Probability.ProbabilityMassFunction.TotalVariation` | `ToMathlib.MeasureTheory.Measure.TotalVariation`; `ToMathlib.Probability.Divergence.RenyiTotalVariation` for the Rényi comparisons |
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

A removed module may have re-exported other modules; add the imports the build then asks for.
The hubs `VCVio.OracleComp.EvalDist`, `VCVio.OracleComp.ProbComp`,
`VCVio.OracleComp.Coercions.SubSpec` and `VCVio.OracleComp.Constructions.SampleableType` remain
and import the measure semantics of their area. `import VCVio.Foundations` is an entry point for
the oracle and probability foundations whose import closure excludes Mathlib's `PMF`.

## Symptoms

| Symptom | Fix |
|---|---|
| failed to synthesize `OracleSpec.AnswerMeasure spec` | add the binder from *Classes and binders*, or the local instance for a concrete specification |
| failed to synthesize `MeasurableSpace (spec.Range t)` inside a proof | `let : MeasurableSpace (spec.Range t) := ⊤` (use `let`, not `letI`, in a proposition-valued goal); in a statement, state the fact with `=ᵈ` or `Pr{…}[…]`, or take `{_ : MeasurableSpace (spec.Range t)}` |
| `rw`/`simp` does not find a query law such as `evalDist_liftM_query_apply` when the answer type appears reduced (`Bool` rather than `spec.Range t`) | name the specification: `evalDist_liftM_query_apply (spec := S) t hs` |
| two instances for a sum specification disagree (e.g. a local `UniformAnswerMeasure (A + B)`) | declare the local instance on the components and let `AnswerMeasure.add` build the sum |
| failed to synthesize `MeasurableSingletonClass α` for `𝒟[mx] {x}` | state the event as `Pr{let y ← mx}[y = x]` |
| `rw` fails on a `𝒟[…]` term whose measurable-space instance is equal but spelled differently (e.g. Mathlib's `Fin` instance against a local `⊤`) | close with `exact`, `.trans` or `convert`, which unify up to definitional equality |
| a goal shows `(toMeasure t).trim le_top` | `MeasureTheory.trim_eq_self` when the answer's measurable space is `⊤` by definition; otherwise evaluate measurable sets with `evalDist_liftM_query_apply` or `trim_measurableSet_eq` |
| `unexpected …; expected '}['` in a `Pr{…}` whose action continues on the next line | the braces hold a `do` sequence: indent the continuation past its `let`, start the sequence on its own line as in a `do` block, or parenthesize the action |
| two events that should agree differ only in how their binds and maps are arranged | `simp only [expect_norm]` brings both into the normal form of `Pr{…}[…]` |
| an explicit `prEvent (p <$> mx)`, `prEvent mx p`, or `prEvent (mx >>= fun x => …)` | an event is the expectation of its indicator: `Pr{let x ← mx}[p x]`; a literal non-normal program is `wp⟦mx >>= f⟧ (predInd p)` |
| `rw` with a lemma about `Pr{let y ← mx >>= f}[q y]` does not find its left side | the notation stores it as `wp⟦mx⟧ fun x => wp⟦f x⟧ fun y => 𝟙⟦q y⟧`; a goal holding a literal `wp (mx >>= f) g ⊥` (after unfolding a definition, say) needs `rw [prEvent_bind]`, `ExpectationWP.wp_bind` or `simp only [expect_norm]` first |
| `rw` with an equation between whole computations no longer finds them inside an event | turn it into the equation of the events: `congrArg (fun mx => Pr{let x ← mx}[p x]) h`, then `simp only [expect_norm] at …` |
| a proof relied on `Pr{…}[…]` unfolding to `𝒟[… >>= fun x => pure …] {True}` | `prEvent_eq_evalDist_map : Pr{let x ← mx}[p x] = 𝒟[p <$> mx] {True}` rewrites a single event to its measure |
| `prEvent_bind_of_discrete`, a `lintegral` over the events of `f x` | the notation gives the expectation `wp⟦mx⟧ fun x => Pr{let y ← f x}[p y]`; `ExpectationWP.wp_eq_lintegral mx _ .of_discrete` gives the integral |
| `prEvent_pure_prop` | `Pr{let y ← pure a}[p y]` elaborates to `𝟙⟦p a⟧`; `propInd_eq_ite` gives the `if` form |
| `prEvent_eq_wp`, `wp_propInd`, `OracleComp.wp_prEvent_swap` | an event is an expectation, so the first two are identities (drop the rewrite) and `OracleComp.wp_swap` covers the third |
| `OracleComp.ProgramLogic.wp oa post`, `OracleComp.ProgramLogic.propInd` | `wp⟦oa⟧ post`, core's `wp` under the measure interpretation; `propInd` at the root |
| `ExpectationWP.Lower.wp_*` | `ExpectationWP.wp_*`, stated on `wp⟦·⟧` and without measurability hypotheses except for `wp_eq_lintegral`, `wp_mono_ae`, `wp_iSup` and the `_mass` bounds |
| `rw` does not find an event lemma whose selector's type depends on an implicit argument | supply that argument, e.g. the query index: `rw [prEvent_liftM_query_eq_card_div t]` |
| `simp only [f]` leaves a partially applied predicate `f a b` in an event | the event selector is eta-reduced; `unfold f` instead |
| an event selector `p ∘ f` does not match `fun x => p (f x)` | the selector is eta-reduced; `simp only [Function.comp_def]` |
| `OracleComp.prEvent_bind_mono_of_support`, `OracleComp.prEvent_bind_congr_of_support` | `wp_mono_of_support mx h`, `wp_congr_of_support mx h` on the expectation over the shared draw |
| `prEvent_le_one mx p` no longer applies | the predicate is implicit: `prEvent_le_one mx`; a nest of expectations is bounded by `wp_le_of_forall_le _ fun _ => prEvent_le_one _` |
| `OracleComp.prEvent_bind_bind_swap` (continuation of type `m Prop`) | `OracleComp.wp_swap`, or `prEvent_bind_bind_swap` with a continuation and predicate |
| `simp` leaves `Pr{let a ← mx; let b ← f a}[True]` on `OracleComp` | `simp` evaluates it through `wp_const` and `OracleComp.prEvent_true_eq_one` |
| laws about `pure` (`prEvent_pure`, `map_pure`) do not fire on `pure v` written with an `OracleComp` ascription | that `pure` elaborates through `PFunctor.FreeM.instPure` rather than the monad; `erw [prEvent_pure]`, or state the term through the `do` block that produced it |
| measurability hypotheses of the `_ae` and `lintegral` event laws | they take the map form `Measurable fun x => 𝒟[p <$> f x]` |
| an event transported between monads (`ProbComp` and `OracleComp spec`) | take `.prEvent_eq p` of an equality in distribution such as `uniformSampleImpl.evalDistEq_simulateQ` or `OracleComp.evalDistEq_liftComp_uniform` |
| `x ∈ support mx ↔ 0 < mass` needs a uniform specification | use `mem_support_iff_evalDist_singleton_pos_of_fullSupport` with a full-support hypothesis for other answer measures |
| probability one from reachability | `prEvent_eq_one_of_forall_mem_support`; the converse `prEvent_eq_one_iff` needs uniform answers |
| `Application type mismatch` at `prEvent_mono_of_support … fun x hx h => …` | the predicates are explicit: `prEvent_mono_of_support mx p q h` |
| `cannot determine the monad of the draw` in a converted `Pr{let x ← e}[…]` | ascribe the computation, `Pr{let x ← (e : ProbComp α)}[…]`: the event elaborates its draws first, so a polymorphic `e` needs its monad |
| `unknown identifier 'tvDist'`, or `tvDist_triangle`, after the codemod rewrote `import VCVio.EvalDist.TVDist` | the event-keyed distance `etvDist` and its real form `tvDist` are in `VCVio.EvalDist.EvalDistTV`, which the current codemod imports |
| `SPMFSemantics`, `ProbCompRuntime.toSPMFSemantics` | `MeasureSemanticsVia` (the codemod renames `SPMFSemantics.withStateOracle` to `MeasureSemanticsVia.withStateOracle`); a runtime gives the field `toMeasureSemanticsVia` and the law `evalDist_map_eq` |
| heartbeat timeout on raw `PFunctor.FreeM` terms | normalize with `FreeM.bind_eq_bind`, `FreeM.map_eq_map`, `FreeM.pure_eq_pure`, or state the helper at the `OracleComp` level |
| unknown identifier `SPMF`, `probOutput`, `evalSPMF`, … or unknown `Pr[…]` syntax | run the codemod, then convert with the tables above |
| failed to synthesize `MeasurableSpace α` at `prEvent_true_eq_evalDist_apply_univ` | it takes the output's measurable space as an instance: `let : MeasurableSpace α := ⊤` first, or use `OracleComp.prEvent_true_eq_one` for an oracle computation |
| unknown namespace `OracleComp.EvalDist` in an `open` | delete it from the `open`; the codemod does this |
| failed to synthesize `EvalDistSemantics ProbComp` or `EvalDistSemantics (OracleComp spec)` | import `VCVio.OracleComp.EvalDist.Measure`; removed hubs used to supply it transitively |
| failed to synthesize `EvalDistSemantics (ExceptT ε m)` | the error type needs a measurable space: supply `MeasurableSpace ε` (e.g. `⊤`) or use an error type that has one |
| a measure lemma does not fire on `liftM mx : OptionT m α` | `OptionT.evalDist_liftM` (a `simp` lemma) |

## Semantic contract

- **Fix σ-algebras inside definitions.** A definition stated with `𝒟[…]` depends on the
  measurable space its caller supplies; under `⊥` an equality of measures says nothing. Security
  definitions state equality in distribution with `=ᵈ`, which needs no measurable space, as
  `SymmEncAlg.ciphertextRowsEqualAt`, `CommitmentScheme.PerfectlyHiding` and
  `DeferredSampling.Factorizes` do, and a distance between computations is `etvDist`. A
  definition about the measures themselves, such as the product measure of
  `SymmEncAlg.perfectSecrecyAt`, puts `letI : MeasurableSpace α := ⊤` inside.
- **Events need no measurable space; singletons do.** `Pr{…}[…]` works on any output type,
  while `𝒟[mx] {x}` needs measurable singletons.
- **Support is operational.** `support mx` is the set of structurally reachable outputs. It
  coincides with the positive-mass outputs only when every answer has positive mass, which the
  uniform specifications provide.
- **Discrete answers.** `OracleSpec` answer measures live on the discrete σ-algebra, so
  oracle programs carry no measurable-space hypotheses on answers. Continuous answer measures
  belong at the `PFunctor.FreeM` level, where `PFunctor.AnswerMeasure` takes any measurable
  structure.
