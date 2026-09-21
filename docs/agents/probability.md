# Probability Reasoning (EvalDist and ProbComp)

For the cross-project survey of SPMF, Mathlib measures and kernels, PolyFun
coalgebraic limits, ArkLib, Bluebell/Iris, and possible long-term migration paths, see
[`Probability Semantics for Computations: Landscape and Design Options`](../reading/probability-semantics-landscape.md).
The accepted design for new work is
[`Denotational Probability Semantics`](../reading/denotational-probability-semantics.md): use
Mathlib measures for closed denotations, kernels for environment/state-indexed computations,
effect-preserving outcome types for transformers, and keep `Pr[...]` as the discrete compatibility
surface. The [notation and computability account](../design/probability-notation-computability.md)
records which finite events can be evaluated exactly and which semantics require measurable
proofs. [`docs/reading/`](../reading/README.md) indexes the full design record.

`import VCVio.Native` is the public entry point for native oracle, sampling, measure, kernel,
operational-support, unary/relational WP, and stateful security foundations. Its ordinary import
closure contains neither
`PMF` nor `SPMF`; `VCVioTest.Native` checks this boundary. Some older module paths additionally
export discrete compatibility corollaries. WriterCost, QueryCost, and CostModel are native owners.

Handler instrumentation uses native owners in `QueryImpl.Constructions.Core`, `Append.Core`,
`WriterT.Core`, `Tracing.Core`, `CountingOracle.Core`, and `LoggingOracle.Core`. Their public
projection equations transport any observation of the computation, including its chosen-space
measure; no separate scalar evaluation theory is necessary. Query bounds, cache/programming
handlers, state projections, and invariant reasoning use these owners directly. Structural
results need no uniform probability interpretation. `StateT.OutputIndependent` compares output
measures, and `StateT.NeverFailsUnder` requires `IsProbabilityMeasure` on each invariant run.
Invariant-preserving prefixes may discard their output and state without choosing measurable
spaces on those discarded types.

`OracleComp.evalDist_bind_apply_mono_of_support` compares continuation events only on reachable
outputs. `le_evalDist_bind_apply_of_support` supplies the corresponding constant lower bound.
Neither theorem needs a measurable space on the intermediate result: induction on actual query
answers proves the bound. The final event must be measurable. `prEvent_congr_of_support`
transports predicates agreeing on reachable outputs. Signature completeness uses this same
event API rather than a scheme-specific scalar helper.

`measurable_evalDist_bind` combines measurable measure families. `evalDistKernel_bind` identifies
their bind with Mathlib kernel composition. `StateT.evalDistKernel_bind` composes through the
joint result/final-state space; the continuation receives both components. These rules use the
chosen measurable spaces and require no discrete structure on environments or states.

`Measure.bind_apply_le_sum_add_lintegral_ae` compares a continuation against a finite family
of reference measures, with possibly different output spaces and only AE measurability under
the chosen prefix measure. It requires no probability or finiteness certificates.
`Kernel.comp_apply_le_sum_add_lintegral_ae` uses the same law for existing Mathlib kernels.
Both share `lintegral_le_sum_add_lintegral_of_le_ae`, which also accepts a finite index set.

`VCVio.EvalDist.Monad.Disagreement.Measure` compares observed continuations after a common
prefix. `prEvent_bind_le_sum_add_lintegral_ae` integrates an AE comparison with finitely many
reference events and a varying allowance on the chosen source space. Continuation observation
families must be measurable; the allowance need not be. The reachable version uses core
attachment and the actual continuation-measure observer, leaving hidden source and result types
unmeasured. `prEvent_bind_le_sum_add_mul_mass_of_support` retains the allowance times the prefix's
successful mass. The weaker constant-allowance and disagreement/bad-world rules specialize the
same argument. The native owner imports no retired probability backend or compatibility class.

`AddWriterT.expectedCost` integrates the cost marginal on the chosen cost space. Weighted
query-cost and CostModel expectations use this same definition. Pathwise expectation bounds
need a measurable valuation; upper bounds permit failure, while lower and exact bounds require
`IsProbabilityMeasure` on the actual cost marginal. A valuation constant on reachable costs
integrates to its value times successful mass. Structural constant-cost laws need no attachment;
exact cost needs no order or monotone valuation. Markov bounds observe only the cost marginal.
`CostsAs` yields a chosen-space output integral when the cost function and valuation are
measurable. Countable sum formulas additionally require a countable output space and measurable
singletons. No measurable space is needed on outputs discarded by the cost marginal.
`AddWriterT.measurable_expectedCost` makes expected valuations measurable for a measurable
family of cost measures, which can be bundled using the existing `evalDistKernel`.
`MeasureTheory.lintegral_coe_nat_eq_tsum` is the tail-sum identity for a measurable Nat observable
under an arbitrary measure, including nonatomic measures. Natural query counts specialize it.

`VCVio.EvalDist.Monad.Branch` factors a conditional continuation through its actual finite
proposition-valued observation. `evalDist_bind_ite` gives the weighted mixture;
`prEvent_bind_ite` gives event probabilities, and `prEvent_bind_eq_mul_of_ite` handles
continuation events constant on one condition and zero elsewhere. No measurable space is needed
on discarded source values. `prEvent_add_prEvent_not` retains successful mass rather than
assuming the two weights sum to one. `evalDist.isProbabilityMeasure_bind_ite` requires a
probability certificate on that observation and on both branches. Measurable observation and
branch families give `measurable_evalDist_bind_ite`, which uses the existing `evalDistKernel`
with chosen environment/output spaces, including continuous spaces.

`VCVio.ProgramLogic.Relational.Measure` uses successful-output measure couplings. Pure and
successful optional values simplify to their exact postcondition with plain `simp`.
`eRelWP_mono` supports `gcongr` and `grw`. Unequal success masses admit no coupling, so the
qualitative judgment is false and the quantitative supremum is zero.
Couplings expose named `joint` and `isCoupling` fields, with public equations for their
constructors. Their joint laws infer probability, subprobability, and finite-measure certificates
from the corresponding marginal certificate. Countable-concentration reflexivity needs no
globally measurable equality relation; native finite-tree reflexivity closes with plain `simp`,
including on uncountable output types.
`CouplingPost.bind_of_countable` composes pointwise coupling witnesses on countable marginal
concentration sets: measurability is needed only under the chosen initial joint law. Its proof
uses Mathlib's measurable modification API, not a globally measurable choice principle.
`relWP_bind_of_aemeasurable` and `lintegral_le_eRelWP_bind` accept an explicit almost everywhere
measurable family. The quantitative rule supplies a witness lower bound; it does not assert
existence of an optimal coupling or interchange a supremum with integration. A product of
arbitrary discrete measurable spaces need not itself be discrete. Do not hide that distinction
in an automatic relational assertion-algebra instance.
`open scoped MeasureProgramLogic.Relational` selects PolyFun's qualitative `MAlgRelOrdered`
interface for finite-response oracle trees. The source and final operational output sets are
finite concentration sets, so arbitrary final relations are handled by restricting to their
countable measurable part. This works for uncountable output types and weighted interpretations;
it needs only finite responses, without enumerations or uniformity. The quantitative algebra is
not installed by this scope, and the qualitative algebra is not automatically anchored to
structural demonic WP under weighted interpretations.
The generic relational class and laws come from `PolyFun.Control.Monad.Algebra.Relational`.
`ToMathlib.Control.Monad.RelationalAlgebra` additionally installs the named upstream transformer
constructions for compatibility typeclass search. New code can select those constructions
explicitly. `MAlgRelOrdered.rwpExc` accepts one postcondition on both exception outcomes;
`rwpExcCases` packages four separate corner postconditions, while the one-sided and optional
case helpers remain available in `RelationalAlgebraAnchored`.

`VCVio.StateSeparating.MeasureDistEquiv` compares all adaptive client output measures under the
selected lawful interpretation. Its `of_step` rule retains each joint response/state law;
`prEvent_eq` transports final events, and the advantage rules permit replacing experiments
with different private-state types. `run_evalDist_eq` is the public observation equation.
Weighted interpretations can give a structurally possible answer zero mass; measure equivalence
therefore does not assert equality of operational support. Native coercions, state handlers,
`SecExp.Measure`, and `Advantage.Measure` have ordinary import closures without PMF/SPMF.

`evalDist_boolBias_bind_coin` is a generic fair-coin reduction for lawful measure semantics and
lossless Boolean branches. The probability-only security facade supplies its fair-coin law.
`SampleableType.evalDist_uniformSample_singleton` normalizes uniform singleton masses directly;
`Measure.apply_true_add_apply_false_eq_one` gives `simp` and `grind` the two-outcome mass law
without first unfolding the universal Boolean event into a finite set.

`VCVio.OracleComp.ProbComp.Basic` owns executable container sampling, and
`VCVio.OracleComp.Constructions.SampleableType.Basic` owns uniform sampler certificates.
Product and vector uniformity follow from product measures and bijective pushforwards.
`SampleableType` derives `Nonempty` and `Finite`; enumeration is a separate computational choice.
An abstract result's `𝒟` still needs its chosen `MeasurableSpace`. Event notation hides intermediate
spaces, and uniformity certificates apply to any result space with measurable singletons.

`VCVio.EvalDist.Lossless` uses Mathlib's `IsProbabilityMeasure` directly. For a lossless prefix,
`evalDist.isProbabilityMeasure_bind_iff` characterizes a lossless bind by almost everywhere
lossless continuations. `isProbabilityMeasure_bind_of_ae` supplies the forward construction;
no structural positivity assumption or bind instance search is needed. `NeverFail`,
`EvalDistCompatible`, and `DiscreteEvalDistCompatible` are deprecated compatibility classes.
Their hypotheses remain meaningful only for the discrete adapters that actually satisfy them.

The [conversion checkpoint roadmap](../design/measure-conversion-roadmap.md) records the native
owners, standard proof conversions, subsequent theorem families, and validation gates.

`open scoped MeasureProgramLogic.Probabilistic` selects bounded `Prob` expectations for any
lawful measure semantics. Public value laws connect them to quantitative WP and Lebesgue
integration; constants retain success mass. Plain `simp`, `gcongr`, and `grw` work on optional
computations and weighted oracles. Qualitative oracle WP delegates to PolyFun's direct demonic
core WP, which needs only lawful attachment. The exact ordered assertion algebra remains
available for free oracle trees. State and reader reasoning uses PolyFun's indexed operational
judgments and kernels; flattened support does not acquire an exact bind law.

The primary notation is measure-valued: `𝒟[mx] : Measure α`. The generic classes and Giry laws
live in `VCVio.EvalDist.Defs.Measure.Core`; the direct free-program instances live in
`VCVio.EvalDist.PFunctorMeasure.Core`. These core modules do not import a PMF/SPMF backend.
`Pr{let x ← mx; ...}[event]` is the computation-style event notation. Write the first
statement directly after `Pr{`; no space is required. An explicit line break after `Pr{` is
also supported for multiline sequences. It elaborates
an ordinary Lean `do` sequence, returns its final Boolean or proposition, and takes
the `{True}` mass of that result's `𝒟`. It works with a direct measure-only oracle
interpretation as well as a finite compatibility interpretation. The
`prEvent_eq_evalDist` theorem requires a measurable predicate; its
discrete specialization discharges that condition. `prEvent_eq_evalDist_decide`
equates an event with a Boolean experiment's final `decide`, without requiring
a measurable space on the intermediate result. Factor the common sampling run
once when both forms of a security game are public. For an optional computation,
successful outputs are measured through `Measure.comap some`, so failure contributes no mass.
The `OptionT` measure instance also works when the base monad has no finite lift.
Native `OptionT` and `ExceptT` inherit the base pure certificate and, for lawful base monads,
the full measurable-bind certificate. Generic bind laws require measurability only of the
successful-output family, rather than the whole run measure. An auxiliary discrete source space
and the base map law transport the source measure back to its selected space.
`VCVio.EvalDist.Monad.Option` collapses a lifted draw followed by a guard into one `prEvent`
condition: `simp` and `grind` turn the guard and final event into their conjunction. Callers need
no measurable space on that intermediate type. A constant output map after the guard has the same
normalization rule, so monad normalization preserves this automation. The guarded unit-output
measure is its event probability times `Measure.dirac ()`. `OptionT.prEvent_eq_run` observes present
values in the underlying run, and `OptionT.prEvent_lift` preserves an event through a lift.
`VCVio.EvalDist.Defs.Measure.Deterministic` gives `Id`, `Option`, and `Except` native Dirac/zero
semantics without a finite backend. Every `Id` value and successful `Option`/`Except` constructor
infers its probability-measure instance; arbitrary optional/exceptional values infer only the
subprobability bound. Bare `Except` observes no errors and needs no measurable space on its error
type. `ExceptT` instead interprets its base run and uses the inherited coproduct space on errors
and outputs. Deterministic final events simplify to their propositional indicators with `simp`
and `grind`, using `Measure.dirac_apply_singleton_true`.
`VCVio.OracleComp.Support` exposes the oracle facade over native attachment, while
`PolyFun.PFunctor.Free.Support` owns the universe-polymorphic map/object equations and
finite/nonempty bounds. VCVio's `PFunctorSupport` module reexports that API. Support-aware bind
congruence needs only weakly lawful attachment, through PolyFun's public generic rule.
`VCVio.OracleComp.EvalDist.Measure` connects structural bounds to almost-everywhere bounds
under any discrete-answer response measures; neither uniformity nor positive singleton masses
is required for that direction. `VCVio.ProgramLogic.Unary.WP.OracleMeasure` exposes these
bounds on native expectation WP, including `gcongr` support hypotheses and additive allowances.
These modules have ordinary imports without PMF/SPMF.
`VCVio.EvalDist.Defs.Support` and its `Support.Failure` module expose operational support without
importing a probability backend. Optional failure has empty support under Lean's
`LawfulMonadAttach`, independently of any probability interpretation or lift. Its pure-output
elimination law suffices: no `ExactMonadAttach` is needed, including over state and reader bases.
`HasEvalSet.LawfulFailure` only requires an `Alternative` and attachment.
The independent `LawfulFailureEvalDistSemantics` mixin certifies zero measure for failure.
Native `Option` and `OptionT` export that certificate; `OptionT` needs only the base pure law.
`VCVio.EvalDist.Monad.Failure` makes failure before a continuation, a constantly failing
continuation, and a final event after failure normalize to zero with `simp` and `grind`.
These composition laws need no attachment or measurable-space instance on intermediate results.
Native transformer semantics takes priority over the generic finite lifting adapter. Opening
`ProbComp.DiscreteCompatibility` explicitly selects that adapter for retiring discrete calibration
proofs. Native certificates describe the native interpretation and do not assert laws about an
independently chosen interpretation. The successful-output pullback equations
`OptionT.evalDist_apply` and `ExceptT.evalDist_apply` hold on arbitrary sets, without a
measurability argument.
`SampleableType.prEvent_uniformSample` counts a decidable event as its accepted fraction of finite
outputs, using Mathlib's native `uniformOn` and counting measure.
`VCVio.EvalDist.Defs.Measure.FinRatPMF` gives the executable rational sampler native measure
semantics without importing a PMF/SPMF backend. `Raw.toMeasure` is a finite sum of weighted Dirac
measures; pure and measurable bind have the generic laws on arbitrary measurable spaces.
`Raw.evalDist_apply` computes decidable event masses as rational sums, and the singleton simp
lemma reduces to `Raw.prob`. `FinRatPMF.finRatImpl.evalDist_simulateQ` and `prEvent_simulateQ`
identify executable evaluation with the native uniform oracle interpretation.
`VCVio.ProgramLogic.Unary.WP.Measure` builds the ordered expectation algebra directly from
lawful measure semantics for any monad. `open scoped MeasureProgramLogic.Quantitative` selects
its `MAlgOrdered` and core `WPMonad` interpretations; no probability backend or oracle uniformity
is required. This scope takes precedence over core `Prop` interpretations, including `Option`.
`wp_eq_lintegral` is an explicit bridge to Mathlib integration. `simp` preserves the WP head
through addition and scaling, and constants keep the successful-mass factor:
`MAlgOrdered.wp mx (fun _ ↦ c) = c * 𝒟[mx] Set.univ`. Finite sums, monotone suprema, and
almost-everywhere comparisons have native laws. `gcongr` and `grw` compare pointwise
postconditions. `wp_le_const_mul_mass_add` retains the mass factor for lossy computations;
`IsProbabilityMeasure` simplifies it to one automatically. The oracle quantitative facade uses
this same native algebra and keeps its existing uniformity assumptions for compatibility.
`OracleComp.EvalDist.lintegral_evalDist` is an explicit discrete calibration equation;
it is deliberately absent from global `simp`, so integrals stay available to Mathlib's API.
Opening `ProbComp.DiscreteCompatibility` restores the old simp direction locally for adapter
proofs; native calibration statements use the equation explicitly.

The native sequencing laws in `VCVio.EvalDist.Monad.Seq.Measure` identify paired draws with
`Measure.prod` on arbitrary measurable result spaces. Discarding either draw retains its
successful-mass factor. `simp` and `grind` also normalize final events after sequencing without
requiring a measurable space on discarded values. Probability instances propagate automatically
through pairs, sequencing, `Fin.mOfFn`, and `Fintype.mPi` when all factors are probability measures.
Raw product measures inherit the subprobability bound as well.

`VCVio.EvalDist.Monad.Measure` provides `evalDist_bind_bind_swap` for jointly measurable
continuations and `evalDist_bind_bind_bind_rotate` for discrete intermediate results. Their
measure-level proofs use Tonelli's theorem and preserve subprobability mass.
The generic `evalDist_pair` law denotes independent sequential draws by Mathlib's product
measure. `evalDist_bind_apply_univ` expresses bind success mass as a `lintegral`, while
`evalDist_map_apply_univ` states map preserves that mass; both live in the measure core.
`prEvent_map` composes an output map with its final event. `prEvent_bind_bind_and` factors
independent conjunctions automatically with `simp` and `grind`; it runs before monad normalization
changes the computation's shape. `prEvent_bind_eq_lintegral` is the observed tower law and keeps
the common draw's measurable space explicit. `prEvent_bind_congr` instead compares continuation
event probabilities pointwise, hiding the intermediate measurable space and allowing different
continuation result types. `prEvent_mono` transports implication between final events without
an intermediate measurable-space argument. Use `grw [prEvent_mono ...]` to rewrite an event bound;
`gcongr` handles surrounding arithmetic, with this lemma closing the event comparison.
For discrete-answer oracle specifications, native `𝒟[mx]` has an automatic
`IsProbabilityMeasure` instance, including when the result space is continuous. Mathlib's
constant-integral and total-mass simp rules therefore need no local instance. This does not
assert losslessness for arbitrary continuous-answer programs with unmeasurable continuations.
A named opaque measure publishes its own measure-property instances once at its definition.
An opaque computation inside `𝒟[...]` still uses the generic denotation instances; computation
opacity alone does not require a separate witness. Callers should infer these properties rather
than recreate local witnesses. An ordinary mass or measurability hypothesis does not itself
register a typeclass instance: use a local `haveI` when a theorem establishes the required
property under that hypothesis. Such a local certificate is appropriate for a particular
measurable pushforward; repeated certificates for the same named measure indicate a missing
exported instance. For an abstract
intermediate type, a local `MeasurableSpace α := ⊤` chooses the discrete structure; Mathlib uses
this idiom in `MeasureTheory.Function.Piecewise` and `MeasureTheory.Function.SimpleFunc`.
Keep that choice inside structural APIs when callers do not need to observe intermediate values.
Mathlib already supplies discrete measurable spaces for `Bool`, `ℕ`, `Fin n`, and other standard
countable types; do not redeclare them locally when the canonical instance suffices.
Choose the space on the underlying data type once; `Option`, products, and subtypes normally use
their inherited measurable-space instances rather than separate local top spaces.
Genuinely measure-indexed results retain their selected measurable spaces as explicit parameters.
Every `𝒟[mx]` automatically satisfies `IsSubprobabilityMeasure`. Products inherit this bound from their two factors. The upper mass bound also
propagates automatically through raw `Measure.map`, whose nonmeasurable fallback has mass at
most one. For raw `Measure.bind`, use `isSubprobabilityMeasure_bind` with an explicit
almost-everywhere measurability proof. Exact mass preservation requires measurability. `pure` infers a probability-measure
instance even for continuous-answer specifications. Lifting a computation whose measure already
has an `IsProbabilityMeasure` instance into `OptionT` or `ExceptT` also infers that instance,
including through `liftM`. These lifts introduce no failure mass; arbitrary optional or exceptional
computations still need a losslessness certificate. `FreeM.isProbabilityMeasure_evalDist_lift`
supplies a single native query's probability proof. It is a theorem: the dependent output type
`P.B a` gives a projection key that instance search cannot match against a concrete reduced type
such as `ℝ`. A general continuous program still requires a continuation measurability proof.
`FreeM.denote` over discrete answers, `FreeM.pathMeasure`, and `FreeM.queryCountMeasure` export
probability instances; proofs should not install them locally. `evalDist_failure_eq_zero`
simplifies failure to zero under its native certificate.
`Measure.dropNone` preserves the subprobability instance of an optional measure, and
`Measure.withFailure` automatically completes any subprobability measure to a probability measure.
The backend-free `evalDistWithFailure` wrapper exports the same probability-measure instance.
The mass at `none` needs no discreteness hypothesis: the optional coproduct makes this singleton
measurable for every result space. Successful singleton masses need only measurable singletons.
`prEvent_eq_evalDist_singleton` identifies an equality event with its singleton mass under that
weaker assumption. It therefore works with inherited product spaces even when they are not discrete.
`FreeM.evalDist_lift_bind_pure` handles a measurable pure function after a single operation
without requiring discrete answer spaces; continuous final-event proofs can use this directly.
`le_evalDist_bind_apply` transports an almost-everywhere lower bound through a lossless draw;
its monad is generic and its event need only be measurable.

Runtime-valued signature experiments expose `IsSubprobabilityMeasure` instances, so
`measure_le_one` and `measure_ne_top` apply directly. An instrumented experiment recording
success and a Boolean selector uses `Measure.fst` for its success marginal.
`Measure.fst_apply_eq_add` splits a marginal event into the two disjoint selector events.
The SLH-DSA `advantage_eq_arms` and `sameMessageAdvantage_eq_arms` equations use that partition
without caller-supplied evaluator laws; the runtime already bundles its measurable-map law.
Their named FORS/hypertree and randomizer halves have exported defining equations and exact
partition theorems, so consumers do not need unfolding hypotheses.
`OracleComp.evalDist_map_const` handles a constant output map without a measurable space on
the discarded result type. This lets default `simp` stay on native measure laws after monad
normalization turns a constant return into a map.

`lintegral_evalDist_bind` states the tower law with a measurable continuation;
`lintegral_evalDist_bind_of_discrete` supplies that proof for a discrete common draw.
`lintegral_evalDist_map_add_nat` integrates an incremented natural-valued observation and
retains its successful-mass factor. The intermediate type needs no measurable space.
Lossless oracle programs infer that factor as one, so default `simp` proves the increment law.
`lintegral_evalDist_map_const_add_nat` supplies the curried `Nat.add` form for `grind`;
lambda-bound parameters are unavailable as automatic `grind` patterns.
`lintegral_uniformOn_univ` averages over a finite uniform measure, including the empty space
and infinite integrands. `ProbComp.lintegral_evalDist_uniformFin` exposes that law for a draw.

The native drawing loop and its measure-valued length integrals live in
`VCVio.OracleComp.Constructions.WithoutReplacement.Basic`. Observe `List.length` before
integrating: the pool's value type needs no measurable space. The stopping and exhaustion laws
use the same negative-hypergeometric recursion. The original import facade also exposes
deprecated discrete expectation equations.

`ToMathlib.MeasureTheory.Integral.Quadratic` specializes upstream Hölder to Cauchy–Schwarz,
retaining the total-mass factor for arbitrary measures and bounding it for subprobability
measures. Its quadratic bound requires only almost-everywhere measurable acceptance and
almost-everywhere acceptance/extraction bounds; the extraction functional need not be measurable.
`OracleComp.EvalDist.marginalized_jensen_forking_bound` applies it to any `EvalDistSemantics`,
without monad laws or discrete-backend assumptions. Its `_map` corollary observes acceptance and
extraction before integrating and keeps the intermediate measurable-space choice internal.

`VCVio.EvalDist.ProbabilityBounds` supplies `prEvent_bind_sq_le_bind_pair` for conditional
independent draws, including lossy common draws and continuations. Its selector-partition bound
`sum_prEvent_option_map_eq_some_le_isSome` uses finite disjoint unions of measurable events,
without expanding singleton probabilities. The raw measure lemma needs only measurable selector
fibers and no measurable space on the selector's target. These native arguments also prove the
discrete compatibility equations. Finite and weighted sum-of-squares inequalities derive from
the same integral Cauchy–Schwarz theorem by integrating atomic measures.
`VCVio.OracleComp.Constructions.Fork.Basic` owns the typed occurrence constructions and
`prEvent_sq_le_observedForkPair`: arbitrary discrete answer measures suffice, with no uniformity
assumption or measurable-space arguments on the observed outputs. The original fork import
facade retains the deprecated discrete equations. `evalDist_map_answer_completeOccurrence` and
`evalDist_map_secondAnswer_fork` recover the configured response measure without assigning a
measurable space to the completion or fork record. `prEvent_answer_completeOccurrence` transports
answer events to a fresh query. `prEvent_focusCollision_fork` identifies the exact collision
probability with the measure of the fixed first answer; adding an output guard only decreases it.
The `_le_of_uniform` corollary obtains inverse cardinality from the uniform measure's singleton law.
Answer marginalization and collision equations normalize with `simp` and `grind`, without a
decidable equality assumption on oracle names.
`ToMathlib.Probability.Kernel.Quadratic` states the conditional-square bound for measurable
kernel events on arbitrary spaces, so continuous kernel families have the same analytic API.

`VCVio.EvalDist.Monad.UniformTable` supplies cell resampling/extraction, permutation,
and injective restriction laws with explicit uniform-measure hypotheses. Its native counting
proofs live in `ToMathlib.MeasureTheory.Measure.UniformTable`. The continuation may lose mass.
`evalDist_map_equiv_of_uniform` packages Mathlib's `uniformOn_univ_map_equiv` for a computation;
use it for a uniform permutation before introducing a bind continuation.
`evalDist_bind_bijective_of_uniform` reindexes any continuation after a uniform draw,
using the finite-uniform pushforward law. `evalDist_bind_congr` compares continuation
measures pointwise without a measurable-space instance on the intermediate result.
`VCVio.OracleComp.EvalDist.Measure` gives `evalDist_bind_congr_of_support` by structural
induction, without a probability/support bridge. These laws power the PRF tag/reader cache,
composed-handler, and shared-observation proofs. `SampleableType.MeasureCompatibility`
keeps the finite adapter calibration for legacy runtimes. BR93's measure-level masking
step takes the chosen measure's uniformity certificate explicitly; its finite corollary
uses the adapter calibration.

The finite distribution API is
explicit as `evalSPMF mx` / `𝒮[mx]`, and `Pr[...]` remains the discrete compatibility façade. One
class connects the two: `DiscreteEvalDistCompatible m` says that integrating a measurable
functional against `𝒟[mx]` is the façade expectation `∑' x, Pr[= x | mx] * g x`. Everything else
is derived from it at an explicit compatibility boundary:
`evalDist_apply_singleton` (`𝒟[mx] {x} = Pr[= x | mx]`), `evalDist_apply_setOf`
(`𝒟[mx] {x | p x} = Pr[p | mx]` on a discrete space), `evalDist_apply_univ`
(`𝒟[mx] univ = 1 - Pr[⊥ | mx]`), and `lintegral_evalDist` (`∫⁻ x, g x ∂𝒟[mx] = expectedValue mx g`).
The compatibility adapter satisfies the class definitionally; the free-monad fold satisfies it
whenever its measure specification agrees with its probability specification
(`PFunctor.IsMeasureSpec.Compatible`, which `IsProbabilitySpec.toMeasureSpec` satisfies by `rfl`).
For a finite uniform oracle, `OracleSpec.IsUniformMeasureSpec.instCompatible` proves the same
agreement for the native `uniformOn Set.univ` interpretation. It lets a theorem about a direct
uniform measure fold use an existing finite probability equation at the compatibility boundary.
For `ProbComp Bool` security games, use `boolDistAdvantage` for a two-game gap and
`𝒟[game] {true}` for a success probability; prefer `Pr{...}[winningCondition]`
when the game ends by testing a predicate. The native uniform measure instances for
`unifSpec` and `coinSpec` are global, so no local uniform certificate is needed.
`boolDistAdvantage_self`,
`boolDistAdvantage_comm`, and `boolDistAdvantage_triangle` keep elementary
metric proofs independent of the finite façade.
The split between `𝒟[…]` and `Pr[…]` is intentional: an unconditional `Eq.rec` law for `Pr[...]`
only needs equality of result types, whereas a measure denotation also depends on the selected
`MeasurableSpace`, so there is no blanket finite-type measurable-space instance.

`SPMF`, `evalSPMF`, `probOutput`, `probEvent`, and `probFailure` are deprecated.
Mathlib owns `PMF`, so VCVio's `usesRetiredProbability` environment linter
records direct uses of it and the local finite API in `scripts/nolints.json`.
New theorem statements should prefer `𝒟` or `Pr{...}[...]` and use a named
compatibility equation only when discrete execution is needed.

The notation alone does not make a theorem measure-native: `evalDist` retains its
`EvalDistSemantics` instance as an implicit argument. If that instance is the
`MonadLiftT … SPMF` adapter, the theorem's elaborated type still refers to `SPMF`,
and `usesRetiredProbability` correctly reports it. State generic measure laws under
an explicit `EvalDistSemantics`, or select a direct `PFunctor.IsMeasureSpec` before
elaborating a concrete theorem. Keep sampler calibration through the old class in
compatibility proofs until the sampler's certificate itself is measure-valued.
For the finite-range and fair-coin oracles, `OracleSpec.IsUniformMeasureSpec.unifSpec`
and `OracleSpec.IsUniformMeasureSpec.coinSpec` are the canonical native interpretations.
Their instances apply only to these concrete oracle specifications; other oracle
specifications still require an explicit measure interpretation. With the native instance,
`ProbComp.evalDist_uniformFin` simplifies a query to `uniformOn Set.univ`, and
`ProbComp.prEvent_uniformFin` evaluates a decidable event by counting
its satisfying outcomes. These laws avoid a point-mass detour; the
`FinEnum.SampleableType` construction also has a native uniformity proof in
`SampleableType.NativeMeasure`, using finite-range sampling and equivalence
transport. Its product sampler law uses `evalDist_pair` and the existing
`uniformOn_univ_prod` construction. These supply the `BitVec` key law and the measure-level
one-time-pad independence theorem. `SampleableType` itself certifies
`𝒟[$ᵗ α] = uniformOn Set.univ` for every finite discrete measurable structure.
Its executable sampler and full-support certificate provide the operational
side; the old `Pr[...]` lemmas are compatibility consequences. Uniform table
resampling and injective restriction use the measure laws in
`VCVio.EvalDist.Monad.UniformTable`.
`ProbComp.evalDist_decide_eq_uniformBool_half` proves that an independent Boolean guess
matches a fair hidden bit with mass `1/2`; it uses the native uniform measure and
Mathlib's `lintegral_fintype`, so all-random game hops need no point-probability sum.
`ProbComp.evalDist_bind_not_uniformBool` applies the uniform-reindexing law to any
continuation after complementing a fair bit.

The type classes separate a choice of response measures (`IsMeasureSpec`) from the
additional uniformity and finite-range laws (`IsUniformMeasureSpec`). A blanket instance
from `[spec.Fintype] [spec.Inhabited]` would silently choose a distribution for an arbitrary
oracle, so only the concrete `unifSpec` and `coinSpec` instances are global. Structural
`OracleComp.support` needs neither measure class; a
positive-mass bridge needs assumptions on the chosen measures.
For oracle-relative possibility, use `OracleComp.reachableWhen possibleOutputs oa`:
it follows only the query responses in `possibleOutputs`, with pure/query/bind laws
and a `gcongr` monotonicity rule. PolyFun defines the underlying
`FreeM.reachableUnder` from an angelic operation-indexed weakest-precondition
fold. `reachableWhen_univ_eq_support` identifies its all-responses case with
`MonadAttach.support`; `supportWhen_eq_reachableWhen` keeps the old `SetM` fold
available as a deprecated compatibility bridge. This distinction matters for
stateful handlers: `MonadAttach` records possible returned values, while a
state-dependent notion must retain the starting state or operation policy.
`OracleComp.mem_support_iff_evalDist_singleton_pos_of_fullSupport` takes the precise
full-support condition on each answer measure, without adding a class for that one law.
`OracleComp.mem_support_iff_evalDist_singleton_pos` discharges it from
`IsUniformMeasureSpec`; use this native bridge when relating structural reachability to
singleton mass. Neither theorem requires the PMF-based `IsUniformSpec` class.
Structural support itself needs no probability interpretation. In particular,
`OracleComp.support_nonempty` needs only `[spec.Inhabited]`; counting-oracle support
and worst-case query bounds use that weaker assumption rather than `IsUniformSpec`.
Keep the class hierarchy for chosen answer measures, and state one-off properties such as
positive singleton mass as explicit hypotheses instead of adding a mixin for each bridge.
Compatibility proofs that still use the finite frontend can open
`ProbComp.DiscreteCompatibility` locally, leaving
the native interpretation as the default elsewhere.

The adapter is also `LawfulEvalDistSemantics` (`instLawfulEvalDistSemanticsOfMonadLiftTSPMF`), so
the Giry laws `evalDist_pure`, `evalDist_bind`, `evalDist_map` and the const laws hold with no
measure specification in scope; `evalDist_eq_evalSPMF_toMeasure` is its definitional unfolding.
`evalDist_bind`/`evalDist_map` are deliberately not `@[simp]` on either side: a bind is expanded
only on request (`gotchas.md` §10), and the measure side has no separate family of sum lemmas.
Independent products denote product measures: `evalDist_mOfFn` and `evalDist_mPi`
(`VCVio/EvalDist/IndepProductMeasure.lean`) identify `𝒟[Fintype.mPi f]` with
`Measure.pi fun i => 𝒟[f i]` directly from `LawfulEvalDistSemantics` and Mathlib's
`measurePreserving_piFinSuccAbove`/`pi_map_piCongrLeft`. The index traversal itself lives in
`ToMathlib.Control.Monad.Fold`, so these measure laws do not import the scalar product proofs.
`evalDist_map_eval_mOfFn_eq_smul` and `evalDist_map_eval_mPi_eq_smul` use
`Measure.pi_map_eval`: a coordinate marginal is its factor's measure scaled by every other
factor's success mass. The full-mass corollaries recover the factor itself.
`lintegral_evalDist_mPi_coord_eq_mul` gives the corresponding integral formula for lossy
families; `lintegral_evalDist_mPi_coord` handles full-mass factors.
`Fin.mOfFn_map` and `Fintype.mPi_map` move coordinate observations through sequencing.
`evalDist_map_coord_mOfFn` and `evalDist_map_coord_mPi` then give product measures on the
chosen observation space without requiring a measurable space on the original payloads.
`measurable_evalDist_mOfFn` and `measurable_evalDist_mPi` assemble measurable factor families
into measurable product families, so `evalDistKernel` packages them as Mathlib kernels on
the chosen parameter space. The proof uses kernel products and measurable reindexing.

`VCVio.EvalDist.IndepProduct` exports native event and reachability rules, also available through
`VCVio.Native`. Joint coordinate events factor by `prEvent_forall_coord_mOfFn` and
`prEvent_forall_coord_mPi`; tuple equality uses `prEvent_eq_mOfFn` and `prEvent_eq_mPi`.
These event rules require neither a measurable payload space nor attachment. The coordinate
`_eq_mul` rules retain the other factors' success masses, `_le` gives an unconditional bound,
and `prEvent_coord_mOfFn`/`prEvent_coord_mPi` need only the *other* factors to be lossless.
`mem_support_mOfFn` and `mem_support_mPi` eliminate reachable coordinates using core
`LawfulMonadAttach`; they require no exact-attachment or probability compatibility mixin.

For finite uniform-output computations, `evalDist_mOfFn_uniformOn_pi` and
`evalDist_mPi_uniformOn_pi` combine those laws with Mathlib's `uniformOn_pi`, allowing each
factor its own uniform set. Their constant-full-space corollaries take the single-draw
uniformity certificate explicitly; the Fischlin small-sum count supplies its compatibility
certificate at the boundary instead of inducting over singleton probabilities.
`OracleComp.evalDist_replicate_succ` uses Mathlib's `Measure.bind` and `Measure.map` for repeated
list-valued sampling, and `evalDist_replicate_apply_univ` gives its success mass as a power.
Because Mathlib does not install a generic measurable space on `List α`, these laws require the
chosen list measurable space and measurability of each `List.cons x` map explicitly.

Failure on the measure side is missing mass, recorded in `VCVio/EvalDist/FailureMeasure.lean`:
`Pr[⊥ | mx] = 1 - 𝒟[mx] univ`, `IsProbabilityMeasure 𝒟[mx] ↔ Pr[⊥ | mx] = 0` (an instance under
`NeverFail mx`), `𝒟[failure] = 0`, the failure-completed `(𝒟[mx]).withFailure : Measure (Option α)`
with `{none}` mass `Pr[⊥ | mx]`, the success mass of `bind`/`map` in `expectedValue` form, and
`OptionT.evalDist_eq_comap_some` (an `OptionT` computation denotes `Measure.comap some` of its run).
`OptionT.evalDist_eq_dropNone` supplies the equivalent compatibility normal form.

## Core Definitions

| Definition | Type | Notation | Defined in |
|-----------|------|----------|------------|
| `evalDist mx` | `Measure α` | `𝒟[mx]` | `EvalDist/Defs/Measure/Core.lean` |
| `evalSPMF mx` | `SPMF α` | `𝒮[mx]` | `EvalDist/Defs/Basic.lean` |
| `probOutput mx x` | `ℝ≥0∞` | `Pr[= x \| mx]` | `EvalDist/Defs/Basic.lean` |
| `probEvent mx p` | `ℝ≥0∞` | `Pr[p \| mx]` | `EvalDist/Defs/Basic.lean` |
| `probFailure mx` | `ℝ≥0∞` | `Pr[⊥ \| mx]` | `EvalDist/Defs/Basic.lean` |
| `support mx` | `Set α` | — | `EvalDist/Defs/Support.lean` |
| `finSupport mx` | `Finset α` | — | `EvalDist/Defs/Support.lean` |

### Kernel-valued interfaces

Use a `Measure α` for a closed computation and a `Kernel ρ α` when `ρ` is a semantic input:
an environment, initial state, public parameter, or previous protocol state. Do not encode the
input by immediately fixing it and returning a bare measure; doing so discards the measurability
needed for composition and data-processing theorems.

| Definition | Purpose | Defined in |
|-----------|---------|------------|
| `IsSubprobabilityKernel κ` | Every value of `κ` has total mass at most one | `ToMathlib/Probability/Kernel/Subprobability.lean` |
| `evalDistKernel f hf` | Measurable computation family `ρ → m α` as a kernel | `EvalDist/Kernel.lean` |
| `evalDistKernelOfDiscrete f` | Discrete-input specialization | `EvalDist/Kernel.lean` |
| `ReaderT.evalDistKernel` | Reader environment as kernel input | `EvalDist/Kernel.lean` |
| `StateT.evalDistKernel` | Initial state to result/final-state kernel | `EvalDist/Kernel.lean` |
| `ProbResponder.answerKernel` | Stateful interactive answer transition | `OracleComp/Coinductive/Responder.lean` |

`IsSubprobabilityKernel` is closed under `Kernel.const`, `restrict`, `map`, `comap`, `comp`,
`prod`, and powers. It implies `IsFiniteKernel`, so Mathlib's s-finite composition API is
available without restating a finiteness bound. A lossless family should additionally expose an
`IsMarkovKernel` instance or theorem.
`evalDistKernel`, its discrete-input specialization, and the reader/state wrappers infer
`IsMarkovKernel` from probability-measure instances for their output family. The reader/state
discrete wrappers also expose subprobability instances directly. `StateT.evalDist_run'` simplifies
the successful-output denotation to its first marginal before the upstream `run'` computation rule
unfolds; consumers do not need to supply the measurable-map equation.

`ProbabilitySemantics` is the total/lossless semantics bundle used by transformer adapters.
The lower-level `MeasureSemanticsVia` continues to describe potentially lossy surface semantics.
Import `VCVio.EvalDist.Defs.Semantics.Core` for native bundles and
`VCVio.EvalDist.MeasureSemantics` for effect-preserving transformer observations. These paths
contain no PMF/SPMF backend; `Defs.Semantics` additionally exports the discrete compatibility
bundles. Bundled `evalDist` observations infer `IsSubprobabilityMeasure` and `IsFiniteMeasure`.
Known probability certificates propagate through bundling, and bundled kernels infer
`IsMarkovKernel` from certificates for their output family. The total semantics bundle's bare
denotation and effect-preserving `optionT`, `exceptT`, and `writerT` observations infer
`IsProbabilityMeasure`; their total mass simplifies to one with `simp`.

Mass properties and measurable spaces have different roles. `evalDist` always supplies the
subprobability bound, but successful-output semantics cannot supply a probability certificate
for a computation that may fail. Exact mass preservation through arbitrary maps and binds also
needs the appropriate measurability proof. A named measure or kernel should export its guaranteed
instances once; consumers should not repeatedly unfold it or redeclare the same instance.
Lean's instance search does not prove arbitrary mass equations or unfold every named wrapper.

For `ProbResponder`, the kernel is authoritative. `ProbResponder.IsExecutable` optionally carries
a coherent realization `ProbResponder.IsExecutable.answerSPMF` for machine execution.
Executable state and answer spaces must have measurable singletons, so equality with
the authoritative kernel determines every executable point mass and therefore the entire SPMF.
Pullback along an interface lens preserves executability only when the transported answer space
also has measurable singletons. This separate capability is important: abstract cryptographic
caches need not be countable, while a kernel-native responder need not have any executable SPMF
realization.

#### Adoption audit

| Area | Decision | Rationale / next integration point |
|------|----------|------------------------------------|
| Closed `evalDist`, advantages, couplings | Keep `Measure` | There is no semantic input to bundle. |
| `ReaderT` and `StateT` observations | Use `Kernel` now | Environment/state is exactly the kernel input; use the adapters above. |
| Stateful responders and wired rounds | Use `Kernel` now | `answerKernel`, `stepAgainstKernel`, and kernel powers model transitions compositionally. |
| Executable `QueryImpl`, `simulateQ`, machine runs | Keep monadic/SPMF syntax | These are programs and evaluators; cross to kernels at observation boundaries. |
| KL/data-processing continuations | Use `Kernel` now | `KLDivergence.denoteKernel` is implemented through `evalDistKernelOfDiscrete`. |
| Query tracing, caches, costs, enforcement | Migrate observations, not handlers | Add kernel views of their `StateT` runs when a theorem composes distributions across states. |
| Crypto functions parameterized by keys/messages/security parameter | Add kernels when composed probabilistically | A plain function remains clearer until measurability or data processing is actually used. |
| UC/open-process runtime | Defer to an observation boundary | Structural process syntax has no canonical measurable space; bundle a kernel only for a chosen execution/observation model. |
| Program-logic predicates and tactics | Keep computation syntax | Their job is to reason before denotation. Add kernel bridge lemmas, not kernel-valued syntax. |

When introducing a new kernel, require the real measurable-space assumptions or bundle them with
the semantic object. Do not install global `MeasurableSpace := ⊤` instances merely to discharge a
proof. For an intentionally discrete local model, `evalDistKernelOfDiscrete` or a locally bundled
measurable space is the explicit escape hatch.
For generic output types, prefer `[MeasurableSpace α]` and structural instances for products,
options, and subtypes. A local `MeasurableSpace := ⊤` deliberately selects discrete semantics;
it is not an extra proof of a property of an already chosen measure. Intermediate choices made
only to normalize a computation belong inside the semantic API, as in `prEvent` and the native
constant-continuation laws.

### Measure-native interfaces

| Definition | Purpose | Defined in |
|-----------|---------|------------|
| `Measure.etvDist` / `Measure.tvDist` | Total variation on arbitrary subprobability measures | `ToMathlib/MeasureTheory/Measure/TotalVariation.lean` |
| `measureETVDist` / `measureTVDist` | Total variation directly on `𝒟[…]` | `EvalDist/MeasureTVDist.lean` |
| `Measure.Coupling` | Joint measure with prescribed marginals | `ToMathlib/MeasureTheory/Measure/Coupling.lean` |
| `MeasureProgramLogic.RelWP` | Almost-everywhere relational postcondition under a measure coupling | `ProgramLogic/Relational/Measure.lean` |
| `MeasureProgramLogic.eRelWP` | Best coupled `lintegral` post-expectation | `ProgramLogic/Relational/Measure.lean` |

## ProbComp and Sampling

`ProbComp α = OracleComp unifSpec α` — computations with only uniform sampling.

### Sampling notations

| Notation | Function | Type | Requirement |
|----------|----------|------|-------------|
| `$ᵗ T` | `uniformSample` | `ProbComp T` | `[SampleableType T]` |
| `$[0..n]` | `uniformFin n` | `ProbComp (Fin (n + 1))` | — |
| `$[n⋯m]` | `uniformRange n m` | `ProbComp (Fin (m + 1))` | `n < m` |
| `$ xs` | `uniformSelect` | `OptionT ProbComp β` | `[HasUniformSelect cont β]` |
| `$! xs` | `uniformSelect!` | `ProbComp β` | `[HasUniformSelect! cont β]` |

### SampleableType instances

Available for: `Bool`, `Fin n` (for `[NeZero n]`), `ZMod n`, `BitVec n`, `α × β` (from components), `Vector α n`, `Fin n → α`, `Matrix`.

### HasUniformSelect instances

- `$ xs` works for `List`, `Finset`, `Array` (can fail with `none` on empty)
- `$! xs` works for `Vector α (n+1)`, `List.Vector α (n+1)` (guaranteed non-empty)

## Simp Lemma Catalog

### Pure

| Lemma | Statement |
|-------|-----------|
| `evalDist_pure` | `𝒟[(pure x : m α)] = Measure.dirac x` |
| `evalSPMF_pure` | `evalSPMF (pure x : m α) = pure x` |
| `probOutput_pure` | `Pr[= x \| pure y] = if x = y then 1 else 0` |
| `probOutput_pure_self` | `Pr[= x \| pure x] = 1` |
| `probEvent_pure` | `Pr[p \| pure x] = if p x then 1 else 0` |
| `probFailure_pure` | `Pr[⊥ \| pure x] = 0` |
| `support_pure` | `support (pure x) = {x}` |

### Bind

| Lemma | Statement |
|-------|-----------|
| `evalDist_bind` | measure bind, with measurable continuation |
| `evalDist_bind_of_discrete` | measure bind on a discrete source space |
| `evalSPMF_bind` | `evalSPMF (mx >>= my) = evalSPMF mx >>= fun x => evalSPMF (my x)` |
| `probOutput_bind_eq_tsum` | `Pr[= y \| mx >>= my] = ∑' x, Pr[= x \| mx] * Pr[= y \| my x]` |
| `probEvent_bind_eq_tsum` | `Pr[q \| mx >>= my] = ∑' x, Pr[= x \| mx] * Pr[q \| my x]` |
| `probFailure_bind_eq_add_tsum` | `Pr[⊥ \| mx >>= my] = Pr[⊥ \| mx] + ∑' x, Pr[= x \| mx] * Pr[⊥ \| my x]` |
| `support_bind` | `support (mx >>= my) = ⋃ x ∈ support mx, support (my x)` |
| `finSupport_bind` | `finSupport (mx >>= my) = (finSupport mx).biUnion (fun x => finSupport (my x))` |

### Bind (constant continuation)

| Lemma | Statement |
|-------|-----------|
| `probOutput_bind_const` | `Pr[= y \| mx >>= fun _ => my] = (1 - Pr[⊥ \| mx]) * Pr[= y \| my]` |
| `probEvent_bind_const` | `Pr[p \| mx >>= fun _ => my] = (1 - Pr[⊥ \| mx]) * Pr[p \| my]` |

### Map

| Lemma | Statement |
|-------|-----------|
| `evalSPMF_map` | `evalSPMF (f <$> mx) = f <$> evalSPMF mx` |
| `probEvent_map` | `Pr[q \| f <$> mx] = Pr[q ∘ f \| mx]` |
| `probFailure_map` | `Pr[⊥ \| f <$> mx] = Pr[⊥ \| mx]` |
| `support_map` | `support (f <$> mx) = f '' support mx` |
| `probOutput_map_injective` | `f.Injective → Pr[= f x \| f <$> mx] = Pr[= x \| mx]` |

### Bind swapping

| Lemma | Use |
|-------|-----|
| `probEvent_bind_bind_swap` | Swap two independent binds (used internally by `vcstep` probability-equality rewrites) |
| `probOutput_bind_congr` | Congruence: equal on support → equal probability |
| `probEvent_bind_congr` | Same for events |

### Zero / membership

| Lemma | Use |
|-------|-----|
| `probOutput_eq_zero_of_not_mem_support` | `x ∉ support mx → Pr[= x \| mx] = 0` |
| `probOutput_bind_eq_tsum_subtype` | Restrict tsum to `support mx` |
| `probOutput_bind_eq_sum_finSupport` | Finite sum over `finSupport` |

## Decision Tree: Which Lemma Do I Reach For?

1. **Goal is `Pr[= y | mx >>= my] = ...`?**
   → Start with `probOutput_bind_eq_tsum`

2. **Goal is `Pr[p | mx >>= my] = ...`?**
   → Start with `probEvent_bind_eq_tsum`

3. **Need to swap two binds?**
   → Use `vcstep` if the swap should close the equality
   → Use `vcstep rw` / `vcstep rw under n` if you need an explicit rewrite step

4. **Need `Pr[= y | f <$> mx]`?**
   → If `f` is injective: `probOutput_map_injective`
   → Otherwise: `probOutput_map_eq_tsum_subtype` or `probOutput_map_eq_sum_finSupport_ite`

5. **Need to restrict a sum to support?**
   → `probOutput_bind_eq_tsum_subtype` or `probOutput_bind_eq_sum_finSupport`

6. **Continuation doesn't depend on result?**
   → `probOutput_bind_const` / `probEvent_bind_const`

7. **Two computations have same distribution?**
   → For legacy coupling lemmas, show `evalSPMF oa = evalSPMF ob`, or use
     `relTriple_eqRel_of_evalSPMF_eq`. For Mathlib probability results, compare `𝒟[oa]` and `𝒟[ob]`.

## `grind` vs `simp` on Probability Goals

`grind` and `simp` have complementary strengths here, and reaching for the wrong one is the most
common way to get a `grind` that hangs.

**Use `simp` to compute a concrete probability or factor structure.** `simp` evaluates
`Pr[= x | $ᵗ T]`, `Pr[p | $ᵗ T]`, products of uniform draws, etc.; `grind` is not an `ℝ≥0∞`/`Fintype.card`
arithmetic engine and will not finish these (it fails fast).

**Use `grind` for symbolic / membership / directed-iff goals.** Equiprobability
(`Pr[= x | $ᵗ T] = Pr[= y | $ᵗ T]`), `x ∈ support (…)`, `Pr[= x | mx] = 0 ↔ x ∉ support mx`, and
similar are squarely in `grind`'s wheelhouse.

**Why some characterization lemmas are `@[simp]` but not `@[grind]`.** A characterization whose RHS
introduces an *unbounded* quantifier or set over the support —
`Pr[…] = 0/1 ↔ ∃/∀ x ∈ support …`, `support = {x}`, `support = ∅` — is a `grind` **saturation
hazard**: as `grind` case-splits the iff it instantiates and Skolemizes the support quantifier into
fresh witnesses, which the always-tagged `bind`-expansion lemmas (`support_bind`,
`probFailure_bind_eq_add_tsum`, `mem_support_bind_iff`, …) re-expand into yet more `support`/`Pr[…]`
terms, with no finite grounding (`support ($ᵗ α) = Set.univ` is infinite). The hazard is
**combinatorial, not per-lemma**: no single one of these lemmas saturates `grind` on its own (restore
any one and a `grind` that should fail fast stays fast), but tagged *together* they form a re-trigger
cycle — restoring all of them makes that same `grind` run ~25× longer. The **hub of the cycle is the
`probEvent_eq_one_iff` family**: its RHS `Pr[⊥|mx]=0 ∧ ∀ x∈support, p x` couples the `probEvent`,
`probFailure`, and `support` layers at once (drop it and the blow-up roughly quarters). So that
family, together with the `∃`-Skolemizing `probEvent_ne_zero_iff` and the `probEvent_eq_zero_iff`
families, is kept `@[simp]`-only (fixed orientation, no case-split — safe). The *directed
single-variable* membership bridges (`probOutput_eq_zero_iff : … ↔ x ∉ support`, `probOutput_pos_iff`,
`mem_finSupport_iff`, `mem_finSupport_iff_mem_support`) are confluent and stay `@[grind =]`.

Lemmas kept `@[simp]`-only by this rule (in `EvalDist/Defs/Basic.lean` unless noted):
`probEvent_eq_zero_iff(')`, `probEvent_ne_zero_iff(')`, `probEvent_eq_one_iff(')`,
`one_eq_probEvent_iff(')`, `probOutput_eq_one_iff`, `one_eq_probOutput_iff`, `probFailure_eq_one_iff`;
and `mem_support_bind_iff` / `mem_finSupport_bind_iff` (untagged — `support_bind` / `finSupport_bind`
are the `simp` forms).

**Support-quantifier lemmas verified safe in isolation, kept `@[grind =]`.** A few carry the support
quantifier yet sit *outside* the `probEvent_eq_one_iff` hub cycle and add no measurable `grind` cost
on their own, so they keep their `grind` tag: `probEvent_pos_iff(')`, `probOutput_eq_one_iff'` (the
mirror of the never-dropped `one_eq_probOutput_iff'` — both are the `finSupport`-singleton form), and
`probFailure_bind_eq_zero_iff` (in `EvalDist/Monad/Basic.lean`). These are safe **only while the hub
family stays `@[simp]`-only**: re-tagging the `probEvent_eq_one_iff` family alongside them re-forms the
saturation cycle. `VCVioTest/LongChainPrograms.lean` is the 10+-step stress benchmark for exactly
this.

**If a `grind` proof needs one of these, re-supply it locally:** `grind [probEvent_eq_zero_iff]`. This
keeps the bridge out of the default set (so naive `grind` on a probability goal fails fast instead of
hanging) while letting the proof that genuinely needs it opt in.

**`Set.Nonempty`-phrased companions stay in the default `grind` set.** `grind` keeps `Set.Nonempty`
atomic (it does not unfold it to `∃ x ∈ support`), so a characterization phrased via `Nonempty`
carries the same information without the saturating quantifier. `probFailure_eq_one_iff_not_nonempty`
(`Pr[⊥ | mx] = 1 ↔ ¬ (support mx).Nonempty`) is the `grind`-friendly companion to the `simp`-only
`probFailure_eq_one_iff` (`… ↔ support mx = ∅`); reach for the `Nonempty` form when a `grind` proof
needs to reason about a computation failing (or not) with probability one.
`support_uniformSample_nonempty` (`(support ($ᵗ α)).Nonempty`, `@[grind]`) closes the loop, letting
`grind` conclude e.g. `Pr[⊥ | $ᵗ α] ≠ 1` end-to-end.

The event-probability versions follow the same recipe with the *filtered* support `{x ∈ support mx | p x}`
(the reachable outputs satisfying `p`): `probEvent_eq_zero_iff_not_nonempty`
(`Pr[ p | mx] = 0 ↔ ¬ {x ∈ support mx | p x}.Nonempty`) is the `@[grind =]` companion to the
`simp`-only `probEvent_eq_zero_iff`. Its sibling `probEvent_ne_zero_iff_nonempty` (`Pr[ p | mx] ≠ 0 ↔ …`)
exists but is deliberately **untagged**: the trio of `Nonempty` companions tagged together re-forms
a saturation cycle in the *generic-monad* context (`grind` on the `probEvent_eq_one_iff` statement
shape times out instead of failing fast; dropping any one of the three restores fail-fast), and
dropping the `≠ 0` sibling is free — `grind` recovers `≠ 0 ↔ Nonempty` from the kept
`= 0 ↔ ¬ Nonempty` form by classical negation. The `Pr[…] = 1` companions are deliberately
*omitted* entirely: a `Nonempty`-phrased `probEvent_eq_one` keeps its `Pr[⊥ | mx] = 0` conjunct,
which re-couples it to the hub family; the `= 1` cases use `grind [probEvent_eq_one_iff]` opt-in
instead. `VCVioTest/GrindFailFast.lean` gates all of this: each dropped lemma has a
`fail_if_success grind` + `grind [<lemma>]` example over a generic `m`, so both a bad re-tag
(bare `grind` starts succeeding) and a new saturation (the timeout escapes `fail_if_success`)
fail the build loudly.

**Monad/functor laws normalise structure for `grind`.** `bind_pure`, `bind_assoc`, and
`map_pure` are tagged `@[grind =]` (in `EvalDist/Monad/Basic.lean`); `pure_bind` is already in the
default set from core (`attribute [grind <=] pure_bind` in `Init.Control.Lawful`), so it is not
re-tagged here. They are confluent rewrites, so
`grind` collapses a computation's structure (`mx >>= pure = mx`, `pure a >>= f = f a`, …) *before*
falling into `probOutput`/`tsum` expansion — turning what would otherwise be a `grind` *explosion* on
a `bind`/`pure`-shaped probability/support/distribution equality into a quick solve
(`Pr[= x | mx >>= pure] = Pr[= x | mx]`, `𝒮[do let x ← mx; pure x] = 𝒮[mx]`,
`support (do let b ← $ᵗ Bool; pure b) = Set.univ` all close by bare `grind`). `bind_pure_comp` /
`map_eq_bind` are omitted (function argument under a binder, unindexable). A *non-trivial*
`<$>` / `if` / `<*>` does not normalise to a `pure`, so those structured equalities stay
`simp`-terminal.

**Independent products factor via `@[grind norm]`, not E-matching.** The second factor of
`Pr[= z | (·, ·) <$> mx <*> my]` sits under a binder (`Seq.seq`'s `Unit → _` thunk), which
`grind`'s pattern compiler cannot index — tagging the factorization lemma `@[grind =]` yields an
"invalid pattern" error (so do `pure_seq`/`seq_pure`). The escape is `grind`'s *normalization*
phase: `probOutput_seq_map_prod_mk_eq_mul` is `@[simp high, grind norm]`, so bare `grind` factors
the applicative spelling (and closes e.g. equiprobability of a uniform product). The `bind`-spelled
product (`do let x ← mx; let y ← my; pure (x, y)`) remains `simp`-only — the second draw sits under
`bind`'s continuation, which the seq-keyed norm rule does not reach.

**`grind norm` can starve E-matching — use it sparingly.** Norm rules rewrite goal/hypothesis
terms *before* E-matching, so a norm rule whose result no longer matches the `@[grind =]` patterns
disconnects them. Concretely: `@[grind norm] bind_pure_comp` (`mx >>= fun a => pure (f a)` →
`f <$> mx`) closes a couple of `target(grind)` gaps but breaks the `replicate` gates — the goal's
do-block normalises to a `<$>` form while the E-matching-side `replicate` unfolds stay in `bind`
form, and the E-graph never connects the two. It is therefore deliberately **not** tagged. Gate any
new `@[grind norm]` candidate against all of `VCVioTest/{ProbabilityTactics,MonadProbability,`
`LongChainPrograms,GrindFailFast}.lean` before keeping it.

**Structural additions to the default set** (all gated in `VCVioTest/GrindFailFast.lean`):
`OracleComp.replicate` unfolds (`replicate_zero`, `replicate_succ_bind`, `replicate_pure`,
`replicateTR_*` — the proof-level loop combinator; core already grind-tags the `List.mapM` /
`foldlM` / `forIn` layer), `Functor.map_map`, `probEvent_False`/`probEvent_false`, and the
`simulateQ` routing layer (`QueryImpl.add_apply_inl/inr`, `simulateQ_add_liftComp_left/right`,
the `withBadFlag`/`withBadUpdate`/`flattenStateT` run-shapes, `simulateQ_option_elim(M)`). The
`simulateQ_add_liftComp` pair also *fixes a saturation*: bare `grind` used to time out on a routed
`simulateQ (impl₁ + impl₂)` goal over a lifted computation.

`VCVioTest/ProbabilityTactics.lean` is the living benchmark and **gate** for all of this: a broad
corpus of probability / event / failure / support / distribution facts organised by category, each
closed by a single *terminal* tactic. Where a fact closes by **both** `simp` and `grind`, both are
kept (the mirror), so each tactic stays exercised on that shape; where only one closes, the entry
is a *gap pair* (`fail_if_success (tac; done)` then the working closer, with a dated
`gap(tac, …)` reason), so the gap is machine-checked and expires the moment the set improves. A
regression in either tactic surfaces there in isolation. When adding probability automation, add
the corresponding battery rows and retire the guards it makes obsolete. The rules are in
*Normal forms and the tactic contract* below.

`VCVioTest/MonadProbability.lean` is the **generic-`m`** companion: the same gate over an abstract
monad `m` with the EvalDist instance stack (`[LawfulMonadLiftT m SPMF]`, …) and over the concrete
transformers (`OptionT`, `ExceptT`, `SPMF`, `Id`), where the lemmas are actually stated. It surfaces
facts `ProbComp` masks — chiefly the **failure factor**: over a monad that can fail,
`Pr[= y | mx *> my] = (1 - Pr[⊥ | mx]) * Pr[= y | my]` and `Pr[⊥ | mx <* my]` /
`Pr[⊥ | mf <*> mx]` are inclusion–exclusion (`Pr[⊥|a] + Pr[⊥|b] - Pr[⊥|a]*Pr[⊥|b]`); both collapse
to the `ProbComp` forms only because `Pr[⊥] = 0` there. New API filled along the way:
`probOutput_map` (the `probOutput`/`<$>` companion to `probEvent_map`, `@[grind =]`), `support_guard`,
and the `orElse` (`<|>`) probability lemmas for `OptionT (OracleComp spec)` (`probFailure_orElse` etc.).

**Opting out downstream.** VCVio deliberately extends the *default* `grind` set — the monad laws
above plus the probability/support bridges — and these tags are inherited by every project that
imports it. All of the standard escape hatches work if a downstream `grind` call misbehaves:
disable a rule per call (`grind [-bind_pure]`), ignore the default set entirely
(`grind only [the, lemmas, you, want]`), or unset a tag for a whole file
(`attribute [-grind] bind_pure`). `grind?` reports a minimal `grind only [...]` call for a goal it
closes, which is the easiest way to make a fragile call site independent of the default set.

## Normal forms and the tactic contract

### Registered interfaces

Use the tactic that matches the mathematical obligation:

| Obligation | Interface |
|---|---|
| Ordered expectations or postconditions | `gcongr with x hx` on `expectedValue` or `OracleComp.ProgramLogic.wp` exposes support membership. |
| An expectation of a mapped computation | `simp` precomposes the payoff using `expectedValue_map`, retaining the expectation head. |
| Directed replacement inside a probability bound | Import `Mathlib.Tactic.GRewrite`; use `grw [h]` for inequalities and `apply_rw [h]` for event implications. A support-restricted rewrite theorem can leave membership as a side goal. |
| Measure bind ordered in its continuation | `Measure.bind_mono_right_of_forall` supports `gcongr` and `grw`, with explicit `AEMeasurable` side conditions. Use `Measure.bind_mono_right` directly for an almost-everywhere bound. |
| A finite expectation on a finite result type | `finiteness` uses `expectedValue_ne_top_of_finite` / `wp_ne_top_of_finite` and asks for finite functional values. |
| A supplied finite bound on an arbitrary result type | Apply `expectedValue_ne_top_of_le mx hc h`; the bound remains explicit. |
| Nonnegative total variation arithmetic | Import `VCVio.EvalDist.TVDist.Positivity` and use `positivity`; this also arrives through `VCVio.ProgramLogic.Tactics`. |
| Measurability through optional or exception-valued maps | `fun_prop` uses `Option.measurable_map`, `Except.measurable_map`, and `Option.measurable_elim'` on arbitrary measurable spaces. |

For a local abbreviation hiding a probability, use a targeted `change` or `dsimp only` before
`finiteness`. For named definitions, `finiteness (add unfold [name])` is also available.
`finiteness [proof]` supplies an explicit finiteness fact. The tactic does not infer finiteness
of an expectation over an infinite result type merely from pointwise finiteness of its functional.

The registrations and their failure boundaries are exercised in `VCVioTest/Tactic/` and
`VCVioTest/ProgramLogic/GCongr.lean`. The expression-specific `fun_prop` rules avoid globally
registering eliminator theorems whose conclusion is the unrestricted `Measurable f`.

For a sum of oracle `wp` bounds, rewrite with `← OracleComp.ProgramLogic.wp_finsetSum`,
then apply `wp_le_const_of_support`. Use `wp_le_const_add_of_support` for a constant allowance
plus another postcondition. Both the oracle facade and `MAlgOrdered.wp` expose support membership
to `gcongr`; callers need no preparatory `change` or discrete expectation expansion.

See the [generalized-relation investigation](../reading/generalized-relation-automation.md) for
tested rewrite directions, theorem-shape requirements, and the distinction between `gcongr`
and `grw` registrations. Measure-bind rewriting requires importing
`ToMathlib.MeasureTheory.Measure.Monotone`; pointwise order does not discharge measurability.

### Normalization discipline

The simp, grind and `gcongr` sets of the probability layer are designed around one *normal-form
ladder*: one canonical spelling per rung, mass-left throughout, each rung reached from the one
above it by an existing pathway rather than by a per-rung twin lemma.

| rung | form | reached by |
|---|---|---|
| 0 closed | numerals, `(Fintype.card α)⁻¹`, `if … then 1 else 0`, `#{x \| p x} / Fintype.card α` | `simp` (`probOutput_pure/query/uniformSample/guard/ite`, `probOutput_bind_const`, `probOutput_map_equiv`) |
| 1 finite sum | `∑ x, Pr[= x \| mx] * g x` | `simp` from rung 2 through Mathlib's `@[simp] tsum_fintype`; `Finset.sum_boole`/`sum_ite_eq` finish |
| 2 tsum | `∑' x, Pr[= x \| mx] * g x`, which is `expectedValue mx g` | `grind` (bind expansion, `probOutput_bind_eq_tsum` is `@[grind =]`); `rw [probOutput_bind_eq_tsum, ← expectedValue_def]` exposes the expectation head |
| 3 integral | `∫⁻ x, g x ∂𝒟[mx]` | countable discrete compatibility measures admit the expectation bridge below; measure-native proofs can keep this form for Mathlib's integration API |

Mass-left is canonical: it is the orientation of Mathlib's `PMF.bind_apply`,
`PMF.toMeasure_bind_apply` and Bochner `integral_fintype`, of `expectedValue`, and of every
bind lemma in this library. Mathlib's `lintegral_countable'`/`lintegral_fintype` are mass-right;
they meet this library exactly once, inside the proof of the measure-to-façade bridge, never as a
normal form.

**What each tactic promises.**

- `simp` is the *structural* normalizer: it reaches a closed form when one exists, applies the
  monad laws, and collapses `∑'` to `∑` on a `Fintype`. It never expands a bind into a `tsum`
  (`gotchas.md` §10); `simp [probOutput_bind_eq_tsum]` is the documented one-step to the sum,
  and on a `Fintype` that call lands on rung 1 with no library lemma involved.
- `grind` is the *symbolic* closer after bind expansion: equiprobability, membership, directed
  iffs, `bind`/`pure`-normalised structure. It is not an `ℝ≥0∞`/`Fintype.card` arithmetic engine
  and must keep failing fast on the `Pr[…] = 0/1 ↔ …` characterization family
  (`VCVioTest/GrindFailFast.lean`).
- `gcongr` and `finiteness` are the *bound* closers, with `expectedValue` as the head symbol for
  rung 2. Rewrite a bind with `probOutput_bind_eq_tsum` and fold the sum with
  `← expectedValue_def` to expose that head. `expectedValue` is a `def` that `simp` does not
  unfold; its untagged `expectedValue_def` equation can be supplied explicitly to `rw` or `grind`.
- The measure side uses `𝒟[…]`, with `evalDist_pure` and `evalDist_bind` under
  `LawfulEvalDistSemantics`; bind also requires a measurable continuation. For `FreeM`,
  `PFunctor.IsMeasureSpec.Compatible` records agreement between the measure and probability
  query specifications. Under `DiscreteEvalDistCompatible`, the generic `evalDist_apply` connects
  measurable events to `Pr[...]`; `evalDist_apply_singleton` and `evalDist_apply_setOf` are its
  singleton-measurable and discrete-space specializations. On a discrete result space,
  `OracleComp.EvalDist.lintegral_evalDist` rewrites an integral against `𝒟[mx]` to
  `expectedValue mx g`, with no separate countability hypothesis. These are explicit coherence
  boundaries; measure-native proofs without discrete compatibility keep their measure denotation.

**What the gates enforce.** The gate files (`VCVioTest/ProbabilityTactics.lean`,
`MonadProbability.lean`, `GrindFailFast.lean`, `Tactic/*.lean`, `EvalDist/*.lean`) state
"goal family → one terminal tactic" and are the gate for every change to these sets:

1. *One terminal call.* A positive entry is `by <one tactic>` or a term: `simp`, `grind`,
   `gcongr`, `finiteness`, `simp [S]`, or `simp only [S]`.
2. *Known gaps are machine-checked and self-expiring.* A gap is a pair: `fail_if_success
   (tac; done)` on its own line, then the working closer, with a dated `gap(tac, date): reason`
   comment. The guard errors as soon as the set improves, so the PR that closes a gap retires
   the guard in the same diff. One guard covers a family of same-shaped entries when the family
   is named in the section note. (`fail_if_success` takes a tactic sequence, so the closer must be
   on its own line; bare `fail_if_success simp` passes only when `simp` makes *no progress*,
   hence the `(tac; done)` form for partial-progress gaps. Explicit no-progress checks keep
   bare `fail_if_success simp` to avoid an unreachable `done`. Bare `fail_if_success grind`
   already tests closure.)
3. *No multi-call scripts.* A `;`/multi-line script is allowed only as the closer of a gap pair.
   A one-call entry that stops closing is fixed in the set or filed as a dated gap pair, never by
   adding a second call.
4. *Normalizers pin their normal form.* For a normalizer such as `simp only [monad_norm]` or
   `handler_step`, follow the normalizing call with `guard_target =ₛ <expected form>` and then
   a closer.
5. *Negatives for every deliberate exclusion*: whatever these docs say is "deliberately not in
   the default set" has a `fail_if_success` entry.
6. *Fail fast stays fail fast*: a saturating `grind` is a deterministic timeout under the default
   heartbeat limit, which escapes `fail_if_success` and fails the build; gate files never raise
   the limit.

Warnings in `VCVioTest` fail CI, so a stale entry (an unused tactic, a redundant `grind`
parameter, a deprecated name) cannot linger. A PR that touches a simp/grind/`gcongr` set says
which rung its lemmas target, which gate entries it adds and which guards it retires, and which
library proofs got shorter; a set with no library caller is itself a finding.

## Common Mistakes

1. **Missing probability spec classes**: on `OracleComp spec`, `evalSPMF`/`probOutput`/`Pr[...]` require `[IsProbabilitySpec spec]`. Uniform/cardinality lemmas and support-probability lemmas require `[IsUniformSpec spec]`, not just `[spec.Fintype] [spec.Inhabited]`. Use `IsUniformSpec.ofFintypeInhabited spec` when a concrete finite inhabited spec should use uniform sampling. `𝒟[...]` additionally needs an ambient `MeasurableSpace` on the output.

2. **Carrying duplicate probability instances**: do not add a separate `[IsProbabilitySpec spec]` when `[IsUniformSpec spec]` is already in scope. `IsUniformSpec` extends `IsProbabilitySpec`; a second instance can make instance search ambiguous and may not describe the same distributions.

3. **Using `support` when `finSupport` is needed**: `probOutput_bind_eq_sum_finSupport` requires `[DecidableEq α]` and `[HasEvalFinset m]`.

4. **Forgetting `probOutput_eq_zero_of_not_mem_support`**: useful when restricting sums.

5. **`evalSPMF` on bare `query t`**: works directly when the expected type pins `query t` to a monadic form, since `query` resolves to `HasQuery.query`. Write `evalSPMF (query t : OracleComp spec _)` (or hand the result to a context that provides the same ascription). If you need the primitive `OracleQuery spec _` (e.g. for `OracleQuery.cont`), use `spec.query t` instead.

`evalDist.ae_of_forall_mem_support` converts a pathwise predicate into an almost-everywhere
predicate under its `MeasurableSet` premise. It uses core `MonadAttach` and native measure laws,
works for arbitrary chosen result spaces and failing computations, and needs no compatibility
class. `evalDist.apply_eq_zero_of_disjoint_support` gives the corresponding zero-mass event rule.
