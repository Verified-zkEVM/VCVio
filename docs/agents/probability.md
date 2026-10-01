# Probability Reasoning (EvalDist and ProbComp)

To convert code written against the removed discrete `Pr[…]` API, follow
[`probability-migration.md`](probability-migration.md).

For the cross-project survey of subprobability mass functions, Mathlib measures and kernels,
PolyFun coalgebraic limits, ArkLib, and Bluebell/Iris, see
[`Probability Semantics for Computations: Landscape and Design Options`](../reading/probability-semantics-landscape.md).
The accepted design is
[`Denotational Probability Semantics`](../reading/denotational-probability-semantics.md): use
Mathlib measures for closed denotations, kernels for environment/state-indexed computations, and
effect-preserving outcome types for transformers. The
[notation and computability account](../design/probability-notation-computability.md) records
which finite events can be evaluated exactly and which semantics require measurable proofs.
[`docs/reading/`](../reading/README.md) indexes the full design record.

`import VCVio.Foundations` is the public entry point for oracle, sampling, measure, kernel,
operational-support, unary/relational WP, and stateful security foundations. Its import closure
excludes Mathlib's `PMF`; `VCVioTest/Foundations.lean` checks this boundary. Across the library,
the `usesRetiredProbability` environment linter (`ToMathlib/Lint/LegacyProbability.lean`) reports
any declaration whose type or value uses `PMF` directly.

Handler instrumentation lives in `QueryImpl.Constructions.Core`, `Append.Core`, `WriterT.Core`,
`Tracing.Core`, `CountingOracle.Core`, and `LoggingOracle.Core`. Their public projection
equations transport any observation of the computation, including its chosen-space measure.
Query bounds, cache/programming handlers, state projections, and invariant reasoning use these
modules directly. Structural results need no uniform probability interpretation.
`StateT.OutputIndependent` compares output measures. Invariant-preserving prefixes may discard
their output and state without choosing measurable spaces on those discarded types.

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
same argument.

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
globally measurable equality relation; finite-tree reflexivity closes with plain `simp`,
including on uncountable output types.
`CouplingPost.bind_of_countable` composes pointwise coupling witnesses on countable marginal
concentration sets: measurability is needed only under the chosen initial joint law. Its proof
uses Mathlib's measurable modification API, not a globally measurable choice principle.
`relWP_bind_of_aemeasurable` and `lintegral_le_eRelWP_bind` accept an explicit almost everywhere
measurable family. The quantitative rule supplies a witness lower bound; it does not assert
existence of an optimal coupling or interchange a supremum with integration. A product of
arbitrary discrete measurable spaces need not itself be discrete. Do not hide that distinction
in an automatic relational assertion-algebra instance.
The qualitative `MAlgRelOrdered` instance for finite-response oracle trees
(`OracleComp.ProgramLogic.Relational.CouplingPost`) observes each output in its discrete
measurable structure. The source and final operational output sets are finite concentration
sets, so arbitrary final relations are handled by restricting to their countable measurable part.
This works for uncountable output types and weighted interpretations; it needs only finite
responses, without enumerations or uniformity. The anchoring to structural demonic WP and the
bijection rules hold under uniform response measures, where every reachable output has positive
mass.
The generic relational class and laws come from `PolyFun.Control.Monad.Algebra.Relational`.
`ToMathlib.Control.Monad.RelationalAlgebra` additionally installs the named upstream transformer
constructions for typeclass search. New code can select those constructions
explicitly. `MAlgRelOrdered.rwpExc` accepts one postcondition on both exception outcomes;
`rwpExcCases` packages four separate corner postconditions, while the one-sided and optional
case helpers remain available in `RelationalAlgebraAnchored`.

`VCVio.StateSeparating.MeasureDistEquiv` compares all adaptive client output measures under the
selected lawful interpretation. Its `of_step` rule retains each joint response/state law;
`prEvent_eq` transports final events, and the advantage rules permit replacing experiments
with different private-state types. `run_evalDist_eq` is the public observation equation.
Weighted interpretations can give a structurally possible answer zero mass; measure equivalence
therefore does not assert equality of operational support.

`evalDist_boolBias_bind_coin` is a generic fair-coin reduction for lawful measure semantics and
lossless Boolean branches. The probability-only security facade supplies its fair-coin law.
`SampleableType.evalDist_uniformSample_singleton` normalizes uniform singleton masses directly;
`Measure.apply_true_add_apply_false_eq_one` gives `simp` and `grind` the two-outcome mass law
without first unfolding the universal Boolean event into a finite set.

`VCVio.OracleComp.ProbComp.Basic` owns executable container sampling, and
`VCVio.OracleComp.Constructions.SampleableType.Basic` owns the `$ᵗ` notation class: a
canonical sampler `selectElem` with the single law `𝒟[$ᵗ β] = uniformOn Set.univ`.
Product and vector uniformity follow from product measures and bijective pushforwards.
`Nonempty`, `Finite` and full operational support are consequences of the law
(`SampleableType.nonempty` and `SampleableType.finite` are priority-100 instances,
`support_uniformSample` a `simp` lemma); enumeration is a separate computational choice.
An abstract result's `𝒟` still needs its chosen `MeasurableSpace`. Event notation hides intermediate
spaces, and uniformity certificates apply to any result space with measurable singletons.

`VCVio.EvalDist.Lossless` uses Mathlib's `IsProbabilityMeasure` directly. For a lossless prefix,
`evalDist.isProbabilityMeasure_bind_iff` characterizes a lossless bind by almost everywhere
lossless continuations. `isProbabilityMeasure_bind_of_ae` supplies the forward construction;
no structural positivity assumption or bind instance search is needed.

The [measure conversion roadmap](../design/measure-conversion-roadmap.md) records the owning
modules, standard proof conversions, theorem families, and validation gates.

`open scoped ExpectationWP.Probabilistic` selects bounded `Prob` expectations for any
lawful measure semantics. Public value laws connect them to quantitative WP and Lebesgue
integration; constants retain success mass. Plain `simp`, `gcongr`, and `grw` work on optional
computations and weighted oracles. The necessary reading of oracle WP delegates to PolyFun's
direct demonic core WP, which needs only lawful attachment. The exact ordered assertion algebra remains
available for free oracle trees. State and reader reasoning uses PolyFun's indexed operational
judgments and kernels; flattened support does not acquire an exact bind law.

The notation is measure-valued: `𝒟[mx] : Measure α` is the successful-output measure, and mass
missing from it is failure or nontermination. The generic classes and Giry laws live in
`VCVio.EvalDist.Defs.Measure.Core`; the direct free-program instances live in
`VCVio.EvalDist.PFunctorMeasure.Core`.
`Pr{let x ← mx; let y ← my x}[event]` is the event notation. The braces hold an ordinary Lean `do`
sequence: statements are separated by `;` or laid out as in a `do` block, and `let y := f x`,
destructuring draws and `if` are available. An action that continues on the following lines is
indented past its `let`, as in any `do` block, or parenthesized.
`Pr{let x ← mx}[x = a]` is the probability of the single output `a` and needs no measurable singletons.

`Pr{items}[t]` is the expectation of the event's indicator, `𝔼{items}[𝟙⟦t⟧]`, and `𝔼{items}[b]`
is the expectation of the value `b` over the draws of the sequence: each draw `let x ← a` is
core's weakest precondition `wp a (fun x => …) ⊥` under the measure interpretation
`ExpectationWP.wpMonad` of `a`'s monad (`VCVio.EvalDist.Expectation`), and the notation is
the translation of its sequence into these nested expectations:

| item | term |
|---|---|
| `let x ← e` (also `let x : τ ← e`, `let _ ← e`, a bare action `e`) | `wp⟦e⟧ fun x => …` |
| `let pat ← e` | `wp⟦e⟧ fun z => match z with \| pat => …` |
| `let x := v`, `have h : p := v` | `let x := v; …`, `have h : p := v; …` |
| `let x ← do …`, `let x ← if …`, a draw with a nested action `(← g)` | the draw of that program |
| an imperative tail (`let mut`, a loop, a do-level `if`) | one program `do tail; pure (v₁, …, vₖ)` of the variables it binds, observed from outside |

```lean
Pr{let x ← mx; let y ← my x}[p x y] = wp⟦mx⟧ fun x => wp⟦my x⟧ (predInd fun y => p x y)
```

Nothing is rewritten at elaboration: the term is the translation, so what a statement says is
what was written. A draw written as a bind, a map, a returned value or a `do` block stays as
written, `Pr{let y ← mx >>= f}[q y]` is `wp⟦mx >>= f⟧ (predInd q)`, and the normal form of a draw
chain is a proof-time notion: `simp only [expect_norm]` applies PolyFun's exact `wp` equations
(`ExactWPMonad.wp_bind`, `wp_map`, `wp_pure`, `wp_ite`, `wp_dite`, `wp_seq`, …), through
pre-procedures that keep the program's binder names, and the fold `wp_predInd_fold` of an
indicator observation `fun x => propInd t` into `predInd (fun x => t)`. Core's `wp` is the only
head, so the program logic, `vcgen` and the expectation laws apply to events directly. Neither
notation needs a measurable space on the outputs; `prEvent_eq_evalDist_map` relates an event to
the mass `𝒟[p <$> mx] {True}`, and `measurable_prEvent` makes a family of events measurable from
its selectors' measures.

An event observes the indicator `predInd p` of its predicate (`predInd p x = propInd (p x)`, by
`predInd_apply`), so the predicate is an argument: `simp` keys, `grind` patterns and `gcongr` see
it, and an event is never confused with a constant observation. Each draw is read in the
expectation interpretation of its own monad, so a sequence may draw from several monads, an
`OptionT ProbComp` adversary inside a `ProbComp` game, and the failure of a draw contributes
nothing to the event. The interpretation of a draw's monad is `ExpectationWP`: the
successful-output measure for a base monad (`ExpectationWP.ofMeasure`), and core's lift of the
base's interpretation for `OptionT` and `ExceptT` (`ExpectationWP.optionT`, `exceptT`), the one
`vcgen` and the readings use, with the bottom exception assertion; `OptionT.wp_eq_run` reads a
lifted expectation through the run, and `OptionT.wp_ofMeasure_eq` / `ExceptT.wp_ofMeasure_eq`
state that the lift and the stack's measure interpretation agree (*Transformer stacks* in
`program-logic.md`). The simp set `expect_eval` continues past the normal form: it unfolds
`replicate`, `List.mapM` and `List.foldlM` by one iteration and gives the value of a query or a
uniform draw (`wp_query`, `wp_uniformSample`), so `simp only [expect_norm, expect_eval]` proves
an equation between one program's expectation and its value. The notations need lawful measure
semantics (`[LawfulMonad m] [LawfulEvalDistSemantics m]`): a semantics whose bind law fails, such
as a free monad over continuous answers where a continuation need not be measurable, has no
expectations, and its events are stated on `𝒟[…]`. A product of indicators merges into the
indicator of the conjunction (`propInd_mul_propInd`), so an expectation that multiplies
indicators, as a guard does, folds back into an event.

`prEvent_bind`, `prEvent_map`, `prEvent_pure`, `prEvent_ite` and `prEvent_dite` state what those
equations give for a literal event `wp⟦mx >>= f⟧ (predInd p)`; `simp` uses the `wp` equations
themselves. Leaf laws are stated for every observation (`Option.wp_none`, `wp_failure`, `wp_lift`,
`wp_guard`), so they apply to events and expectations alike. Over a uniform draw, an event is
counted (`prEvent_uniformSample`) and any other observation averaged (`wp_uniformSample_eq_sum`,
through a simproc that leaves events to the counting law).

Goals display an expectation as the notation it elaborates from: `Pr{…}[p x]` when its innermost
observation is `predInd p` or `propInd t`, and `𝔼{…}[…]` otherwise, with a draw that is a bind,
a map or a `do` block displayed as such, which is how a goal that still needs
`simp only [expect_norm]` shows it. What is displayed elaborates back to the term displayed,
except that a draw whose display carries no monad, such as `pure a`, needs an ascription or
`pp.analyze` to be read back. A literal expectation is written `wp⟦mx⟧ g`.

In a definition, name an experiment as a computation and take one event of it,
`Pr{let b ← exp adv}[b = true]`; every draw is stored as written.

### Writing events with `do` sequences

Because the braces hold an ordinary `do` sequence, Lean's `do` sugar is available with its
bindings in scope for the event. State an experiment the way it reads, rather than
pre-composing it into one computation with `>>=` and `<$>`:

```lean
Pr{let x ← mx; let y := x + 1; let z ← my y}[z = y]      -- pure `let`s
Pr{let (pk, sk) ← keygen; let c ← enc pk m}[dec sk c = m] -- destructuring draws
Pr{let z ← f (← mx) (← my)}[z = 0]                       -- nested actions `(← e)`
Pr{let b ← $ᵗ Bool; let x ← if b then m₁ else m₂}[x = 3]  -- branches on a draw
Pr{let o ← mo; let x ← match o with | some a => pure a | none => mx}[x = 1]
Pr{let mut s := 0; for i in [1, 2, 3] do s := s + (← my i)}[s = 3]  -- `let mut` and loops
Pr{let x : ZMod q ← mx}[x = 0]                            -- type ascriptions
```

The event in the brackets may mention every binding of the sequence, including destructured
components and mutable variables. The observation sits outside the sequence's programs, so a
`return` at the top level of the braces is rejected (a computation that returns early is bound
as `let x ← (do …)`), and bindings inside a tail's `if` or loop are not visible to the event. An
event over a loop keeps its `forIn` draw; the default `simp` set unrolls a loop over a literal
list, and other loops are reasoned about with the loop's own lemmas or `wp⟦·⟧`. A `match` with
several cases also stays a draw of its own.

`mx =ᵈ my` (`EvalDistEq`, in `VCVio.EvalDist.EvalDistEq`) states that two computations, possibly
in different monads, give every event the same probability. It needs no measurable space on the
output:
- `EvalDistEq.evalDist_eq` gives equal output measures in every structure;
- `EvalDistEq.of_evalDist_eq` proves it from equal measures in a discrete structure;
- `evalDistEq_iff_forall_prEvent_eq_output` reduces it to point masses on countable outputs;
- `EvalDistEq.wp_eq` gives equal expectations of every observation.

It is an equivalence usable in `calc`, and its bind and map congruences are registered for
`gcongr` and `grw`. A lemma whose selector's type depends on an implicit argument, such as a
query index, is rewritten with that argument supplied: `Functor.map` unifies the selector before
the computation. `prEvent_eq_evalDist` identifies an event with the measure of its set for a
measurable predicate; `prEvent_eq_evalDist_of_discrete` discharges that condition on a discrete
output space. `prEvent_eq_evalDist_decide` equates an event with a Boolean experiment's final
`decide`, without requiring a measurable space on the intermediate result. Factor the common
sampling run once when both forms of a security game are public. For an optional computation,
successful outputs are measured through `Measure.comap some`, so failure contributes no mass.
The `OptionT` measure instance needs only a measure semantics on the base monad.
`OptionT` and `ExceptT` inherit the base pure certificate and, for lawful base monads,
the full measurable-bind certificate. Generic bind laws require measurability only of the
successful-output family, rather than the whole run measure. An auxiliary discrete source space
and the base map law transport the source measure back to its selected space.
`VCVio.EvalDist.Monad.Option` collapses a lifted draw followed by a guard into one event
condition: `simp` and `grind` turn the guard and final event into their conjunction. Callers need
no measurable space on that intermediate type. A constant output map after the guard has the same
normalization rule, so monad normalization preserves this automation. The guarded unit-output
measure is its event probability times `Measure.dirac ()`. `OptionT.prEvent_eq_run` observes present
values in the underlying run, and `OptionT.prEvent_lift` preserves an event through a lift.
`VCVio.EvalDist.Defs.Measure.Deterministic` gives `Id`, `Option`, and `Except` Dirac/zero
semantics. Every `Id` value and successful `Option`/`Except` constructor infers its
probability-measure instance; arbitrary optional/exceptional values infer only the
subprobability bound. Bare `Except` observes no errors and needs no measurable space on its error
type. `ExceptT` instead interprets its base run and uses the inherited coproduct space on errors
and outputs. Deterministic final events simplify to their propositional indicators with `simp`
and `grind`, using `Measure.dirac_apply_singleton_true`.
`VCVio.OracleComp.Support` exposes the oracle facade over PolyFun's attachment semantics, while
`PolyFun.PFunctor.Free.Support` owns the universe-polymorphic map/object equations and
finite/nonempty bounds. VCVio's `PFunctorSupport` module reexports that API. Support-aware bind
congruence needs only weakly lawful attachment, through PolyFun's public generic rule.
`VCVio.OracleComp.EvalDist.Measure` connects structural bounds to almost-everywhere bounds
under any discrete-answer response measures; neither uniformity nor positive singleton masses
is required for that direction. `VCVio.ProgramLogic.Unary.WP.OracleMeasure` exposes these
bounds on expectation WP, including `gcongr` support hypotheses and additive allowances.
`VCVio.EvalDist.Defs.Support` and its `Support.Failure` module expose operational support
without any probability semantics. Optional failure has empty support under Lean's
`LawfulMonadAttach`. Its pure-output elimination law suffices: no `ExactMonadAttach` is needed,
including over state and reader bases. `HasEvalSet.LawfulFailure` only requires an
`Alternative` and attachment.
The independent `LawfulFailureEvalDistSemantics` mixin certifies zero measure for failure.
`Option` and `OptionT` export that certificate; `OptionT` needs only the base pure law.
`VCVio.EvalDist.Monad.Failure` makes failure before a continuation, a constantly failing
continuation, and a final event after failure normalize to zero with `simp` and `grind`.
These composition laws need no attachment or measurable-space instance on intermediate results.
The successful-output pullback equations `OptionT.evalDist_apply` and `ExceptT.evalDist_apply`
hold on arbitrary sets, without a measurability argument.
`SampleableType.prEvent_uniformSample` counts a decidable event as its accepted fraction of finite
outputs, using Mathlib's `uniformOn` and counting measure.
`VCVio.EvalDist.Defs.Measure.FinRatPMF` gives the executable rational sampler measure
semantics. `Raw.toMeasure` is a finite sum of weighted Dirac measures; pure and measurable bind
have the generic laws on arbitrary measurable spaces. `Raw.evalDist_apply` computes decidable
event masses as rational sums, and the singleton simp lemma reduces to `Raw.prob`.
`FinRatPMF.finRatImpl.evalDist_simulateQ` and `prEvent_simulateQ` identify executable evaluation
with the uniform oracle interpretation.
`VCVio.EvalDist.Expectation` gives every monad with lawful measure semantics its expectations.
`wp⟦mx⟧ g` is the expectation of `g : α → ℝ≥0∞` over the outputs of `mx`. It is core's
`wp mx g ⊥` under the measure interpretation `ExpectationWP.wpMonad m`, which is built from
the ordered expectation algebra `ExpectationWP.algebra m` and is exact (PolyFun's
`ExactWPMonad`). The interpretation is supplied explicitly rather than found by instance search.
For oracle computations it is the core `WPMonad` instance, and
`open scoped ExpectationWP.Lower` selects it for any other lawful monad, so
`wp mx g ⊥` and core triples read expectations.

The laws in `ExpectationWP` need no measurable structure on the outputs:
- `wp_mono` (`gcongr`), `wp_congr`, `wp_zero`, `wp_add`;
- `wp_const_mul`, `wp_mul_const`, `wp_finsetSum`, `wp_pure`, `wp_bind`, `wp_map`.

`wp_eq_lintegral` bridges to Mathlib's lintegral for a measurable observation, and
`wp_eq_lintegral_comap` does so in the σ-algebra the observation induces. Monotone suprema and
almost-everywhere comparisons (`wp_iSup`, `wp_mono_ae`, `wp_le_const_mul_mass_add`) keep their
measurability hypotheses. In `VCVio.EvalDist.ProbabilityNotation`:
- a constant keeps the successful-mass factor, `wp_const : wp⟦mx⟧ (fun _ ↦ c) = c * Pr{let _ ← mx}[True]`;
- the event and sum laws are `wp_le_of_forall_le`, `le_wp_of_forall_le`, `wp_le_prEvent_add`,
  `wp_eq_sum_fintype` and `wp_eq_tsum_of_countable`.

For oracle computations with finite answers, `OracleComp.wp_eq_tsum` sums over outputs without
a countability assumption. `OracleComp.wp_swap` commutes independent draws,
including those of an event. `wp_mono_of_support` and `wp_congr_of_support` compare observations on the
reachable outputs; `wp_mono_of_support` is the preferred `gcongr` rule.

The sequencing laws in `VCVio.EvalDist.Monad.Seq.Measure` identify paired draws with
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
For discrete-answer oracle specifications, `𝒟[mx]` has an automatic
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
Every `𝒟[mx]` automatically satisfies `IsSubprobabilityMeasure`. Products inherit this bound from
their two factors. The upper mass bound also propagates automatically through raw `Measure.map`,
whose nonmeasurable fallback has mass at most one. For raw `Measure.bind`, use
`isSubprobabilityMeasure_bind` with an explicit almost-everywhere measurability proof. Exact mass
preservation requires measurability. `pure` infers a probability-measure instance even for
continuous-answer specifications. Lifting a computation whose measure already has an
`IsProbabilityMeasure` instance into `OptionT` or `ExceptT` also infers that instance,
including through `liftM`. These lifts introduce no failure mass; arbitrary optional or exceptional
computations still need a losslessness certificate. `FreeM.isProbabilityMeasure_evalDist_lift`
supplies a single query's probability proof. It is a theorem: the dependent output type
`P.B a` gives a projection key that instance search cannot match against a concrete reduced type
such as `ℝ`. A general continuous program still requires a continuation measurability proof.
`FreeM.denote` over discrete answers, `FreeM.pathMeasure`, and `FreeM.queryCountMeasure` export
probability instances; proofs should not install them locally. `evalDist_failure_eq_zero`
simplifies failure to zero under its `LawfulFailureEvalDistSemantics` certificate.
`Measure.dropNone` preserves the subprobability instance of an optional measure, and
`Measure.withFailure` automatically completes any subprobability measure to a probability measure.
The `evalDistWithFailure` wrapper exports the same probability-measure instance.
The mass at `none` needs no discreteness hypothesis: the optional coproduct makes this singleton
measurable for every result space. Successful singleton masses need only measurable singletons.
`prEvent_eq_evalDist_singleton` identifies an equality event with its singleton mass under that
weaker assumption. It therefore works with inherited product spaces even when they are not discrete.
`FreeM.evalDist_lift_bind_pure` handles a measurable pure function after a single operation
without requiring discrete answer spaces; continuous final-event proofs can use this directly.
`le_evalDist_bind_apply` transports an almost-everywhere lower bound through a lossless draw;
its monad is generic and its event need only be measurable.

A runtime assigns every experiment a subprobability measure `runtime.evalDist exp`, so
`measure_le_one` and `measure_ne_top` apply directly. An instrumented experiment recording
success and a Boolean selector uses `Measure.fst` of its measure for the success marginal.
`Measure.fst_apply_eq_add` splits a marginal event into the two disjoint selector events.
The SLH-DSA `advantage_eq_arms` and `sameMessageAdvantage_eq_arms` equations use that partition
without caller-supplied evaluator laws; the runtime already bundles its measurable-map law.
Their named FORS/hypertree and randomizer halves have exported defining equations and exact
partition theorems, so consumers do not need unfolding hypotheses.
`OracleComp.evalDist_map_const` handles a constant output map without a measurable space on
the discarded result type. This keeps default `simp` on measure laws after monad normalization
turns a constant return into a map.

`lintegral_evalDist_bind` states the tower law with a measurable continuation;
`lintegral_evalDist_bind_of_discrete` supplies that proof for a discrete common draw.
`lintegral_evalDist_map_add_nat` integrates an incremented natural-valued observation and
retains its successful-mass factor. The intermediate type needs no measurable space.
Lossless oracle programs infer that factor as one, so default `simp` proves the increment law.
`lintegral_evalDist_map_const_add_nat` supplies the curried `Nat.add` form for `grind`;
lambda-bound parameters are unavailable as automatic `grind` patterns.
`lintegral_uniformOn_univ` averages over a finite uniform measure, including the empty space
and infinite integrands. `ProbComp.lintegral_evalDist_uniformFin` exposes that law for a draw.

The drawing loop and its measure-valued length integrals live in
`VCVio.OracleComp.Constructions.WithoutReplacement.Basic`. Observe `List.length` before
integrating: the pool's value type needs no measurable space. The stopping and exhaustion laws
use the same negative-hypergeometric recursion.

`ToMathlib.MeasureTheory.Integral.Quadratic` specializes upstream Hölder to Cauchy–Schwarz,
retaining the total-mass factor for arbitrary measures and bounding it for subprobability
measures. Its quadratic bound requires only almost-everywhere measurable acceptance and
almost-everywhere acceptance/extraction bounds; the extraction functional need not be measurable.
`OracleComp.EvalDist.marginalized_jensen_forking_bound` applies it to any `EvalDistSemantics`,
without monad laws. Its `_map` corollary observes acceptance and extraction before integrating
and keeps the intermediate measurable-space choice internal.

`VCVio.EvalDist.ProbabilityBounds` supplies `prEvent_bind_sq_le_bind_pair` for conditional
independent draws, including lossy common draws and continuations. Its selector-partition bound
`sum_prEvent_option_map_eq_some_le_isSome` uses finite disjoint unions of measurable events,
without expanding singleton probabilities. The raw measure lemma needs only measurable selector
fibers and no measurable space on the selector's target. Finite and weighted sum-of-squares
inequalities derive from the same integral Cauchy–Schwarz theorem by integrating atomic measures.
`VCVio.OracleComp.Constructions.Fork.Basic` owns the typed occurrence constructions and
`prEvent_sq_le_observedForkPair`: arbitrary discrete answer measures suffice, with no uniformity
assumption or measurable-space arguments on the observed outputs.
`evalDist_map_answer_completeOccurrence` and
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
and injective restriction laws with explicit uniform-measure hypotheses. Its counting
proofs live in `ToMathlib.MeasureTheory.Measure.UniformTable`. The continuation may lose mass.
`evalDist_map_equiv_of_uniform` packages Mathlib's `uniformOn_univ_map_equiv` for a computation;
use it for a uniform permutation before introducing a bind continuation.
`evalDist_bind_bijective_of_uniform` reindexes any continuation after a uniform draw,
using the finite-uniform pushforward law. `evalDist_bind_congr` compares continuation
measures pointwise without a measurable-space instance on the intermediate result.
`VCVio.OracleComp.EvalDist.Measure` gives `evalDist_bind_congr_of_support` by structural
induction, without a probability/support bridge. These laws power the PRF tag/reader cache,
composed-handler, and shared-observation proofs. `SampleableType.evalDist_uniformSample` is
the one measure law for `$ᵗ α`, read off the class certificate for any measurable space with
measurable singletons. BR93's masking step takes the chosen measure's uniformity certificate
explicitly.

For `ProbComp Bool` security games, use `𝒟[game₀].boolDist 𝒟[game₁]` for a two-game gap and
`𝒟[game] {true}` for a success probability; prefer `Pr{...}[winningCondition]`
when the game ends by testing a predicate. The uniform measure instances for
`unifSpec` and `coinSpec` are global, so no local uniform certificate is needed.
`Measure.boolDist_self`, `Measure.boolDist_comm`, and `Measure.boolDist_triangle` supply the
elementary metric laws.
A measure denotation depends on the `MeasurableSpace` selected on its result type, so there is no
blanket measurable-space instance on finite types: `𝒟[…]` asks for one, while `Pr{…}[…]`
observes the computation through `Prop` and keeps the choice internal.

For the finite-range and fair-coin oracles, `OracleSpec.UniformAnswerMeasure.unifSpec`
and `OracleSpec.UniformAnswerMeasure.coinSpec` are the canonical interpretations.
Their instances apply only to these concrete oracle specifications; other oracle
specifications require an explicit measure interpretation. `ProbComp.evalDist_uniformFin`
simplifies a query to `uniformOn Set.univ`, and `ProbComp.prEvent_uniformFin` evaluates a
decidable event by counting its satisfying outcomes. These laws avoid a point-mass detour; the
`FinEnum.SampleableType` construction also has a uniformity proof in
`SampleableType.Measure` (`SampleableType.evalDist_finEnum`), using finite-range sampling and
equivalence transport. Its product sampler law uses `evalDist_pair` and the existing
`uniformOn_univ_prod` construction. These supply the `BitVec` key law and the measure-level
one-time-pad independence theorem. The executable sampler of a `SampleableType` is the
operational side, with full support a consequence of its uniformity law. Uniform table
resampling and injective restriction use the measure laws in
`VCVio.EvalDist.Monad.UniformTable`.
`ProbComp.evalDist_decide_eq_uniformBool_half` proves that an independent Boolean guess
matches a fair hidden bit with mass `1/2`; it uses the uniform measure and
Mathlib's `lintegral_fintype`, so all-random game hops need no point-probability sum.
`ProbComp.evalDist_bind_not_uniformBool` applies the uniform-reindexing law to any
continuation after complementing a fair bit.

The type classes separate a choice of response measures (`AnswerMeasure`) from the
uniformity law (`UniformAnswerMeasure`), which is a proposition about the chosen measures and
carries no finiteness data: `UniformAnswerMeasure.finite_range` and `nonempty_range` recover
both facts, and a cardinality statement takes `[Fintype (spec.Range t)]` for the query it
mentions (`UniformAnswerMeasure.toMeasure_singleton`). A blanket instance from
`[∀ t, Finite (spec.Range t)] [∀ t, Nonempty (spec.Range t)]` would silently choose a
distribution for an arbitrary oracle, so `UniformAnswerMeasure.ofFiniteNonempty` is an explicit
opt-in and only the concrete `unifSpec` and `coinSpec` instances are global. Structural
`OracleComp.support` needs neither measure class; a
positive-mass bridge needs assumptions on the chosen measures.

Oracle answer measures live on the discrete σ-algebra. `OracleSpec.AnswerMeasure spec` is
`PFunctor.AnswerMeasure` at `fun _ => ⊤`, so `AnswerMeasure.toMeasure t` is a measure on
`(spec.Range t, ⊤)`, and statements about oracle computations take no measurable-space
hypotheses on answer types. Continuous answer measures belong at the `PFunctor.FreeM` level,
where `PFunctor.AnswerMeasure` accepts arbitrary measurable structures. The query laws are generic
in the measurable structure that observes an answer:

- `evalDist_liftM_query` gives `(toMeasure t).trim le_top`, and `MeasureTheory.trim_eq_self`
  removes the trim when the observing instance is `⊤` by definition, as for `Bool` and `Fin n`;
- `evalDist_liftM_query_apply` (simp) evaluates a measurable event to `toMeasure t s`;
- `evalDist_liftM_query_uniform` gives `uniformOn Set.univ` for a uniform specification, and
  `evalDist_liftM_unifSpec_query` and `evalDist_liftM_coinSpec_query` are its simp forms for the
  built-in specifications.

When a concrete specification's answer type appears reduced (`Bool` rather than
`spec.Range t`), `rw` and `simp` match the generic laws only with the specification named, as in
`evalDist_liftM_query_apply (spec := S) t hs`: Lean assigns the measurable-space argument before
the query has determined `spec`. Handler-level hypotheses (`evalDist_simulateQ_congr`,
`evalDist_simulateQ_run_congr`, `QueryImpl.Stateful.MeasureDistEquiv.of_step`,
`wp_simulateQ_eq`, `wp_simulateQ_run'_eq`) are equalities in distribution `=ᵈ`, so handler states
need no measurable structure either. A tactic proof that needs the discrete structure on an answer
or on a reply-state product declares it with `let : MeasurableSpace (spec.Range t) := ⊤`, using
`let` because the goal is a proposition. A concrete specification with finite nonempty answers
takes `UniformAnswerMeasure.ofFiniteNonempty _` as a local instance on that specification. Sums
get their instances from `AnswerMeasure.add` and `UniformAnswerMeasure.add`, and a local instance
declared on the sum itself would compete with them.
For oracle-relative possibility, use `OracleComp.reachableWhen possibleOutputs oa`:
it follows only the query responses in `possibleOutputs`, with pure/query/bind laws
and a `gcongr` monotonicity rule. PolyFun defines the underlying
`FreeM.reachableUnder` from an angelic operation-indexed weakest-precondition
fold. `reachableWhen_univ_eq_support` identifies its all-responses case with
`MonadAttach.support`. This distinction matters for
stateful handlers: `MonadAttach` records possible returned values, while a
state-dependent notion must retain the starting state or operation policy.
`OracleComp.mem_support_iff_evalDist_singleton_pos_of_fullSupport` takes the precise
full-support condition on each answer measure, without adding a class for that one law.
`OracleComp.mem_support_iff_evalDist_singleton_pos` discharges it from
`UniformAnswerMeasure`; use this bridge when relating structural reachability to
singleton mass.
Structural support itself needs no probability interpretation. In particular,
`OracleComp.support_nonempty` needs only `[∀ t, Nonempty (spec.Range t)]`; counting-oracle support
and worst-case query bounds use that assumption alone.
Keep the class hierarchy for chosen answer measures, and state one-off properties such as
positive singleton mass as explicit hypotheses instead of adding a mixin for each bridge.

The Giry laws `evalDist_pure`, `evalDist_bind`, and `evalDist_map` hold under
`LawfulEvalDistSemantics`; bind needs a measurable continuation and map a measurable function,
which `evalDist_bind_of_discrete` and `evalDist_map_of_discrete` discharge on a discrete source.
`evalDist_bind`/`evalDist_map` are deliberately not `@[simp]`: a bind is expanded only on request
(`gotchas.md` §10).
Independent products denote product measures: `evalDist_mOfFn` and `evalDist_mPi`
(`VCVio/EvalDist/IndepProductMeasure.lean`) identify `𝒟[Fintype.mPi f]` with
`Measure.pi fun i => 𝒟[f i]` directly from `LawfulEvalDistSemantics` and Mathlib's
`measurePreserving_piFinSuccAbove`/`pi_map_piCongrLeft`. The index traversal itself lives in
`ToMathlib.Control.Monad.Fold`.
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

`VCVio.EvalDist.IndepProduct` exports event and reachability rules, also available through
`VCVio.Foundations`. Joint coordinate events factor by `prEvent_forall_coord_mOfFn` and
`prEvent_forall_coord_mPi`; tuple equality uses `prEvent_eq_mOfFn` and `prEvent_eq_mPi`.
These event rules require neither a measurable payload space nor attachment. The coordinate
`_eq_mul` rules retain the other factors' success masses, `_le` gives an unconditional bound,
and `prEvent_coord_mOfFn`/`prEvent_coord_mPi` need only the *other* factors to be lossless.
`mem_support_mOfFn` and `mem_support_mPi` eliminate reachable coordinates using core
`LawfulMonadAttach`; they require no exact attachment.

For finite uniform-output computations, `evalDist_mOfFn_uniformOn_pi` and
`evalDist_mPi_uniformOn_pi` combine those laws with Mathlib's `uniformOn_pi`, allowing each
factor its own uniform set. Their constant-full-space corollaries
(`evalDist_mOfFn_const_uniform`, `evalDist_mPi_const_uniform`) take the single-draw
uniformity certificate explicitly.
`OracleComp.evalDist_replicate_succ` uses Mathlib's `Measure.bind` and `Measure.map` for repeated
list-valued sampling, and `evalDist_replicate_apply_univ` gives its success mass as a power.
Because Mathlib does not install a generic measurable space on `List α`, these laws require the
chosen list measurable space and measurability of each `List.cons x` map explicitly.

Failure is missing mass. `𝒟[mx]` measures successful outputs only, so the failure probability of
`mx` is `prFail mx = 1 - Pr{let _ ← mx}[True]` (`prFail_def`; `prEvent_true_add_prFail` states that
the two add up to one, and `prFail_eq_one_sub_evalDist_univ` identifies it with
`1 - 𝒟[mx] Set.univ`), and `IsProbabilityMeasure 𝒟[mx]` states losslessness. `simp` evaluates
`prFail` on `pure` (`0`), maps, `if`, `failure` (`1`), `guard`, `OptionT.lift`, and oracle
computations (`OracleComp.prFail_eq_zero`); `prFail_bind_eq_add_lintegral_of_discrete` is the bind
law.
`evalDistWithFailure mx : Measure (Option α)` (`VCVio/EvalDist/WithFailure.lean`) is the
probability measure that puts the missing mass at `none`: `evalDistWithFailure_none_eq_prFail`
gives `prFail mx`, and `evalDistWithFailure_some` recovers the successful singleton masses.
`𝒟[failure] = 0` under `LawfulFailureEvalDistSemantics` (`evalDist_failure_eq_zero`). An
`OptionT` computation denotes `Measure.comap some` of its run (`OptionT.evalDist_eq_comap_some`),
equivalently its run's `dropNone` (`OptionT.evalDist_eq_dropNone`, in
`VCVio/EvalDist/Defs/Measure/OptionT.lean`), and a lift keeps the measure:
`OptionT.evalDist_liftM` (`@[simp]`) states `𝒟[(liftM mx : OptionT m α)] = 𝒟[mx]`.

## Core Definitions

| Definition | Type | Notation | Defined in |
|-----------|------|----------|------------|
| `evalDist mx` | `Measure α` | `𝒟[mx]` | `EvalDist/Defs/Measure/Core.lean` |
| `wp mx g ⊥` under `wpMonad m` | `ℝ≥0∞` | `𝔼{let x ← mx; …}[g x]`, `wp⟦mx⟧ g` | `EvalDist/Expectation.lean`, `EvalDist/ProbabilityNotation.lean` |
| event, `𝔼{…}[𝟙⟦p x⟧]` | `ℝ≥0∞` | `Pr{let x ← mx; …}[p x]`, `Pr{let x ← mx}[x = a]` | `EvalDist/ProbabilityNotation.lean` |
| `prFail mx` | `ℝ≥0∞` | `1 - Pr{let _ ← mx}[True]` | `EvalDist/ProbabilityNotation.lean` |
| `evalDistWithFailure mx` | `Measure (Option α)` | — | `EvalDist/WithFailure.lean` |
| `EvalDistEq mx my` | `Prop` | `mx =ᵈ my` | `EvalDist/EvalDistEq.lean` |
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
The lower-level `MeasureSemanticsVia` describes potentially lossy surface semantics.
Import `VCVio.EvalDist.Defs.Semantics.Core` for the bundles and
`VCVio.EvalDist.MeasureSemantics` for effect-preserving transformer observations. Bundled
`evalDist` observations infer `IsSubprobabilityMeasure` and `IsFiniteMeasure`.
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
a `ProbComp` realization `ProbResponder.IsExecutable.answerComp` for machine execution, whose
output measures are the kernel in σ-algebras that separate points; two realizations therefore
agree in distribution (`IsExecutable.answerComp_evalDistEq`), and so do the executions against
them. Stateful `ProbComp` handlers become responders through `ProbResponder.ofQueryImpl`, and the
handler of the result is the original one on the nose. Pullback along an interface lens preserves
executability when the pulled-back answer σ-algebras still separate points, as they do for an
injective answer translation (`pullback.measurableSingletonClass_range_of_forall_injective`).
This separate capability is important: abstract cryptographic caches need not be countable, while
a kernel-based responder need not have any executable realization. The executable layer lives in
`Type`, where the measure semantics of `ProbComp` does.

#### Adoption audit

| Area | Decision | Rationale / next integration point |
|------|----------|------------------------------------|
| Closed `evalDist`, advantages, couplings | Keep `Measure` | There is no semantic input to bundle. |
| `ReaderT` and `StateT` observations | Use `Kernel` now | Environment/state is exactly the kernel input; use the adapters above. |
| Stateful responders and wired rounds | Use `Kernel` now | `answerKernel`, `stepAgainstKernel`, and kernel powers model transitions compositionally. |
| Executable `QueryImpl`, `simulateQ`, machine runs | Keep monadic syntax | These are programs and evaluators; cross to kernels at observation boundaries. |
| KL/data-processing continuations | Use `Kernel` now | `KLDivergence.denoteKernel` is implemented through `evalDistKernelOfDiscrete`. |
| Query tracing, caches, costs, enforcement | Kernel views of observations, not handlers | Add kernel views of their `StateT` runs when a theorem composes distributions across states. |
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
only to normalize a computation belong inside the semantic API, as in the expectation laws and
the constant-continuation laws.

### Measure interfaces

| Definition | Purpose | Defined in |
|-----------|---------|------------|
| `etvDist mx my` / `tvDist mx my` | Event-keyed total variation, `⨆ p, absDiff Pr{let x ← mx}[p x] Pr{let y ← my}[p y]`, and its real form; the two computations may live in different monads, and no measurable structure is involved (`etvDist_eq_zero_iff` is `=ᵈ`) | `EvalDist/EvalDistTV.lean` |
| `etvDist_map_le`, `etvDist_bind_le`, `etvDist_bind_bind_le_wp`, `etvDist_bind_bind_le_of_bad` | Post-processing and common-prefix contraction, conditional composition with a pointwise majorant as the prefix's expectation `wp⟦mx⟧ bound`, exceptional prefix mass plus the good-branch allowance | `EvalDist/EvalDistTV.lean` |
| `etvDist_map_le_prEvent_of_agree`, `etvDist_map_le_map_add_prEvent_bad` | Identical-until-bad on events: agreement off a bad event bounds the distance by the bad mass | `EvalDist/EvalDistTV.lean` |
| `Measure.etvDist` / `Measure.tvDist` | Total variation on arbitrary subprobability measures | `ToMathlib/MeasureTheory/Measure/TotalVariation.lean` |
| `measureETVDist` / `measureTVDist` | Total variation of `𝒟[…]` on a chosen σ-algebra; `etvDist_eq_measureETVDist` identifies it with the event-keyed distance on a discrete output space, `measureETVDist_le_etvDist` bounds it on any other | `EvalDist/MeasureTVDist/Basic.lean`, `EvalDist/EvalDistTV.lean` |
| `Measure.etvDist_bind_le` / `Kernel.etvDist_comp_le` | Common-transition contraction on chosen measurable spaces | `ToMathlib/MeasureTheory/Measure/TotalVariation/Bind.lean`, `ToMathlib/Probability/Kernel/TotalVariation.lean` |
| `measureETVDist_bind_bind_le_lintegral` | Conditional composition with an AE majorant under the prefix law, for σ-algebra-parametric statements | `EvalDist/MeasureTVDist/Bind.lean` |
| `Measure.etvDist_bind_bind_le_of_bad` | Exceptional prefix mass plus the good-branch allowance weighted by its mass | `ToMathlib/MeasureTheory/Measure/TotalVariation/Bind.lean` |
| `Measure.Coupling` | Joint measure with prescribed marginals | `ToMathlib/MeasureTheory/Measure/Coupling.lean` |
| `ExpectationWP.RelWP` | Almost-everywhere relational postcondition under a measure coupling | `ProgramLogic/Relational/Measure.lean` |
| `ExpectationWP.eRelWP` | Best coupled `lintegral` post-expectation | `ProgramLogic/Relational/Measure.lean` |

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

The *Tags* column records the default-set membership each lemma has; an entry without a tag is
applied by name (`rw`, `exact`, or a `simp [...]` argument).

### Pure

| Lemma | Statement | Tags |
|-------|-----------|------|
| `evalDist_pure` | `𝒟[(pure x : m α)] = Measure.dirac x` | `simp` |
| `prEvent_pure` | `prEvent (pure a : m α) p = propInd (p a)` | `simp`, `grind =`, `expect_norm` |
| `propInd_eq_ite` | `propInd P = if P then 1 else 0` for decidable `P` | — |
| `support_pure` | `support (pure x) = {x}` | `grind =` |

### Bind

| Lemma | Statement | Tags |
|-------|-----------|------|
| `evalDist_bind` | `𝒟[mx >>= f] = 𝒟[mx].bind fun x => 𝒟[f x]`, for a measurable continuation | — |
| `evalDist_bind_of_discrete` | the same on a discrete source space | — |
| `prEvent_bind` | `prEvent (mx >>= f) p = wp⟦mx⟧ fun a => prEvent (f a) p` | `simp`, `grind norm`, `expect_norm` |
| `ExpectationWP.wp_bind` | `wp⟦mx >>= f⟧ g = wp⟦mx⟧ fun a => wp⟦f a⟧ g` (`simp` uses `ExactWPMonad.wp_bind`) | — |
| `prEvent_bind_eq_lintegral_of_discrete` | `Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx]` | — |
| `prEvent_bind_eq_sum_fintype` | `Pr{let y ← mx >>= f}[p y] = ∑ a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y]` | — |
| `prEvent_bind_eq_tsum_of_countable` | the same as a `tsum` over a countable source | — |
| `evalDist_bind_apply_univ` | `𝒟[mx >>= f] Set.univ = ∫⁻ x, 𝒟[f x] Set.univ ∂𝒟[mx]` | — |
| `support_bind` | `support (mx >>= my) = ⋃ x ∈ support mx, support (my x)` | `grind =` |
| `finSupport_bind` | `finSupport (mx >>= my) = (finSupport mx).biUnion (fun x => finSupport (my x))` | `simp`, `grind =` |

### Bind (constant continuation)

| Lemma | Statement | Tags |
|-------|-----------|------|
| `evalDist_bind_const` | `𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my]` | `simp` |
| `prEvent_bind_const` | `prEvent (mx >>= fun _ => my) = Pr{let _ ← mx}[True] * prEvent my` | `simp` |
| `OracleComp.evalDist_bind_const` | `𝒟[mx >>= fun _ => my] = 𝒟[my]` for a lossless oracle computation | `simp` |
| `OracleComp.prEvent_true_eq_one` | `Pr{let _ ← mx}[True] = 1` for an oracle computation | `simp`, `grind =` |

### Map

| Lemma | Statement | Tags |
|-------|-----------|------|
| `evalDist_map` | `𝒟[f <$> mx] = 𝒟[mx].map f`, for a measurable `f` | — |
| `evalDist_map_apply` | `𝒟[f <$> mx] s = 𝒟[mx] (f ⁻¹' s)`, for measurable `f` and `s` | — |
| `prEvent_map` | `Pr{let y ← f <$> mx}[q y] = Pr{let x ← mx}[q (f x)]` | `grind norm` |
| `evalDist_map_const` | `𝒟[(fun _ => c) <$> mx] = 𝒟[mx] Set.univ • Measure.dirac c` | `simp` |
| `support_map` | `support (f <$> mx) = f '' support mx` | `grind =` |
| `evalDist_map_equiv_of_uniform` | a permutation of a finite uniform draw keeps its measure | — |

### Bind swapping and congruence

| Lemma | Use |
|-------|-----|
| `OracleComp.evalDist_bind_bind_swap` / `OracleComp.wp_swap` | Swap two independent oracle draws (used by `prrw`; `_of_uniform` variants take uniform answers) |
| `evalDist_bind_congr` / `ExpectationWP.wp_congr` | Pointwise equal continuations give equal binds or expectations, with no measurable space on the intermediate result |
| `OracleComp.evalDist_bind_congr_of_support` / `wp_congr_of_support` | Continuations equal on the support of the shared prefix give equal binds or expectations |

### Zero / membership

| Lemma | Use |
|-------|-----|
| `prEvent_eq_zero_of_forall_mem_support` | An event false on every reachable output has probability zero |
| `evalDist.apply_eq_zero_of_disjoint_support` | A measurable event disjoint from the support has zero mass |
| `OracleComp.mem_support_iff_evalDist_singleton_pos` | `x ∈ support mx ↔ 0 < 𝒟[mx] {x}` under uniform answers |

## Decision Tree: Which Lemma Do I Reach For?

1. **Goal is `Pr{let y ← mx >>= my}[p y] = ...` or `𝒟[mx >>= my] s = ...`?**
   → `prEvent_bind_eq_lintegral_of_discrete` (or `evalDist_bind_of_discrete` followed by
     `Measure.bind_apply`) exposes the integral
   → On a `Fintype` draw, `prEvent_bind_eq_sum_fintype` gives the finite sum directly; on a
     countable draw, `prEvent_bind_eq_tsum_of_countable`

2. **Need to swap two binds?**
   → `prrw` rewrites one swap (`prrw under n` below shared binds) and closes the equality when
     the two sides then agree
   → `prrw normalize` searches for a sequence of swaps and shared-prefix steps that closes it

3. **Need an event or measure of `f <$> mx`?**
   → Events: `simp` or `grind` (`prEvent_map`)
   → Measures: `evalDist_map` / `evalDist_map_of_discrete`, and `evalDist_map_apply` on a set
   → A permutation of a uniform draw: `evalDist_map_equiv_of_uniform`

4. **Continuation doesn't depend on result?**
   → `evalDist_bind_const` / `wp_const` (by `simp`; the prefix contributes its success
     mass), and `OracleComp.evalDist_bind_const` for a lossless oracle prefix

5. **Continuations agree only on the support of a shared prefix?**
   → `OracleComp.evalDist_bind_congr_of_support` / `wp_congr_of_support` (or `prrw congr`)

6. **Relating probability to support?**
   → Under uniform answers: `OracleComp.mem_support_iff_evalDist_singleton_pos`,
     `OracleComp.prEvent_eq_zero_iff`, `OracleComp.prEvent_eq_one_iff`, `OracleComp.prEvent_pos_iff`
   → Without uniformity (one direction): `prEvent_eq_zero_of_forall_mem_support`,
     `OracleComp.prEvent_eq_one_of_forall_mem_support`, `evalDist.ae_of_forall_mem_support`

7. **Two computations have same distribution?**
   → State `oa =ᵈ ob` (`EvalDistEq`, possibly across monads); `relTriple_eqRel_of_evalDistEq`
     turns it into an `EqRel` coupling, and `EvalDistEq.of_evalDist_eq` proves it from equal
     output measures in a discrete structure.

## `grind` vs `simp` on Probability Goals

`grind` and `simp` have complementary strengths here, and reaching for the wrong one is the most
common way to get a `grind` that hangs.

**Use `simp` to compute a concrete probability or factor structure.** `simp` evaluates Dirac
masses of `pure`, uniform masses such as `𝒟[$ᵗ T] {x}` (and `Pr{let x ← $ᵗ T}[p x]` down to its
filtered cardinality `#{x | p x} / Fintype.card T`), constant continuations
(`evalDist_bind_const`), bounds (`𝒟[mx] s ≤ 1`, `Pr{…}[…] ≠ ⊤`), and the success mass of an
oracle computation. `grind` is not an `ℝ≥0∞`/`Fintype.card` arithmetic engine and has no rules
for Dirac singletons, measure bounds, or the success factor of a constant continuation, so it
will not finish these (it fails fast).

**Use `grind` for symbolic / structural goals.** Equiprobability (`𝒟[$ᵗ T] {x} = 𝒟[$ᵗ T] {y}`,
through the `grind norm` uniform laws `SampleableType.evalDist_uniformSample_singleton` and
`SampleableType.prEvent_uniformSample`), the pushforward of an event (`prEvent_map`),
independent conjunctions (`prEvent_bind_bind_and`), the lossless event `Pr{let _ ← mx}[True] = 1` of
an oracle computation (`OracleComp.prEvent_true_eq_one`), failure (`evalDist_failure_eq_zero`),
`x ∈ support (…)`, and `bind`/`pure`-shaped equalities of computations and their measures are
squarely in `grind`'s wheelhouse.

**Support characterizations are opt-in for `grind`.** Under uniform answer measures,
`OracleComp.prEvent_eq_zero_iff` (`Pr{let x ← mx}[p x] = 0 ↔ ∀ x ∈ support mx, ¬ p x`),
`OracleComp.prEvent_eq_one_iff` (`… = 1 ↔ ∀ x ∈ support mx, p x`), and
`OracleComp.prEvent_pos_iff` (`0 < … ↔ ∃ x ∈ support mx, p x`), all in
`VCVio/OracleComp/EvalDist/Measure.lean`, relate event probability to structural support. Their
right-hand sides introduce an *unbounded* quantifier over the support, which `grind` instantiates
and Skolemizes into fresh witnesses that the default `support_bind` rules re-expand, with no
finite grounding (`support ($ᵗ α) = Set.univ` is infinite). A default set containing them
saturates instead of failing fast, so none of them is a `grind` rule, and neither is
`OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support`. The point bridge
`OracleComp.mem_support_iff_evalDist_singleton_pos` (`x ∈ support mx ↔ 0 < 𝒟[mx] {x}`) is in
neither default set either. A proof that needs one supplies it:
`grind [OracleComp.prEvent_eq_zero_iff]`. This keeps naive `grind` on a probability goal failing
fast instead of hanging, while letting the proof that genuinely needs a bridge opt in.
`VCVioTest/GrindFailFast.lean` gates all of this: each characterization has a
`fail_if_success grind` + `grind [<lemma>]` example, so both a bad tag (bare `grind` starts
succeeding) and a new saturation (the timeout escapes `fail_if_success`) fail the build loudly.

**Monad/functor laws normalise structure for `grind`.** `bind_pure`, `bind_assoc`, `map_pure`,
and `Functor.map_map` are tagged `@[grind =]` (in `VCVio/EvalDist/Monad/Basic.lean`); `pure_bind`
is already in the default set from core (`attribute [grind <=] pure_bind` in
`Init.Control.Lawful`), so it is not re-tagged here. They are confluent rewrites, so `grind`
collapses a computation's structure (`mx >>= pure = mx`, `pure a >>= f = f a`, …) *before*
expanding events and measures, turning what would otherwise be a `grind` *explosion* on a
`bind`/`pure`-shaped equality into a quick solve: over an abstract lawful monad,
`𝒟[do let a ← mx; let b ← pure a; let c ← pure b; pure c] = 𝒟[mx]` and
`Pr{let _ ← g <$> (f <$> mx)}[True] = Pr{let _ ← mx}[True]` close by bare `grind`, and the ten-deep
redundant-`pure` tower of `VCVioTest/LongChainPrograms.lean` by `grind` given its definition.
`bind_pure_comp` / `map_eq_bind` are omitted (function argument under a binder, unindexable). A
*non-trivial* `<$>` / `if` / `<*>` does not normalise to a `pure`, so those structured equalities
go through the dedicated rules below or stay `simp`-terminal.

**Sequencing factors via `@[grind norm]`, not E-matching.** The second factor of
`(·, ·) <$> mx <*> my` sits under a binder (`Seq.seq`'s `Unit → _` thunk), which `grind`'s
pattern compiler cannot index: tagging such a lemma `@[grind =]` yields an "invalid pattern" error
(so do `pure_seq`/`seq_pure`). The escape is `grind`'s *normalization* phase:
`evalDist_seq_map_prod_mk`, `evalDist_seqLeft`, `evalDist_seqRight`, `prEvent_seqLeft`, and
`prEvent_seqRight` (`VCVio/EvalDist/Monad/Seq/Measure.lean`) are `@[simp high, grind norm]`, so
bare `grind` identifies `𝒟[Prod.mk <$> mx <*> my]` with `𝒟[mx].prod 𝒟[my]` and scales a
discarded computation's event by its success mass. A singleton of the `bind`-spelled product
(`do let x ← mx; let y ← my; pure (x, y)`) goes through `evalDist_pair` and `Measure.prod_prod` by
name; independent conjunctions of that shape factor automatically through
`prEvent_bind_bind_and`.

**`grind norm` can starve E-matching — use it sparingly.** Norm rules rewrite goal/hypothesis
terms *before* E-matching, so a norm rule whose result does not match the `@[grind =]` patterns
disconnects them. Concretely: `@[grind norm] bind_pure_comp` (`mx >>= fun a => pure (f a)` →
`f <$> mx`) would close a couple of target gaps but breaks the `replicate` gates: the goal's
do-block normalises to a `<$>` form while the E-matching-side `replicate` unfolds stay in `bind`
form, and the E-graph never connects the two. It is therefore deliberately **not** tagged. Gate any
new `@[grind norm]` candidate against all of `VCVioTest/{ProbabilityTactics,MonadProbability,`
`LongChainPrograms,GrindFailFast}.lean` and `VCVioTest/EvalDist/MeasureBridge.lean` before
keeping it.

**Structural additions to the default set** (all gated in `VCVioTest/GrindFailFast.lean`):
`OracleComp.replicate` unfolds (`replicate_zero`, `replicate_succ_bind`, `replicate_pure`,
`replicateTR_zero`, `replicateTR_eq_replicate`; the proof-level loop combinator, while core
already grind-tags the `List.mapM` / `foldlM` / `forIn` layer), `Functor.map_map`, and the
`simulateQ` routing layer (`QueryImpl.add_apply_inl/inr`, `simulateQ_add_liftComp_left/right`,
the `withBadFlag`/`withBadUpdate`/`flattenStateT` run-shapes, `simulateQ_option_elim(M)`). The
`simulateQ_add_liftComp` pair also prevents a saturation: without it, bare `grind` times out on a
routed `simulateQ (impl₁ + impl₂)` goal over a lifted computation.

`VCVioTest/ProbabilityTactics.lean` is the living benchmark and **gate** for all of this: outcome
masses `𝒟[mx] {x}`, events `Pr{…}[…]`, success masses, and output measures over `ProbComp` (and
`OptionT ProbComp` for selection and abort), organised by category, each closed by a single
*terminal* tactic. Where a fact closes by **both** `simp` and `grind`, both are kept (the mirror),
so each tactic stays exercised on that shape; where only one closes, the entry is a *gap pair*
(`fail_if_success (tac; done)` then the working closer, with a dated `gap(tac, …)` reason), so the
gap is machine-checked and expires the moment the set improves. A regression in either tactic
surfaces there in isolation. Its recorded gaps: `grind` has no Dirac, bound, or
`𝒟[mx] Set.univ` success-mass rules and does no counting arithmetic; a product singleton is not
split into a rectangle; `simp` rewrites `(Set.univ : Set Bool)` to `{false, true}` ahead of the
lossless-mass rule; finite counting leaves `#{x | p x} / n` unevaluated; and the support/mass
bridges are applied by name.
When adding probability automation, add the corresponding battery rows and retire the guards it
makes obsolete in the same change. The rules are in *Normal forms and the tactic contract* below.

`VCVioTest/MonadProbability.lean` is the **generic-`m`** companion: the same gate over an abstract
monad `m` with `[EvalDistSemantics m] [LawfulEvalDistSemantics m]` and over the concrete carriers
`Id`, `OptionT ProbComp`, and `ExceptT Bool ProbComp`, where the lemmas are actually stated. It
surfaces what `ProbComp` masks, chiefly the **success factor**: over a monad that can fail, a
discarded computation scales the continuation by its success mass,
`𝒟[mx >>= fun _ => my] = 𝒟[mx] Set.univ • 𝒟[my]` and
`Pr{let y ← mx *> my}[p y] = 𝒟[mx] Set.univ * Pr{let y ← my}[p y]`. Both collapse to the `ProbComp`
forms only because oracle computations are lossless (`OracleComp.evalDist_bind_const`).

`VCVioTest/LongChainPrograms.lean` stresses the same sets on programs with ten or more binds:
the total mass of a twelve-step chain (`simp` and `grind`), the mass of the same chain over
`OptionT ProbComp` (`simp`), monad-law collapse of a ten-deep redundant-`pure` tower (`simp` and
`grind`), and a reachable support point (`simp`). Its `target(...)` notes record what neither
tactic closes yet: the mass of a guarded `OptionT` chain, the full support
`support chain12 = Set.univ`, and the concrete outcome value `Pr{let x ← chain12}[x = true] = (2 ^ 12)⁻¹`.

**Opting out downstream.** VCVio deliberately extends the *default* `grind` set (the monad laws
above plus the event, measure and support rules), and these tags are inherited by every project
that imports it. All of the standard escape hatches work if a downstream `grind` call misbehaves:
disable a rule per call (`grind [-bind_pure]`), ignore the default set entirely
(`grind only [the, lemmas, you, want]`), or unset a tag for a whole file
(`attribute [-grind] bind_pure`). `grind?` reports a minimal `grind only [...]` call for a goal it
closes, which is the easiest way to make a fragile call site independent of the default set.

## Normal forms and the tactic contract

### Registered interfaces

Use the tactic that matches the mathematical obligation:

| Obligation | Interface |
|---|---|
| Ordered expectations or postconditions | `gcongr with x hx` on `wp⟦mx⟧ f ≤ wp⟦mx⟧ g` exposes support membership. |
| An expectation of a mapped computation | `simp` precomposes the payoff using `lintegral_evalDist_map_of_discrete`, retaining the integral. |
| Directed replacement inside a probability bound | Import `Mathlib.Tactic.GRewrite`; use `grw [h]` for inequalities and `apply_rw [h]` for event implications. A support-restricted rewrite theorem can leave membership as a side goal. |
| Measure bind ordered in its continuation | `Measure.bind_mono_right_of_forall` supports `gcongr` and `grw`, with explicit `AEMeasurable` side conditions. Use `Measure.bind_mono_right` directly for an almost-everywhere bound. |
| A finite event probability or mass | `finiteness` closes `Pr{…}[…] ≠ ⊤` through `prEvent_ne_top` (tagged for its rule set) and `𝒟[mx] s ≠ ⊤` through Mathlib's finite-measure rule, inside sums and arithmetic. |
| A finite expectation on a finite result type | `finiteness` uses `wp_ne_top_of_finite` and asks for finite functional values. |
| A supplied finite bound on an arbitrary result type | Apply `ne_top_of_le_ne_top hc (wp_le_const_of_support oa h)`; the bound remains explicit. |
| Nonnegative total variation arithmetic | Import `VCVio.EvalDist.MeasureTVDist.Positivity` and use `positivity` on `tvDist` and `measureTVDist`; this also arrives through `VCVio.ProgramLogic.Tactics`. |
| Measurability through optional or exception-valued maps | `fun_prop` uses `Option.measurable_map`, `Except.measurable_map`, and `Option.measurable_elim'` on arbitrary measurable spaces. |

For a local abbreviation hiding a probability, use a targeted `change` or `dsimp only` before
`finiteness`. For named definitions, `finiteness (add unfold [name])` is also available.
`finiteness [proof]` supplies an explicit finiteness fact. The tactic does not infer finiteness
of an expectation over an infinite result type merely from pointwise finiteness of its functional.

The registrations and their failure boundaries are exercised in `VCVioTest/Tactic/` (including
`VCVioTest/Tactic/Finiteness.lean`) and `VCVioTest/ProgramLogic/GCongr.lean`. The
expression-specific `fun_prop` rules avoid globally registering eliminator theorems whose
conclusion is the unrestricted `Measurable f`.

For a sum of oracle `wp` bounds, rewrite with `← OracleComp.ProgramLogic.wp_finsetSum`,
then apply `wp_le_const_of_support`. Use `wp_le_const_add_of_support` for a constant allowance
plus another postcondition. Both the oracle facade and core's raw `Std.WP.wp` expose
support membership to `gcongr`; callers need no preparatory `change`.

See the [generalized-relation investigation](../reading/generalized-relation-automation.md) for
tested rewrite directions, theorem-shape requirements, and the distinction between `gcongr`
and `grw` registrations. Measure-bind rewriting requires importing
`ToMathlib.MeasureTheory.Measure.Monotone`; pointwise order does not discharge measurability.

### Normalization discipline

The simp, grind and `gcongr` sets of the probability layer are designed around one normal form
and one *ladder* below it. The normal form is the measure form: singleton, event and total masses
stay `𝒟[mx] s` or `Pr{…}[…]`, and `simp` leaves it only to reach a closed form.
`VCVioTest/EvalDist/MeasureBridge.lean` pins this contract. The ladder has one canonical spelling
per rung, mass-left throughout, each rung reached from the one above it by an existing pathway
rather than by a per-rung duplicate lemma.

| rung | form | reached by |
|---|---|---|
| 0 closed | numerals, `(Fintype.card α)⁻¹`, `if … then 1 else 0`, `#{x \| p x} / Fintype.card α` | `simp` (`evalDist_pure`, `prEvent_pure`, `SampleableType.evalDist_uniformSample_singleton`, `SampleableType.prEvent_uniformSample`, `ProbComp.evalDist_uniformFin`, `evalDist_bind_const`, `OracleComp.prEvent_true_eq_one`) |
| 1 finite sum | `∑ x, Pr{let y ← mx}[y = x] * g x`, or `∑ x, 𝒟[mx] {x} * g x` | `rw [prEvent_bind_eq_sum_fintype]`; from rung 3, Mathlib's `lintegral_fintype`, then `simp [mul_comm]` |
| 2 countable sum | `∑' x, Pr{let y ← mx}[y = x] * g x` | `rw [prEvent_bind_eq_tsum_of_countable]`; from rung 3, Mathlib's `lintegral_countable'`; `simp` collapses it to rung 1 on a `Fintype` through `tsum_fintype` |
| 3 integral | `∫⁻ x, g x ∂𝒟[mx]` | `rw [prEvent_bind_eq_lintegral_of_discrete]`, or `evalDist_bind_of_discrete` with `Measure.bind_apply`; an intermediate for Mathlib's integration API, not a target |

Mass-left is canonical: it is the orientation of `prEvent_bind_eq_sum_fintype`,
`prEvent_bind_eq_tsum_of_countable`, Mathlib's Bochner `integral_fintype`, and the library's
own bind lemmas. Mathlib's `lintegral_countable'`/`lintegral_fintype` are mass-right; they appear
inside proofs, never as a normal form.

**What each tactic promises.**

- `simp` is the *structural* normalizer: it reaches a closed form when one exists, applies the
  monad laws, keeps `𝒟[mx] s` and `Pr{…}[…]` otherwise, and collapses `∑'` to `∑` on a
  `Fintype`. It never expands a bind or map into a Giry bind, pushforward or integral:
  `evalDist_bind`, `evalDist_bind_of_discrete` and `evalDist_map` are not `@[simp]`
  (`gotchas.md` §10), and `rw [prEvent_bind_eq_sum_fintype]` is the documented one step to a
  finite sum.
- `grind` is the *symbolic* closer: equiprobability, event pushforward, independent
  conjunctions, membership, losslessness of oracle computations, failure, and
  `bind`/`pure`-normalised structure. It is not an `ℝ≥0∞`/`Fintype.card` arithmetic engine and
  must keep failing fast on the support characterizations (`VCVioTest/GrindFailFast.lean`).
- `gcongr` and `finiteness` are the *bound* closers. On expectations they act on
  `wp⟦·⟧` (`wp_mono_of_support`, `wp_ne_top_of_finite`); `finiteness`
  also closes `Pr{…}[…] ≠ ⊤` and `𝒟[mx] s ≠ ⊤` inside arithmetic, and `grw [prEvent_mono …]`
  rewrites an event under a bound.
- The measure laws are `evalDist_pure` under `LawfulPureEvalDistSemantics` and `evalDist_bind`
  under `LawfulEvalDistSemantics`; bind also requires a measurable continuation, which
  `evalDist_bind_of_discrete` discharges on a discrete source. `prEvent_eq_evalDist_map`,
  `prEvent_eq_evalDist` and `prEvent_eq_evalDist_singleton` connect an event to the measure of
  its set when an argument needs the set form.

**What the gates enforce.** The gate files (`VCVioTest/ProbabilityTactics.lean`,
`MonadProbability.lean`, `LongChainPrograms.lean`, `GrindFailFast.lean`,
`EvalDist/MeasureBridge.lean`, `Tactic/*.lean`, `ProgramLogic/GCongr.lean`) state
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
   already tests closure.) A fact that no single call closes yet is recorded as a `target(…)`
   note rather than carried as a multi-step proof.
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

1. **Missing probability spec classes**: on `OracleComp spec`, `𝒟[...]` and `Pr{...}[...]` require `[OracleSpec.AnswerMeasure spec]`, and uniform-answer lemmas `[OracleSpec.UniformAnswerMeasure spec]`, not just finite, nonempty answer types. Answer measures live on the discrete σ-algebra, so answer types take no `MeasurableSpace` hypotheses. Use `UniformAnswerMeasure.ofFiniteNonempty spec` as a local instance when a concrete finite spec should answer uniformly. `𝒟[...]` additionally needs an ambient `MeasurableSpace` on the output; `Pr{...}[...]` does not.

2. **Carrying duplicate probability instances**: do not add a separate `[OracleSpec.AnswerMeasure spec]` when `[OracleSpec.UniformAnswerMeasure spec]` is already in scope. `UniformAnswerMeasure` extends `AnswerMeasure`; a second instance can make instance search ambiguous and need not describe the same answer measures.

3. **Using `support` when `finSupport` is needed**: `finSupport mx` requires `[HasEvalFinset m]` and `[DecidableEq α]`, and `finSupport_bind` also `[DecidableEq β]`.

4. **Forgetting the support bounds**: `prEvent_eq_zero_of_forall_mem_support` and `evalDist.apply_eq_zero_of_disjoint_support` restrict an event or mass to reachable outputs with no uniformity assumption.

5. **`𝒟` on bare `query t`**: works directly when the expected type pins `query t` to a monadic form, since `query` resolves to `HasQuery.query`. Write `𝒟[(query t : OracleComp spec _)]` (or hand the result to a context that provides the same ascription). If you need the primitive `OracleQuery spec _` (e.g. for `OracleQuery.cont`), use `spec.query t` instead.

`evalDist.ae_of_forall_mem_support` converts a pathwise predicate into an almost-everywhere
predicate under its `MeasurableSet` premise. It uses core `MonadAttach` and the measure laws, and
works for arbitrary chosen result spaces and failing computations.
`evalDist.apply_eq_zero_of_disjoint_support` gives the corresponding zero-mass event rule.
