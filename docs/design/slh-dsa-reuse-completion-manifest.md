# Finite SLH-DSA reuse completion manifest

Documentation candidate bound to accepted commit
`ae23574db895fd68ae28db806b54e0b3b275a551`. The clean committed full validation and independent P6 acceptance passed.
This manifest freezes the finite completion deliverables; it does not freeze the
complete per-unit Lean contracts or authorize bodies or migration. Full P5, R5
delegation and R6c/R8 completion remain open.

This finite endpoint supplements the [reuse plan](slh-dsa-reuse-refactor-plan.md),
[original strength inventory](slh-dsa-reuse-evidence/strength-manifest.json),
[R0 semantic archive](slh-dsa-reuse-evidence/r0/README.md), and
[R0b readable/runtime bindings](slh-dsa-reuse-evidence/r0b/README.md).
The [source map](slh-dsa-reuse-evidence/r6c/source-map.json) retains its original
historical provenance; every selected source anchor also matches this accepted
commit. [Evidence and reproduction](slh-dsa-reuse-evidence/r6c/README.md),
[target-shape requirements](slh-dsa-reuse-evidence/r6c/target-shapes.md), and the
[P6 checkpoint](slh-dsa-reuse-evidence/r6c/p6-checkpoint.json) distinguish this
finite deliverable list from the fully quantified contracts still required
before each body unit.

## Endpoint and exclusions

The endpoint is one canonical provider-based construction and counted experiment,
with two complementary probability arguments. It is not one universal security
proof, nor a facade over permanently duplicated signing bodies. Five finite R6c
families below must be consumed by the real proof/construction routes. R5 then
removes duplicate implementation ownership in the named dependency units below.
A completed family is not reopened by discovering another possible extraction;
additional families become separate follow-up work. Purely specialized helpers
may remain local. No LOC or build-speed target is claimed.

Every recovery uses the exact frozen original type and semantic equations, not
only a theorem with the same pretty-printed name. No q+1/max(1,q) replacement,
extra lifetime/width/freshness premise, or numerical slack is permitted. Generic
hypotheses such as FreshFor are discharged by an honest component application;
they are not added to the final adversary/security theorem.

## Five required extraction / actual-use families

All new names in this section are PROPOSED acceptance names, not declarations
claimed to exist. Old fully qualified names and sources are in the linked source map.
Each family needs ordinary-import type/axiom witnesses and actual production use.
A test-only reproving wrapper is useful evidence but does not finish delegation.

All **52** named source declarations are absent from the original RAW1242 table;
the source-map first-line headers are location anchors, not full contracts.
Before each body unit, freeze and independently review its complete quantified
Lean headers, exact old literal types, relevant semantic values/equations,
declaration shape and axiom sets, dependencies/owner closure, and explicit
carrier, sampler, policy and observation maps. Add coverage for these previously
uncaptured declarations. Complete the existing-owner search before choosing a
new owner. No body unit starts from this prose or an unchecked record alone.

### C1. Adaptive sampler: finish actual ownership and consumers

Existing generic owner: `OracleComp.RandomOracleTraversal` in
`VCVio/OracleComp/QueryTracking/RandomOracle/Traversal.lean`. Keep its existing
five definitions evaluate/sample/program/Separated/FreshFor and five laws.
Do not add another traversal. Accepted A Frame remains its effectful frame API.

Required old recoveries, namespace `SLHDSA.SHAKE128s.GraphFreshSampling`:
`evaluate_eq_sample`, `program_congr`, `program_update_outside`,
`evalDist_sample_eq_uniform_program`, `evalDist_evaluate_eq_uniform_program`.
Also recover the five definitions' exact old specialization equations.
Proposed ledger group: `R6c.Sampler` (5 definition equations +5 literal types).
Delegate the old proof uses to the generic owner after classifying any required
guard migration below (proof-only reuse need not change RAW records); preserve
old public types and exact state/cache observations.

Actual consumers: the existing 128s `CanonicalGraph.Programming.warmup_uniform`
route and the canonical 192f FORS graph traversal. For 192f use actual GraphInput,
Widths, schedule and update/prefix laws, with Separated/FreshFor and Nodup at the
precise traversal boundary. State all freshness hypotheses on the local lemma;
prove an empty-cache/local namespace instance. Do not claim an arbitrary warm
signing execution has fresh independent answers: repeats retain their queries
and charges and need not satisfy FreshFor. The full effectful P6 128s/192f clients
remain separate from these conditional random-oracle sampling clients.

Proposed consumer theorems `SLHDSA.Security.ForsGraphSampling.shake128s` and
`.shake192f` must both consume the SAME generic sampler law, actual canonical
GraphInput/schedule, and retain complete traversal state plus outer oracle cache.
Their exact hypotheses must be frozen before authoring, not invented as fields.
Uniform-prefix laws require their own sampling hypotheses: zero-padding for m<n
does not yield uniform n-byte output. The universal effectful programme equality
keeps all validated parameters without Width, PrefixFits or FreshFor premises.

### C2. Independent moments: use the generic proof in the real FORS tail route

Existing generic owner:
`ToMathlib.Probability.Moments.IndependentPowers`, namespace ProbabilityTheory.
Preserve the two arbitrary-order independent binomial power laws, the centered
sum polynomial through six, its zero/succ equations, and finite-sum law.
No new Poisson API is required to complete this family.

Required old recoveries in `SLHDSA.SHAKE128s.ForsConcentration`:
`independent_integrable_add_power`, `independent_integral_add_power`,
`sumMoment` (all orders, including fallback >6), `sumMoment_zero`,
`sumMoment_succ`, `independent_sum_moments`, and
`poisson_centered_sum_moments`. Proposed ledger group `R6c.Moments`.
The original production `poisson_centered_sum_moments` must consume the generic
finite-sum law, and `poisson_sixth_sum_bound` / `poisson_load_tail_sharper`
must still consume that production theorem. The accepted separate test theorem
`Refactor.IndependentPowersRecovery.poisson_centered_sum_moments` is not enough.
Retain its actual measure, all integrability and moment assumptions and constants.

Reuse criterion is intrinsic mathematics: no SLH imports/constants in generic
owner; Mathlib ownership/search check; exact old specializations; existing public
`iIndepFun.integral_pow_six_finsetSum_of_signs` consumer with polynomial
15*n^3-30*n^2+16*n, including n=0,1. No artificial second cryptoscheme is needed.

### C3. Presampling: extract only the two local value-law mechanisms

Intended owner: existing RandomOracle/DeferredSampling layer, or a small leaf
below it after checking current Commute/Programming laws. Reuse randomOracle,
QueryCache, simulateQ and existing traversal; no new ROM or world interpreter.
Finite targets: one fresh-entry prepend value-distribution law and its adaptive
traversal prepend law, generic in input/output and ambient private sampling.
Recover exact old `Presample.evalDist_prepend_fresh_world` and
`Presample.evalDist_prepend_worldEvaluate`; recover `worldEvaluate` as the exact
lift of existing Traversal.evaluate. Proposed ledger group `R6c.Presample`.
`cacheQuery_comm` should reuse an existing update lemma, not grow another API.

Actual consumers: original `evalDist_prepend_warmup` (keygen graph warmup) and
`evalDist_prepend_warmup_after` (post-private-seed continuation), through the
original `evalDist_counted_warmed` route. Preserve their precise advertised
projection: they compare downstream value laws, NOT final-cache equality.
Warmup remains deliberately outside the selected counter in that transformation;
never present it as a cost/cache-preserving actual execution or ignore repeated
query multiplicity. Full joint keygen/observer P5 contracts remain separate.

### C4. Programming by dependency agreement

Intended generic owner: `RandomOracle/Traversal/Programming` under the existing
traversal, with no HashSig imports. Finite mechanism: agreement outside remaining
writes, preservation after one assignment, input agreement when all read children
agree, and deterministic program = final cells + cache written in SAME list order.
Do not add rank sorting, Fintype enumeration or a second evaluator to the owner.
Freeze explicit topological read-before-write assumptions before authoring.

Recover old `CanonicalGraph.Programming.AgreesOutside.assign`, `input_eq_target`,
and `program_eq_cacheFrom`; the old Pairwise RankLE hypothesis discharges the
new local read-before-write condition via accepted Graph.Children rank laws.
Retain original cacheFrom order and full cells/cache equality.
Proposed ledger group `R6c.Programming` (three types plus exact local-definition
specialization equations required by those types).

Actual consumers: old full-graph 128s `warmup_uniform` and 192f canonical FORS
subtree/forest programming using accepted B dependencies and C/D output stability.
192f need not recreate a rank-sorted WHOLE-SLH graph or infer a 191-bit theorem.
The same generic programming lemma must handle both; partial traversal leaves
unwritten cells at their initial values and the target-agreement premise must
explicitly cover those cells. No tautological final-state definition substitutes
for proved child-read availability or output persistence.

### C5. Exact counting and answer-representation transport (two finite slices)

#### C5a. Exact counts, unchanged verifier arithmetic

Intended owner: `VCVio/OracleComp/QueryTracking/QueryBound/Exact` (final path after
existing-owner check), reusing existing QueryCostExactly for instrumentation.
Finite declarations: ExactQueryCount, pure/query constructors, bind, map;
generic finite sequencing and list fold count; transport to existing exact cost.
Recover old `Generic.ExactQueryCount`, `.bind`, `.map` and old
`VerificationQueries.exact_bind`, `exact_map`, `sequenceFin_exact`,
`foldlM_exact`, `exact_cost`. Proposed ledger group `R6c.ExactCount`.
Keep concrete `Bounds` and verifier branch/chain arithmetic local unless the
existing QueryBound API already supplies a lemma; do not introduce a cost model.

Actual consumers: original concrete `fors_exact` and `wots_exact` verifier routes,
and their canonical provider counterparts through R5 observation equalities.
Recovery must reach unchanged `VerificationBudget.verification_count_bounds`,
`verification_accepted_count_bounds`, `accepted_outcome_work` and q<569 zero.
Calls include cache hits; exact count is not number of distinct cache entries.

#### C5b. Answer representation transport, not another game/ROM

Intended generic owner: `VCVio/OracleComp/SimSemantics/QueryImpl/Relabel` or an
existing equivalent after owner search. Use dependent QueryImpl + existing
writer/state fold composition. Finite original Bridge.Transfer targets:
`simulateQ_relabel_unlabel`, `simulateQ_unlabel_relabel`, `mapCache_empty`,
`mapCache_cacheQuery`, `run_simulateQ_relabel_from`,
`simulateQ_writerT_run_compose`, `simulateQ_writerT_stateT_run_compose`.
Retain their exact original specializations in Bridge.Transfer.
Proposed ledger group `R6c.Relabel` (seven literal targets).

Actual consumers: existing FIPS byte/full-answer bridge using answerEquiv and
canonical shared-experiment observation with the corresponding oracle-answer
representation. Required pullback includes cache update, reply/log observation
and caller's ordered cost policy. The sampler-preserving answer law is separate
and explicit; arbitrary truncation/padding is not an equivalence. Original
`runBySource_evalDistEq` and `hasSecurityBits_of_bridge` remain specialized game
corollaries consuming the generic fold laws; they are not moved as a second
security semantics. Generic no-HashSig import audit is mandatory.

## Specialized quantitative arguments deliberately retained

- #766 CoverageBound/JointBound/ByteBound/WeakKeyBound/HedgedKeyBound and their
  general witness, byte-clash, seed coupling, per-seed/averaged/randomizer bounds.
  They cover different resource predicates/modes; they are not duplicate 127 math.
- #912 ForsMoments concrete polynomial certificates, Poisson rate3 / power14 /
  centered-six constants, occupancy/de-Poissonization thresholds, disclosure and
  share ledger/charging/provenance, WorkTarget/WorkFinal final accounting.
  These are the specialized tight quantitative proof, not generic graph execution.
  C2 factors independent-sum algebra; it does not replace those coefficients.
- Exact 127 at ORIGINAL q>=1, probability-one ACTUAL combined work and original
  lifetime eligibility; q<569 zero (which has no lifetime premise); supported
  verification 569..3824 with their original framing/acceptance distinctions;
  universal3929 cap; no cap confused with exact every-path count.
- All six #766 deterministic/hedged families, full weak-seed term, n=32 sharper
  minimum, per-seed and arbitrary seedDist/epsilon-randomizer families, wire/EUF
  corollaries. No lifetime restriction is added to general #766 claims.
- Exact18-row CSV bytes/evaluator/certificates and range inequalities. These are
  regression artifacts, not substitutes for all-q kernel recovery.

## R5 finite dependency units (after P4/P5/P6 and named guard migration)

1. WOTS primitives/chain/keygen/sign/recover: canonical Wots/GeneralWots provider
   programs; recover old Bridge.Wots complete sign/public-key/recovery equations.
2. FORS recursive tree/auth/sign/recover: canonical Fors provider; use accepted
   naturality/P4 and C/D full program observation. Keep secret-first order and
   exact parser/defaultbits; preserve PRF→F, left→right→parent and output stability.
3. XMSS/Merkle: after1, canonical Xmss effectful tree/auth/climb; recover original
   Bridge.Xmss merkleNode/Sign/Climb/PublicKeyFromSignature/Root equations.
4. Hypertree: after1–3, canonical GeneralHypertree layers/root; recover original
   Bridge.Hypertree signLayers/sign/root/verify/keygenRoot equations.
5. Scheme/codec/view: after1–4, canonical GeneralScheme + existing codec and
   fromInternalPure family; retain randomizer/mode, context validity, optional
   rejection and exact zero-work losing branches. Recover old Scheme.* external
   keygen/sign/verify and Bridge.Scheme internal/relabel equations.
6. Game/observation entrypoints: after5 and complete P5, canonical counted
   experiment + Reply/readback view; retain old public game/security theorem
   statements as compatibility exports, not independent executable game bodies.
   Chosen actual sampler joint keypair/cache/original-cost continuation law is
   required; private draw reorder does not imply arbitrary private trace equality.

Each unit removes duplicate executable definition ownership only AFTER exact
operational equations and public recovery; the complementary probability proof
routes remain. Preserve all old names/types/stronger auxiliary results until
ledger recovery and an ordinary consumer replacement is independently reviewed.
Use finite per-unit inventories before editing; no whole-file rewrite authority.

## RAW1242 and operational-source guard migration is a separate obligation

Current R0a stores1242 semantic records rooted at112 original semantic constants,
77 literal theorem contracts and11 groups. Its comparison includes declaration
body AST, dependency closure, owner/calling metadata and axioms, not only types.
Even an extensionally equal delegating definition can change its body/dependencies
and must FAIL honestly. Capture.lean excludes theorem proof VALUES: changing only
a theorem proof with the same statement/axiom set does not itself add its proof
dependencies. Computational or Prop-valued defnInfo, opaqueInfo and recInfo RHS
values, and declaration TYPES, are captured. Classify each port before editing.
The 52 selected declarations are not themselves RAW1242 entries, so this archive
is not evidence that their bodies are currently covered. Each unit must add its
reviewed literal/equation/shape/axiom/closure recovery before changing a body.
R0b additionally binds readable semantic source files, runtime sources, CSV,
protected executable registration and driver scaffold. U compatibility work
remains a separate reviewed unit; bind any production
manifest to its accepted parent and separately review operational binding deltas.

Do not delete RAW records, suppress the check, permit whole-module differences,
mark new owners external, or regenerate expected output to make delegation green.
Before each affected migration, freeze the named original raw body/type/dependency
record and equation; add a versioned, separately reviewed semantic migration
entry stating old→new representation, actual canonical RHS and observation map.
Prove exact quantified operational/equal-law compatibility, replay immutable old
literal contracts, and mutation-test that a changed canonical branch/cost/parser
is still rejected. Retain the original1242 archive as historical oracle. A new
current-definition capture may be added only with a reviewed explicit mapping
and complete dependency coverage; no blanket bypass or automatic accept-list.
This is guard evolution with theorem evidence, not a silent baseline refresh.

## Finite F6 universe recovery gate under U

R8 also requires a reviewed, finite compatibility inventory for F6's frozen
`Expr.const` universe vectors under the independent index/runtime universes U.
Keep all **42** original closed goals and their original level-name lists exact,
including the immutable a2d2 goal archive, 7b25 exact-schema producer archive and
8ab4 row-proof archive. Ordinary source recompilation does not update a frozen
metaprogram constant vector.

Before implementation, freeze each affected named constant occurrence/structural
AST path, original and new arity, explicit inserted index level, retained level
roles, and specialization/inverse-recovery map. Prove exact specialization back
to each frozen original goal; reject unknown/moved/duplicated sites or mismatched
levels. Preserve complete goal ASTs, declaration types/shapes/axioms and import
closure. No alpha/level quotient, reduction-based matching, goal recapture or
replacement expected schema may discharge this gate. The finite four-declaration /
seven-reference R0 U adapter is not a blanket permission to rewrite F6 vectors.

Retain the original generic row 36. Add a **separate full counted generic row**
quantified independently over oracle index universe i and runtime-carrier
universe r, retaining the original EUF-to-SUF inequality and all algorithm,
request/reply, observer, runtime and policy quantifiers. It must not specialize
i=r, force either to zero, or widen payload universes as a substitute. Freeze its
complete Lean header and exact old specialization/inverse witnesses before its
proof. Recover the original 39 counted concrete rows and two DIRECT rows 37/38
without changing their bounds/seed assumptions; the old generic row remains the
42nd archived row, not silently replaced by the new counted theorem.

## Cost-policy eligibility

Full operational observation laws remain valid over the caller's arbitrary
`AddMonoid C`; they do not equip C with an order or numerical security metric.
For matching ordered scalar costs on corresponding actual executions, reusing
the 127-bit bound at the same q requires a certified domination direction
`originalSelectedWork <= newPolicyCost`, with the appropriate pointwise or
almost-sure run law and budget transport. Erasure and input-policy pullback alone
do not prove this domination.

For other cost carriers, specify a budget observer into the proof's ordered scalar
metric and prove its observation/transport certificate, including any explicit
loss. No order on arbitrary C is inferred. A nonzero transport loss changes the
applicable budget/numerical conclusion and cannot be advertised as the original
same-q guarantee. The chosen-sampler factory's joint keypair/cache/**original
cost** continuation law remains distinct from arbitrary private-query cost or
private route/trace observations. A different private observer needs its own law.

## R8 finite completion checklist

R8 closes when: P5/all old strength ledger and P6 clean committed full gate;
C1–C5 actual production consumers/recoveries; R5 units1–6 delegation inventories;
light normal-import adaptation recipes for valid/rejected contexts,128s/192f,
effectful provider and ordered/input-dependent policy; old theorem eligibility
without automatic min under different hypotheses; all original + registered
runtime/negative/table tests; reviewed finite F6/U recovery and separate full
counted i/r row; eligible cost observers/transports; approved guard migrations;
unchanged pins/baselines;
clean recorded final head/source before==after full lint/init/axioms/test/build;
independent final review. Recover exact joint127 and all old766 bounds on SAME
canonical experiment with their original distinct contracts. No new security
exponent for192f, XOF/prehash/SHA2 or whole-engine unification is required here.

## Risks and bounded decision points

C1 freshness is stronger than node-address separation and may fail on arbitrary
adversarial cache. C3 preserves a value law, not warm cache/cost. C4 partial writes
need precise boundary agreement. C5b full joint observations can exceed old
value-only bridges. R5 semantic-guard evolution and opaque public definitional APIs
are real work, not clerical wrappers. Stop/revise a family if exact original
strength cannot be recovered; retain the working original route. No reliable
whole-migration time estimate follows from the completed P6 pilot.
