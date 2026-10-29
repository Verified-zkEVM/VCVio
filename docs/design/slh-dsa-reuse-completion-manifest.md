# Finite SLH-DSA reuse completion manifest

The original evidence checkpoint is accepted commit
`ae23574db895fd68ae28db806b54e0b3b275a551`. The clean committed full validation and independent P6 acceptance passed.
This manifest freezes the finite completion deliverables; it does not freeze the
intermediate declarations, proof bodies or public names. The later
[P5 checkpoint](slh-dsa-reuse-evidence/r6c/p5-checkpoint.md) is accepted at `fb6f14cb`;
R5 delegation and R6c/R8 completion remain open.

This finite endpoint supplements the [reuse plan](slh-dsa-reuse-refactor-plan.md),
[original strength inventory](slh-dsa-reuse-evidence/strength-manifest.json),
[R0 semantic archive](slh-dsa-reuse-evidence/r0/README.md), and
[R0b readable/runtime bindings](slh-dsa-reuse-evidence/r0b/README.md).
The [source map](slh-dsa-reuse-evidence/r6c/source-map.json) retains its original
historical provenance; every selected source anchor also matches this accepted
commit. Those historical hashes are not claims about later documentation revisions.
[Evidence and reproduction](slh-dsa-reuse-evidence/r6c/README.md),
[target-shape requirements](slh-dsa-reuse-evidence/r6c/target-shapes.md), and the
[P6 checkpoint](slh-dsa-reuse-evidence/r6c/p6-checkpoint.json) distinguish this
finite deliverable list from the per-unit claims, implementations and evidence
still needed for acceptance.

## Endpoint and exclusions

The endpoint is one canonical provider-based construction and counted experiment,
with useful shared mathematics and complementary probability arguments where needed.
A unified proof is eligible if it retains or improves every required guarantee;
permanently duplicated signing bodies behind a facade are insufficient. Five finite R6c
families below must be consumed by the real proof/construction routes. R5 then
removes duplicate implementation ownership in the named dependency units below.
A completed family is not reopened by discovering another possible extraction;
additional families become separate follow-up work. Purely specialized helpers
may remain local. No LOC or build-speed target is claimed.

Acceptance preserves or improves the end security guarantees over their original
scheme, adversary/success event, seed/hash assumptions, context/profile and
resource/lifetime regimes. Each required guarantee remains available, possibly
in a specialized module, or follows from a retained/new bound at least as strong
over that whole scope. Independent review cannot authorize its loss or narrowing;
that requires an explicit user change to the required outcome.

Intermediate theorems and APIs may change or disappear when a refactor tightens
a bound, streamlines a proof or improves reuse. Document the affected consumers
and the comparison, refinement or resource transport supporting the retained/new
guarantee. Historical types, bodies and owner snapshots are comparison evidence,
not permanent API obligations. A shorter proof can improve clarity with the same
bound; it is not itself evidence of a tighter bound. No q+1/max(1,q) substitution,
extra lifetime/width/freshness premise or numerical loss may weaken the original
security regime. Generic hypotheses such as FreshFor must be discharged in the
actual application rather than passed to the final adversary/security theorem.

Required observation laws concern the intended scheme/experiment contract, not
every old internal trace or proof representation. A changed implementation may
use an appropriate operational/distributional refinement and sound resource
domination/transport. It must account for rejected/final-loss work and must not
substitute expected cost for an almost-sure joint budget.

## Five required extraction / actual-use families

Names in this section locate original arguments or proposed consumers; they are
not permanent declaration requirements. Old qualified names and sources are in the linked source map.
Each family needs ordinary-import type/axiom witnesses and actual production use.
A test-only reproving wrapper is useful evidence but does not finish delegation.

The **52** named source declarations are a finite change-impact inventory, and
are absent from the original RAW1242 table. Their first-line headers locate
arguments, not complete contracts. For each unit state the proposed security or
functional claims and relevant carrier/sampler/policy/observation maps, identify
which anchors are retained, strengthened, replaced or retired, and review the
actual proofs, axioms and consumers. Use old type/body/dependency captures where
they help establish that comparison, without requiring a new complete capture
of every intermediate before implementation. Check existing owners before adding
a generic mechanism. The five families and six construction layers fix the
functional endpoint; they do not require retaining 52 declarations.

### C1. Adaptive sampler: finish actual ownership and consumers

Existing generic owner: `OracleComp.RandomOracleTraversal` in
`VCVio/OracleComp/QueryTracking/RandomOracle/Traversal.lean`. Use its
evaluate/sample/program and Separated/FreshFor mechanisms and laws.
Do not add another traversal. Accepted A Frame remains its effectful frame API.

Original comparison anchors, namespace `SLHDSA.SHAKE128s.GraphFreshSampling`:
`evaluate_eq_sample`, `program_congr`, `program_update_outside`,
`evalDist_sample_eq_uniform_program`, `evalDist_evaluate_eq_uniform_program`.
The five definition equations and five theorem types identify the original
specialization. Proposed ledger group: `R6c.Sampler`. Make the real proof uses
consume the generic mechanism, with the required full state/cache observations;
document any intermediate/API replacement and evolve affected guards explicitly.

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
Their hypotheses must be explicit and discharged for the actual clients, not assumed as fields.
Uniform-prefix laws require their own sampling hypotheses: zero-padding for m<n
does not yield uniform n-byte output. The universal effectful programme equality
keeps all validated parameters without Width, PrefixFits or FreshFor premises.

### C2. Independent moments: use the generic proof in the real FORS tail route

Existing generic owner:
`ToMathlib.Probability.Moments.IndependentPowers`, namespace ProbabilityTheory.
Preserve the two arbitrary-order independent binomial power laws, the centered
sum polynomial through six, its zero/succ equations, and finite-sum law.
No new Poisson API is required to complete this family.

Original comparison anchors in `SLHDSA.SHAKE128s.ForsConcentration`:
`independent_integrable_add_power`, `independent_integral_add_power`,
`sumMoment` (all orders, including fallback >6), `sumMoment_zero`,
`sumMoment_succ`, `independent_sum_moments`, and
`poisson_centered_sum_moments`. Proposed ledger group `R6c.Moments`.
The production FORS concentration/tail argument must consume the generic
finite-sum mechanism and retain or improve the resulting security bound under
the original measure, integrability and moment assumptions. The accepted separate test theorem
`Refactor.IndependentPowersRecovery.poisson_centered_sum_moments` is not enough.
The named original proof chain is comparison evidence, not a permanent intermediate API.

Reuse criterion is intrinsic mathematics: no SLH imports/constants in generic
owner; Mathlib ownership/search check; actual production specialization; existing public
`iIndepFun.integral_pow_six_finsetSum_of_signs` consumer with polynomial
15*n^3-30*n^2+16*n, including n=0,1. No artificial second cryptoscheme is needed.

### C3. Presampling: extract only the two local value-law mechanisms

Intended owner: existing RandomOracle/DeferredSampling layer, or a small leaf
below it after checking current Commute/Programming laws. Reuse randomOracle,
QueryCache, simulateQ and existing traversal; no new ROM or world interpreter.
Finite targets: one fresh-entry prepend value-distribution law and its adaptive
traversal prepend law, generic in input/output and ambient private sampling.
Original anchors are `Presample.evalDist_prepend_fresh_world`,
`Presample.evalDist_prepend_worldEvaluate` and `worldEvaluate`'s lift of existing
Traversal.evaluate. Retain their required value laws through the generic mechanism,
with documented replacement or retirement of intermediate APIs. Proposed ledger group `R6c.Presample`.
`cacheQuery_comm` should reuse an existing update lemma, not grow another API.

Actual consumers: original `evalDist_prepend_warmup` (keygen graph warmup) and
`evalDist_prepend_warmup_after` (post-private-seed continuation), through the
original `evalDist_counted_warmed` route. Preserve their precise advertised
projection: they compare downstream value laws, NOT final-cache equality.
Warmup remains deliberately outside the selected counter in that transformation;
never present it as a cost/cache-preserving actual execution or ignore repeated
query multiplicity. The separate full joint keygen/observer P5 contract is accepted
for its actual chosen-sampler case; this value-law family does not generalize it.

### C4. Programming by dependency agreement

Intended generic owner: `RandomOracle/Traversal/Programming` under the existing
traversal, with no HashSig imports. Finite mechanism: agreement outside remaining
writes, preservation after one assignment, input agreement when all read children
agree, and deterministic program = final cells + cache written in SAME list order.
Do not add rank sorting, Fintype enumeration or a second evaluator to the owner.
Freeze explicit topological read-before-write assumptions before authoring.

Original anchors are `CanonicalGraph.Programming.AgreesOutside.assign`, `input_eq_target`,
and `program_eq_cacheFrom`; the old Pairwise RankLE hypothesis discharges the
new local read-before-write condition via accepted Graph.Children rank laws.
Retain original cacheFrom order and full cells/cache equality.
Proposed ledger group `R6c.Programming`. The required behavior is the complete
programming/observation law, not permanent retention of those local definitions.

Actual consumers: old full-graph 128s `warmup_uniform` and 192f canonical FORS
subtree/forest programming using accepted B dependencies and C/D output stability.
192f need not recreate a rank-sorted WHOLE-SLH graph or infer a 191-bit theorem.
The same generic programming lemma must handle both; partial traversal leaves
unwritten cells at their initial values and the target-agreement premise must
explicitly cover those cells. No tautological final-state definition substitutes
for proved child-read availability or output persistence.

### C5. Exact counting and answer-representation transport (two finite slices)

#### C5a. Exact counts and retained/improved verifier guarantees

Intended owner: `VCVio/OracleComp/QueryTracking/QueryBound/Exact` (final path after
existing-owner check), reusing existing QueryCostExactly for instrumentation.
Finite declarations: ExactQueryCount, pure/query constructors, bind, map;
generic finite sequencing and list fold count; transport to existing exact cost.
Original anchors are `Generic.ExactQueryCount`, `.bind`, `.map` and
`VerificationQueries.exact_bind`, `exact_map`, `sequenceFin_exact`,
`foldlM_exact`, `exact_cost`. Proposed ledger group `R6c.ExactCount`.
Keep concrete `Bounds` and verifier branch/chain arithmetic local unless the
existing QueryBound API already supplies a lemma; do not introduce a cost model.

Actual consumers: original concrete `fors_exact` and `wots_exact` verifier routes,
and their canonical provider counterparts through R5 observation equalities.
Retain the guarantees supplied by `VerificationBudget.verification_count_bounds`,
`verification_accepted_count_bounds`, `accepted_outcome_work` and q<569 zero,
or prove stronger guarantees on their original framing/acceptance/resource scope.
Calls include cache hits; exact count is not number of distinct cache entries.

#### C5b. Answer representation transport, not another game/ROM

Intended generic owner: `VCVio/OracleComp/SimSemantics/QueryImpl/Relabel` or an
existing equivalent after owner search. Use dependent QueryImpl + existing
writer/state fold composition. Finite original Bridge.Transfer targets:
`simulateQ_relabel_unlabel`, `simulateQ_unlabel_relabel`, `mapCache_empty`,
`mapCache_cacheQuery`, `run_simulateQ_relabel_from`,
`simulateQ_writerT_run_compose`, `simulateQ_writerT_stateT_run_compose`.
Use these seven anchors to compare the original specializations with the new
mechanism. Document intermediate replacements/retirements. Proposed ledger group `R6c.Relabel`.

Actual consumers: existing FIPS byte/full-answer bridge using answerEquiv and
canonical shared-experiment observation with the corresponding oracle-answer
representation. Required pullback includes cache update, reply/log observation
and caller's ordered cost policy. The sampler-preserving answer law is separate
and explicit; arbitrary truncation/padding is not an equivalence. Original
`runBySource_evalDistEq` and `hasSecurityBits_of_bridge` identify the specialized game
consumers; retained/new corollaries consume the generic fold laws without a second
security semantics. Generic no-HashSig import audit is mandatory.

## Specialized quantitative guarantees and certificates

These guarantees remain available or are dominated over their original scopes.
Their specialized proofs may stay local; a proved tighter or simpler replacement
can retire intermediate certificates without retaining their original names.

- #766 CoverageBound/JointBound/ByteBound/WeakKeyBound/HedgedKeyBound and their
  general witness, byte-clash, seed coupling, per-seed/averaged/randomizer bounds.
  They cover different resource predicates/modes; they are not duplicate 127 math.
- #912 ForsMoments concrete polynomial certificates, Poisson rate3 / power14 /
  centered-six constants, occupancy/de-Poissonization thresholds, disclosure and
  share ledger/charging/provenance, WorkTarget/WorkFinal final accounting.
  These are the specialized tight quantitative proof, not generic graph execution.
  C2 factors independent-sum algebra; changing quantitative certificates needs
  proof that the resulting end guarantee is at least as strong.
- Exact 127 at ORIGINAL q>=1, probability-one ACTUAL combined work and original
  lifetime eligibility; q<569 zero (which has no lifetime premise); supported
  verification 569..3824 with their original framing/acceptance distinctions;
  universal3929 cap; no cap confused with exact every-path count.
- All six #766 deterministic/hedged families, full weak-seed term, n=32 sharper
  minimum, per-seed and arbitrary seedDist/epsilon-randomizer families, wire/EUF
  corollaries. No lifetime restriction is added to general #766 claims.
- Exact18-row CSV bytes/evaluator/certificates and range inequalities. These are
  regression artifacts, not substitutes for all-q kernel recovery.

## R5 finite dependency units (after P4/P5/P6 and affected guard migration)

1. WOTS primitives/chain/keygen/sign/recover: canonical Wots/GeneralWots provider
   programs; establish the sign/public-key/recovery refinements identified by Bridge.Wots.
2. FORS recursive tree/auth/sign/recover: canonical Fors provider; use accepted
   naturality/P4 and C/D full program observation. Keep secret-first order and
   exact parser/defaultbits; preserve PRF→F, left→right→parent and output stability.
3. XMSS/Merkle: after1, canonical Xmss effectful tree/auth/climb; establish the
   node/sign/climb/public-key/root refinements identified by Bridge.Xmss.
4. Hypertree: after1–3, canonical GeneralHypertree layers/root; establish the
   layer/sign/root/verify/keygen refinements identified by Bridge.Hypertree.
5. Scheme/codec/view: after1–4, canonical GeneralScheme + existing codec and
   fromInternalPure family; retain randomizer/mode, context validity, optional
   rejection and zero-work losing branches in the intended experiment. Establish
   the external keygen/sign/verify and internal/relabel refinements identified by
   Scheme.* and Bridge.Scheme.
6. Game/observation entrypoints: after5 and complete P5, canonical counted
   experiment + Reply/readback view; retain or improve the old game/security
   guarantees, with documented public replacements or compatibility exports.
   Do not retain independent executable game bodies merely to preserve names.
   Chosen actual sampler joint keypair/cache/original-cost continuation law is
   required; private draw reorder does not imply arbitrary private trace equality.

Each unit removes duplicate executable ownership only after the required
operational/observation laws and retained/improved end guarantees are proved.
Review real consumer migration and deliberate intermediate/API retirements;
compatibility exports are a choice. Complementary probability routes stay where
needed for a guarantee. Use finite per-unit change-impact inventories and
independently review each self-contained implementation unit.

## Historical comparison archives and guard evolution

R0a's original snapshot stores 1242 semantic records rooted at 112 constants,
77 theorem contracts and 11 groups. Its AST/dependency/owner/axiom comparison
can reject an extensionally equal refactor. That is honest evidence of a change,
not proof of a security regression. The 52 selected anchors are not themselves
RAW1242 entries; the archive does not claim complete intermediate coverage.
R0b also records readable/runtime sources, CSV, executable registration and the
driver scaffold. Preserve these historical archives and their original provenance.

For an affected unit, explain which old claims remain required, which are
strengthened or replaced, and which intermediates are no longer needed. Supply
the Lean security comparison and appropriate operational refinement, equal-law
or resource-domination evidence. Internal proof values, representation choices
and traces need not be identical when that evidence establishes the intended
scheme/experiment semantics and honest resource scope. Exact observations remain
required where they are part of an advertised contract; hidden rejection or
final-loss charges cannot be erased by changing a guard.

Evolve active guards in the same independently reviewed unit so they check the
retained/new claims and meaningful branch/cost/parser behavior. A guard tied only
to a retired intermediate may itself be retired with justification. Never edit
an old archive or relabel an unrun/failed check to pretend the implementation is
unchanged. New captures and comparison mappings must identify their actual
source and coverage honestly; no blanket baseline refresh substitutes for proof.

## Security comparison and independent universe coverage

The **42** original F6 goals, level-name lists and proof/schema captures remain
immutable historical evidence. Later implementations need not export all 42
names, reproduce every raw AST or retain every intermediate proof route. They
must retain or improve the substantive guarantees over their original scopes,
with sound universe instantiation and ordinary checked consumers. When adapting
a frozen metaprogram, review its explicit universe arguments: recompiling source
does not repair a stale `Expr.const` level vector.

The full counted generic EUF-to-SUF comparison is quantified independently over
oracle index universe i and runtime-carrier universe r, including the advertised
algorithm, request/reply, observer, runtime and policy parameters. Do not replace
that generality by i=r, either universe fixed to zero, or extra security premises.
The original generic row 36, 39 counted concrete rows and two DIRECT rows 37/38
provide comparison cases. Their accepted recovery records establish that work
at the recorded checkpoint; future simplification can use different intermediate
statements while proving the retained/improved end guarantees.

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

R8 closes when: P5/retained-or-improved security guarantee mapping and P6;
C1–C5 actual production use; R5 units1–6 canonical delegation;
light normal-import adaptation recipes for valid/rejected contexts,128s/192f,
effectful provider and ordered/input-dependent policy; old theorem eligibility
without automatic min under different hypotheses; meaningful registered
runtime/negative/table tests; checked security/universe comparisons and full
counted i/r generality; eligible cost observers/transports; reviewed guard changes;
unchanged pins/baselines;
clean recorded final head/source before==after full lint/init/axioms/test/build;
independent final review. Retain or improve joint127 and all required766 security
regimes on the same canonical experiment with their distinct eligibility contracts. No new security
exponent for192f, XOF/prehash/SHA2 or whole-engine unification is required here.

## Risks and bounded decision points

C1 freshness is stronger than node-address separation and may fail on arbitrary
adversarial cache. C3 preserves a value law, not warm cache/cost. C4 partial writes
need precise boundary agreement. C5b full joint observations can exceed old
value-only bridges. R5 semantic-guard evolution and opaque public definitional APIs
are real work, not clerical wrappers. Revise a family if it cannot retain or
improve a required security guarantee on its original scope; retain the working route. No reliable
whole-migration time estimate follows from the completed P6 pilot.
