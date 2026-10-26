# Reusable SLH-DSA specifications and complementary security proofs

Status: proposed gated execution plan, 2026-10-26. The three bounded prototypes below are
checked; the shared experiment, effectful component refinement and complete migration are not.
Plan approval is not implementation acceptance.
No production code, dependency, public theorem or default build is changed by this document.

The objective is maximum useful generality **without sacrificing an existing security bound or
strengthening its resource premises**. Use SLH-DSA as the constructive anchor. Share canonical
construction, request, observation and probability infrastructure; retain two complementary
proof methods until a stronger unification is actually proved. A cleaner facade is a step,
not the endpoint. A near-total proof rewrite is an option only when evidence favors it.

## Recorded inputs and research scope

The implementation base is merged #912, `9b4e1a0307414994c5fe7b136d4c52cdd39333fa`, tree
`e10d9c5580c60c61e60659a3895c95e0f443b5a2`. This is the same source tree as the reviewed
integration head `f2bd85c91e5a0df4d874c320f7ad3174606d91fe`. Preserve #766's merged FORS repair,
#886's generic APIs and #911's dependency update. The local unpublished withdrawal `92eaa1af`
is not the implementation base and does not authorize deleting either proof method.

Use Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, PolyFun
`ecac686fd8a3b4763d3df2e738c91947bdec40d6`, and all eleven manifest revisions. The manifest
SHA-256 is `68e3e9f60f635be3e88e676b871b3419004f882626da3ab85523cb2b374da8d2`.
The prototypes ran in an isolated checkout at `92eaa1af9d9c120e6e6e9d3036aca1af9e751573`,
with its private locked dependencies. Their framework/#766 inputs are unchanged from the base;
P1 additionally checks all 295 local import-closure blobs against both commits.
These are scoped prototype results, not a recorded-head acceptance of future refactoring.

Read the [agent guide](../../AGENTS.md), [contribution policy](../../CONTRIBUTING.md),
[crypto guide](../agents/crypto.md), [query-tracking guide](../agents/query-tracking.md),
[oracle guide](../agents/oracle-comp.md) and [probability guide](../agents/probability.md).
The research examines interfaces and representative proof assemblies, not every line of the
221 specialized probability-proof modules. No target line-count or build-speed saving is proved.

## Strength and behavior ledger

Keep model, scheme, success event, observer, probability interpretation and resource predicate
attached to every certificate. A shared name such as `WorkBound` does not make them equivalent.

| Required result | Preserve exactly |
|---|---|
| General #766 construction/security | Arbitrary-depth/provider APIs, their current hypotheses, `securityTarget_two_one`, SUF/EUF forms, per-seed and averaged results; no new adversary or hash assumptions |
| Six SHAKE sets, deterministic | Full `byteBound + honestAdrsCount / 2^256 * weakSeedFactor(everySeedBound)`; keep existing `optRand` generality and structural `RomQueryBound qh qs` |
| Per-seed/refined #766 families | Preserve epsilon-randomizer and arbitrary seed-distribution forms, outside-weak-seed bounds, sharper every-seed `n=32`/minimum forms and their exact current hypotheses, not only averaged headlines |
| Six SHAKE sets, hedged | The distinct sharper hedged expression, uniform randomizer contract and full weak-seed contribution, including the `n=32` treatment |
| Original #912 theorem | Exact success bound `q/2^127` for every original `q >= 1`, actual selected joint work bounded with probability one, actual signing count at most `2^64` with probability one |
| Original #912 game | Variable contexts, optional signing replies, strict byte signatures, generated-key support, one empty-cache shared 30-byte oracle; keygen/signer hashes and private draws execute but are excluded from selected work |
| #912 cost-tightness auxiliaries | Zero-win result below 569; well-framed/parseable verifier 569–3824 from arbitrary caches, accepted variants and accepted-outcome work lower bound, under exactly their original support/framing/acceptance premises |
| Common wire interface | Advantage correspondence, syntactic-to-counted transports, literal `(qh+qs+3929)/2^127` and the full minimum on their common scope; do not replace an actual joint premise by separate maxima |
| Conformance/numerical interfaces | Existing canonical codecs, algorithm/query behavior, secret-first FORS order, evaluators, 18 exact CSV rows, kernel point/range certificates, profiles and tests |

The canonical experiment must not bake in or enforce `2^64`: #766's general results have no
such lifetime restriction. That number belongs to the #912 certificate's eligibility predicate.
Preserve the original domain `q >= 1` and the proof that nothing wins below 569 selected calls;
no `q+1`, `max 1 q`, additional structural cap, or worst-case verifier substitution is allowed.
Losing outcomes, repeated/cache-hit calls and rejected signing requests remain in the premise.

The [R0 declaration manifest](slh-dsa-reuse-evidence/strength-manifest.json) records 77 actual
source declarations in 25 groups, with qualified names, source headers, file hashes and semantic
anchors. It includes per-seed/epsilon-randomizer and sharper `n=32`/minimum families, derived EUF,
profiles, the exact #912 game/budget predicates and protected provider/honest-work APIs. Source
headers are a research inventory; R0 still captures elaborated statements/axioms and observer
laws at the implementation head. A list of `#check` names alone is not strength preservation.

A new cost policy describes declared query/request events, not arbitrary CPU or wall-clock work.
Changing weights does not automatically retain 127 bits. To reuse it at the same q, prove
`originalSelectedWork ≤ newPolicyCost` pointwise/on actual runs: the new policy dominates the
original, not conversely. Otherwise prove the exact conversion separately; retain the old certificate.
Expected cost, almost-sure cost and a probability-one event are different predicates.

## What is shared and what is genuinely different

#766's [canonical construction](../../HashSig/SLHDSA/GeneralScheme.lean) uses validated parameters,
abstract carriers and provider/public-hash interfaces. Its [security proof](../../HashSig/SLHDSA/Security/CoverageBound.lean)
combines hidden-seed idealization, trace witnesses, role-tagged answer tapes and weighted target
coverage, then byte-model/weak-seed transport. Its raw bound is global in `qh,qs`; the tables and
budget rectangles are additional corollaries, not its only security statements.

#912 has a second fixed-128s transcription, a presampled honest graph, FORS load/concentration
arguments and blind shared-cell/key-hit ledgers. Its final proof charges an answer half and a
shared half to actual joint work, using accepted verification's cost to absorb fixed terms.
The exact global 127 statement is not an arithmetic consequence of the current #766 formula.
An inexpensive replacement proof has not been established. Both proofs use the same framework
and classical-ROM assumptions on their common scope; different methods do not diversify those
assumptions. Preserve the real mathematical result without presenting it as broader security.

There are 238 original specialized modules: 221 `Proof`, eight `Statement`, eight `Bridge` and
one `Generic`. All belong to the original headline closure. Moving generic lemmas changes their
owner and clients; it does not imply that the remaining probability argument disappears.

## Alternatives and decision

| Alternative | Exact-strength risk and reuse | Decision |
|---|---|---|
| Keep both stacks with a facade | Low immediate proof risk; leaves competing algorithms/games and internal coupling | Useful baseline and transition only |
| Mechanical generic extraction | Removes some misplaced instrumentation/transport duplication; does not by itself unify construction or consumers | Early work units, not the endpoint |
| Shared canonical construction/experiment, two methods | Makes adaptations use one specification while preserving both mathematical arguments through exact refinements | Target architecture |
| Deep graph/probability parameterization | Can reuse graph/cache/moment mechanisms; parameter and numerical certificates still need real proofs | Required incremental direction, with tiered real-client/math ownership criteria |
| One unified probability proof or near-total rewrite | Could remove more duplication; no demonstrated derivation of every original bound/premise | Conditional research option, never the starting assumption |
| Withdraw #912 entirely | Removes the distinct actual-joint theorem and interfaces | Superseded by the user's strength-preservation requirement |

Choose the shared core plus evidence-led deeper extraction. Do not stop at namespace changes,
or move 51,000 lines under a generic name while importing fixed byte/message/128s constants.
Full unification becomes an option only after it derives every ledger entry with unchanged
premises and exact expressions, with evidence that it improves maintenance/adaptation.

## Target ownership and dependency direction

| Layer | Owner and contract |
|---|---|
| Construction | Existing SLH-DSA parameters, representations, provider-based component programs and canonical codecs; pure/concrete and oracle interpretations are views |
| Generic instrumentation | Existing `QueryTracking`/`SimSemantics` writer, logging, ROM, support and cost APIs; no HashSig imports |
| Signature semantics | One Reply/readback-aware signing view and counted strong experiment in `CryptoFoundations/SignatureAlg`; existing public interfaces are compatibility views |
| SLH refinement | Address/codec/graph equations and exact program/cache/source-observation laws; generated-key consistency proved here |
| Probability methods | General weighted-coverage method and specialized warmed-graph/joint-work method consume shared contracts; numerical specialization remains explicit |
| Consumer entry points | Light specification, request-adaptation, observation and certificate leaves; profiles expose eligible theorems and their exact resource predicates |

Use existing `Params`, `ValidatedParams`, `CorePrimitives`, `GeneralScheme`, `SecretProvider` and
codec ownership. A provider-first canonical implementation can make current pure/oracle twins
specializations, but it needs an import-DAG/component migration; do not create another twin family.
Initially retain current definitions and prove component laws before delegating their bodies.
Keep existing symbols and theorem statements as exact facades during the transition.

The public algorithm has one canonical meaning. A graph or bit-vector view may remain as an
internal proof representation, with a certified refinement. It must not become a second public
FIPS specification that downstream clients have to choose or reimplement.

Before deprecating/removing an old public declaration, recover its exact type, model and budget
meaning, including stronger auxiliary cost/security bounds; provide the ordinary consumer
replacement and prove the compatibility observation. Review the consumer migration and the
ledger together. The headline inventory is not permission to silently drop unlisted helpers or
external-facing types. Keep exact compatibility names/views until that criterion passes.

## Signing, rejection and the one experiment

The following is a proposed interface shape, not a completed generic implementation:

```lean
universe v
structure SigningView (m : Type → Type v) [Monad m]
    (Request PK SK Sig Reply : Type) where
  keygen : m (PK × SK)
  sign : PK → SK → Request → m Reply
  verify : PK → Request → Sig → m Bool
  readback : Reply → Option Sig
```

The total #766 instance uses `Reply=Sig`, `readback=some`; the rejecting #912 instance uses
`Reply=Option Sig`, `readback=id`. Final candidates are `Request × Sig`, not optional signing
replies. This preserves each signing oracle's observable reply type. Avoid unnecessary equality,
finiteness, sampling or probability assumptions on Reply in structural definitions.

Keep every raw `(request,reply)` entry. Derive successful returned pairs by `filterMap readback`;
strong freshness means absence of the exact request/signature pair in that projection. A rejected
request is logged and charged before signing; it is a returned value, not monad failure.
Readback need not be globally injective. Byte-normalizing readback requires its own canonicality
proof before claiming raw-byte SUF; security-relevant reply metadata belongs in Sig.

Use one free-world experiment for keygen, adversary/signing and verification, interpreted through
one shared ROM handler and initial cache at the outside. Preserve candidate, raw log, verified bit,
cache and source observations jointly. Derive old uninstrumented and counted games by projections,
not copied run bodies. Direct source tagging must match #912's residual signer-count decomposition
on all supported outcomes, including its no-underflow invariant.

Reply/Sig separation is necessary but not sufficient for partial frontends. Mapping a final None,
invalid context or malformed signature to an arbitrary typed sentinel may run verification on a
losing branch and break exact joint `q`. No generic zero-cost sentinel is assumed. Preserve actual
zero-work rejection, or prove an explicit cost-preserving partial/event adapter. The old structural
wire inequality does not automatically supply that law. Invalid signing queries generally give a
filtered-prefix relation and a count inequality, not equality, in a reduction to a total signer.

Expose totality/losslessness where converting AE cost into `Pr[event]=1`; a zero-mass computation
can satisfy an AE predicate vacuously. Discharge those hypotheses for the actual finite-uniform
SLH instances. Do not turn rejected replies into `OptionT` failure that erases counts or the log.

## Cost-policy generality and exact observations

Build the instrumentation from existing `withAddCost`, logging and writer projections. Its policy
must see phase plus the actual oracle query (including private queries) and signing-request events,
folding into an additive cost monoid C. This admits request length, hash-input length and block-cost
policies without asking consumers to write another experiment. Require order/probability structure
only on lemmas that use it, not on the structural interface.

The five crypto coordinates are one exact instance: keygen hashes, signer hashes, direct hashes,
verification hashes and signing attempts. Constant source weights are additive observations of
that vector; they do not cover every input-dependent policy. Use a product with a custom cost
observer when simultaneous joint observations are needed. Original selected work remains exactly
signing attempts + direct hashes + verification hashes, with repeated calls charged even on hits.
Graph/cache cardinality and fresh draws must not replace call multiplicity.

For each policy transformation prove the cost pullback or exact per-step instrumented equation.
A certificate `originalSelectedWork ≤ newPolicyCost` can reuse 127 at the same q; otherwise only a separately
proved scaled/new bound is eligible. Whole-honest-work certificates remain a distinct policy and
obligation. Do not infer a full honest-work certificate from a keygen lower bound or free signer.

## Construction and representation proof obligations

First test the canonical FORS component with an effectful secret provider and a stateful oracle.
[The existing bridge](../../HashSig/SLHDSA/SHAKE128s/Bridge/Fors.lean) supplies an actual
`simulateQ_forsSign` equation at its concrete oracle provider. Lift/generalize it with aligned
handler, provider and source-cost laws; output equality alone does not establish those hypotheses.
Preserve selected-secret-first chronology, result, cache, raw effect trace and weighted source
observations. Instantiate a second real parameter/provider case, not another alias of 128s.

One-to-one query maps require matching input/readback and cost pullbacks. One-to-many steps need
an exact instrumented simulation, not only a query upper bound. Preserve arbitrary initial caches
and log prefixes. Existing provider naturality is the starting abstraction, not a reason to copy
another FORS implementation. A chronological trace assertion must detect an order/source swap.

Keygen currently agrees in law after reordering independent private seed draws. Prove the needed
joint keypair/cache/original-observer law under arbitrary continuations. A keypair marginal or
ordinary output equality is insufficient. Do not claim universal private-sampler route, replay,
checkpoint or arbitrary-cost trace equality. Custom canonical policies still execute exactly;
their transfer to a proof backend requires the appropriate observation law or metric domination.

Address validity and byte coherence stay explicit: mathematical parameter validity alone does
not prove concrete width bounds, namespace separation, parsing or uniform-output/padding laws.
New instances discharge these local construction/model laws; no adversary is asked to assume the
security conclusion or an unproved graph property in a generic record.

## Deeper generic probability extraction

| First candidate | Genuine shared statement | Two real consumers and gate |
|---|---|---|
| `GraphFreshSampling.evaluate_eq_sample` | State-and-cache program equality for a fresh, separated adaptive traversal; general Input/Output, no Experiment import | Canonical FORS and WOTS/XMSS subgraphs; exact old specialization and payload-dependent traversal tests |
| Remaining graph programming laws | Coordinate agreement, updates outside a traversal, rank/dependency evaluation and table programming | Two actual SLH graph components or parameter instances; preserve complete cache, not just returned nodes |
| `Presample` local lemmas | Prepending unused samples and adaptive traversals preserves the advertised law | Keygen warmup and later continuation warmup; keep outside the selected counter and preserve conditional cache law |
| Independent-power/moment lemmas in `ForsConcentration` | Integrability/binomial moments for independent variables, before concrete 14th/sixth moments | Existing real FORS use, exact old specialization and ordinary public math consumer exposing assumptions; check Mathlib ownership first, no invented second cryptoscheme |
| Exact counts/answer relabelling | Existing cost semantics and equal-information sampler-preserving bijections | Total/rejecting scheme views and concrete byte/bit view; exact policy/log/cache diagrams |

These are extraction candidates, not accepted proofs of universal graph security. Current graph
coordinates, ranks, width arguments, child equations and final concentration/cost arithmetic bake
in 128s constants. Generalizing them and producing another parameter's quantitative certificate
requires new work. No automatic 127/191/255-bit or SHA-2 claim follows from a parameter record.
A sampler-preserving answer bijection is not arbitrary truncation or an XOF model; preserve the
separate prefix/padding and role-encoding arguments. Reuse existing deferred-sampling/coupling
kernels rather than another probability semantics.

Use tiered reuse criteria. The signing architecture needs both actual total/rejecting clients;
construction/graph abstractions need two genuine SLH components or parameter instances. A toy
can falsify a bug but cannot be their second construction consumer. Intrinsically generic
measure/moment/structural math may have one real FORS use if it has no SLH types/constants/imports,
a justified existing Mathlib/framework owner, exact old specialization and an ordinary public
math consumer exposing the assumptions. Do not invent another cryptoscheme to satisfy a checkbox.
A model-specific one-use helper stays scoped. Every extraction removes a real ownership/import
coupling. No numerical slack, extra adversary premise or whole-security conclusion hidden as a
field may pay for generality; retain specialized tight constants/certificates.

## Required SLH graph-parameterization pilot

Deep proof reuse is part of completion, not an optional task after a facade release. In addition
to the concrete generic sampler and moment extractions above, build a structural graph instance
from canonical parameters/provider programs and instantiate it for SHAKE-128s **and SHAKE-192f**.
Downstream adaptation should change local definitions/laws/certificates, not copy 221 proof files.

The pilot covers finite structural coordinates, encoded addresses, ordered children, rank decrease,
canonical component evaluation and the provider/source observer. Replace baked-in 7/14/12/35/17
coordinates and ranks with formulas justified by validated parameters; prove the concrete width
and namespace laws separately. Preserve effectful traffic, not just the value recurrence.
Use the same generic state/cache traversal theorem in two actual component/parameter instances.

Keep this structural contract distinct from quantitative side certificates: output/cardinality
and sampler laws, FORS load/moment inequalities, ledger charges and the final security exponent.
Recover the existing 128s instance and exact 127 proof without slack before replacing its route.
The 192f structural instance uses its existing applicable general bound; no new 191-bit joint
claim is inferred. Mathematical validity alone does not imply every byte/address constraint.

If this pilot cannot support real parameter/provider adaptation without importing fixed-128s
programs or weakening a bound, revise the architecture before destructive migration. A facade
and a few moved helpers do not satisfy this completion gate. Full one-engine probability
unification remains conditional; useful generic mechanisms plus specialized tight certificates
are an acceptable endpoint when each serves real clients.

## Downstream adaptation recipes

| Consumer changes | Intended reuse | Additional obligation |
|---|---|---|
| Valid context/message policy | Generic Wire plus canonical frame, as P1 | Injectivity, length validity and unchanged freshness/budgets |
| Rejectable request policy | Shared partial frontend/readback log | Partial injectivity, reject-then-continue behavior, final-loss cost law |
| Approved SHAKE set/mode | Canonical profile and general proof method | Select the exact deterministic or sharper hedged certificate; keep weak-seed terms |
| Effectful secret provider | Canonical provider component and naturality | Handler/provider refinement and source/cost law; new security assumptions exposed if provider changes |
| Input/phase-dependent resources | Same instrumented experiment, chosen C/policy | Structural/pathwise/AE premise and exact observation; original-work domination for reuse of 127 |
| New graph/parameter constraints | Local graph and encoding contracts | Width/separation/cell laws and quantitative certificates, not an inherited 128s constant |

The consumer selects a certificate whose actual hypotheses hold. Even on one canonical game,
structural separate caps and an actual joint cap are not interchangeable. Form a minimum only
when both eligible certificates have been supplied on the same success event and interpretation;
there is no automatic "best bound" that manufactures a missing budget assumption.

## Checked prototypes and deliberately open gates

[Evidence and reproduction instructions](slh-dsa-reuse-evidence/README.md) bind final source/log
hashes and the clean isolated environment. All three use Lean 4.35, explicit autoImplicit=false,
default recursion/heartbeat limits, private locked dependencies and standard axioms only.

| Probe | Checked result | Limit |
|---|---|---|
| P1 `VariableContextWire.lean` | Canonical Wire handles per-query valid contexts; full old bound/weak term and sharper hedged bound; actual 128s/192f instances; 256-byte unchecked-frame collision | No rejected/optional signing experiment, exact joint-127 port or graph migration |
| P2 `WeightedBudgetProbe.lean` | Exact weighted structural-to-pathwise bridge; adaptive joint cap 2 but necessary separate maxima 2+2; nonunit 3/1 policy cap/witness 6, erasure, AE and probability-one event | A free-computation consumer, not complete SUF/source/cache specialization or input-dependent-policy execution |
| P3 `ReplyLogProbe.lean` | Total replies specialize to actual `signingLogContains`; optional-success projection; raw log length 3 versus successful length 2; replay/different-signature checks | Pure log laws; no execution/charging of a rejecting signer, full experiment or security transfer |
| P4, first implementation gate | Effectful canonical FORS/tagged weighted observer, second actual instance | Unproved; must pass before broad construction/proof migration |
| P5, full preservation gate | One actual shared SUF experiment, exact old/new outcome/log/cache/source refinements and all-q headline recovery | Unproved; must pass before deleting superseded algorithms/games/proof routes |
| P6, structural generality gate | Shared graph coordinates/address/rank/provider observer on 128s and 192f, with separate quantitative certificates | Unproved; required for completion; no automatic extension of the 127 exponent |

P1's independent scoped review is `b8365df9875f916e39318383fd3cbec4f142157969f99d6c50b022537bad097a`;
P2/P3's is `e945431cbdd0fa70fed5feab0e23465e7004118443cc43db8844435505709b0f`.
Those reviews accept the stated prototype scope, not this full implementation plan or P4/P5/P6.
P4/P5/P6 are gates within an approvable execution plan; their being open is not a prohibition on
starting their implementation, and their planned status is not permission for early deletion.

## Work units, dependencies and acceptance

Each unit is a separate reviewable commit after independent adversarial PASS and appropriate
checks. Root orchestration owns commits; authors freeze exact packets before review. The first
units add contracts and proved compatibility; retain original theorem routes while porting.

| Unit | Dependencies and deliverable | Required acceptance |
|---|---|---|
| R0 strength baseline | Recorded base/lock, theorem types/axioms, models, observer/budget predicates, exact numeric artifacts and explicit old tests | Complete ledger manifest; arbitrary-q preservation criteria, not just sampled output |
| R1 generic owners | R0; source/phase/input cost policy, Reply/readback/log core, existing cost/exact-count/relabel ownership | Two existing total/rejecting clients; no HashSig/fixed-message imports in generic modules; no duplicate cost semantics |
| R2 frontend/experiment gate | R1; rejectable policy and one actual counted experiment over the canonical view | Reject then continue; raw prefix/log/count/cache laws, repeated hits and exact source vector; nonunit and input-dependent actual consumer; no sentinel-cost trap |
| R3 component gate P4 | R1; canonical effectful FORS/provider refinement and chronological tagged observer | Two actual parameter/provider instances, hidden provider traffic and exact weighted costs; adversarial order/source controls |
| R4 full gate P5 | R2/R3; concrete keygen/caches/answer representation and old/new game specialization | Original joint probability-one 127 at exact q/lifetime, every original #766 bound/hypothesis, losing/invalid branches; all-q kernel proofs |
| R5 canonical delegation | P4/P5/P6; migrate WOTS/FORS/XMSS/hypertree/scheme/view bodies in dependency-complete units | Public equations preserve each old result and effect observation; remove a duplicate only after complete old theorem recovery |
| R6a generic probability owners | R1; general-Input/Output adaptive sampler plus independent-moment family, after existing-owner search | Tiered reuse criteria: real graph clients or intrinsic public math with actual FORS use; exact old specialization, no fixed-128s import/slack |
| R6b graph gate P6 | R3/R6a; canonical-parameter graph on 128s and 192f, structural laws separate from quantitative certificates | Actual coordinates/address/rank/evaluation/provider observer reuse; recover old 128s specialization; revise architecture if it fails |
| R6c deeper proof extraction | R6b; further theorem families selected by demonstrated shared clients | Same exact-strength/consumer gates; document genuine new math and retain specialized side certificates |
| R7 consumer surface | R2/R4; light construction/adaptation/observation/certificate leaves and examples | Real changed-context, parameter, provider and resource consumers without engine rewrites; import and global-attribute guards |
| R8 final migration gate | R5/R6a–c/R7; clean recorded committed source/generated imports and full validation | Ledger complete, all original regressions and exact 18-row artifact, strict before/after head/dependency cleanliness and independent final review |

R4/P5 uses the existing unchanged representation bridges to establish the shared experiment's
concrete specializations first. It does not require replacing every construction/proof body.
After the graph pilot also passes, R5 delegates or retargets bodies component by component
against those proved contracts;
there is no circular requirement to finish a whole rewrite before validating shared semantics.

R6a–c proceed incrementally alongside compatibility work; required probability extraction and
the graph pilot must not be postponed indefinitely
behind a facade-only completion claim. Whole-engine replacement is a new decision after local
extractions expose a genuinely shared argument. Any failed exact-strength gate retains the old
working proof route and narrows/revises the proposed abstraction rather than weakening a theorem.

## Tests, imports and final evaluation

Retain original compiler, Game, WireBridge, FORS-order, wire/codec/ACVP/table and framework tests.
Runtime assertions must execute through explicitly registered Lake steps; library-glob compilation
is not execution. Preserve full-hash/selected-work/fresh-draw/private-sample distinctions and the
literal fixture counters. Add asymmetric phase/input traces and an input-size-dependent policy.
Reject replay, accept a different valid signature on the same request, and charge failed requests.

Negative controls must catch source/order swaps, free cache hits, omitted rejection charges,
expectation substituted for almost-sure cost, and inadmissible weights inheriting 127. Add a
final-invalid-request control that fails if a fallback adds verifier work. Preserve small-q and
lifetime endpoints. Sampled counts/18-row arithmetic complement the all-budget kernel proofs;
they cannot replace exact statement/premise recovery. Keep original axioms and all baselines.

The specification, counting and adaptation leaves must exclude the 221 proof files. Existing
Game/Transfer/FIPS205 leaves already do this; FIPS205 already excludes Statement.Scheme and its
global Fin.cases compiler override. New ownership and real reuse, not renaming those leaves, is
the goal. Generic modules import no HashSig. Keep the generated legacy HashSig umbrella initially;
run update-lib.sh for legitimate additions and commit generated imports before final validation.

Separate the proved Fin.cases optimization into an appropriate explicit compiler owner/client
when migrating the transcription, with the existing bounded canary and independent review. It
must not leak through an inert specification import. Use finite-type laws without eagerly building
huge graph enumerations at module initialization. Preserve ordinary prologues, attribution,
public scopes/per-definition exposure and the existing proof/FFI/Interop boundaries.

After each committed semantic unit run its targeted build, public signature/axiom checks and
meaningful runtime/negative controls. Before final acceptance run the repository's full
validate.sh --lint --test --axioms through the strict recorded-head helper, with clean source
and all eleven locked dependencies before and after. Regeneration is preparation before commit,
never a hidden mutation inside the final acceptance run. Preserve reports outside that source
head; a whitespace check alone does not certify committed inputs. Rebased/merged heads require
their own validation and current-head CI. No baseline increase is part of this plan.

## Effort, uncertainty and go/no-go

R0 plus the first framework/frontend/component pilots are the bounded estimation stage: budget
roughly 1–2 engineer-weeks for those pilots and review, then re-estimate from their actual proof
obligations and compiler behavior. This is a low-confidence planning allowance, not a validated estimate or implementation promise.
P1–P3 establish useful seams but do not price the complete rejection-aware experiment or FORS port.

Do not repeat the earlier 3–8-day forecast for the entire integration/refactor. Canonical delegation
and deep graph/numerical generalization may take multiple staged iterations; there is no reliable
estimate for rewriting 221 proof modules or unifying both probability methods from this research.
A near-total rewrite needs a separate evidence-backed proposal after P4/P5 and the first real
extractions, with exact strength retained. No line-count or default-build-speed target substitutes
for those proofs.

Proceed with gated shared-core implementation when this plan/ledger/prototype evidence passes
independent review. Continue each broad migration only when its prerequisite exact-observation
and strength gates pass. Pause that abstraction if it needs weaker bounds, stronger adversary
premises, unsupported rejection behavior or duplicated security semantics. Keep both existing
proof methods usable throughout; successful deeper reuse is the endpoint.
