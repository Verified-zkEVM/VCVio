# The Polynomial-Time Adversary Model: Design Audit and Decisions

Status: living design note for the draft dynamical-systems / oracle-machine / polytime
layer (`VCVio/OracleComp/Coinductive/`, `ToMathlib/Computability/`,
`VCVio/CryptoFoundations/Asymptotics/PolyTime.lean`). It records the July 2026 audit's
findings, the repairs already landed, and the open architecture decision, so the layer
can be discussed and reviewed with all modeling choices explicit.

## The model, in one paragraph

An adversary is a family of oracle machines, one per security parameter `n`
(`PolyTimeAdversary`). Semantics: the machine `Implements` a program family when its
fuelled probabilistic run equals the program's `simulateQ` distribution against *every*
probabilistic handler — a two-sided equality, so no machine can vacuously qualify.
Resources: four independent polynomial bounds shared across the family — oracle rounds
(`steps`), encoded-state length (`sizeBound`), per-step machine time (`stepTime`), and
machine description size (`descBound`). Each step function carries a concrete
single-tape Turing machine witness (`Computability.EncPolyTime`, grounded in Cslib's
proven `PolyTimeComputable`), whose `map_encode` field ties the machine to the actual
Lean function. `OracleComp.IsPolyTime oa` = some bundle implements `oa` within its
round budget, and `oa` is syntactically query-bounded by that budget. This is the
standard **non-uniform P/poly** adversary.

## The advice-collapse finding (repaired)

The audit's headline finding: before the repair, nothing bounded the *description
size* of the witness machines. Cslib's `SingleTapeTM` requires only `Fintype State`;
`PolyTimeComputable` bounds running time only; and the finite-table machine
`EncPolyTime.ofFintype` computes **any** function on a finite domain in linear time
using one state per valid input. A family of tables over `BitVec n` inputs therefore
smuggled `2^n` states of advice per parameter, and the induced "polynomial-time" class
was *all functions on polynomially-encodable domains* — e.g. the pure image tester
`fun n y => pure (decide (y ∈ Set.range (prg n).gen))` was `IsPolyTime`, distinguishing
any expanding PRG with advantage ≥ 1/2, so `PRGSecure` was unsatisfiable for every
useful PRG. No proven theorem was wrong (hardness is always a hypothesis), but no
computational hardness assumption stated in the model could ever be instantiated.

**Repair (landed, round 1)**: `EncPolyTime.size` (machine state count) with size lemmas for
every proven combinator (`size_id = 1`, `size_copy`, `size_comp` additive,
`size_const_le`, `size_ofFintype_le` — the table's size is the domain's total encoded
length), and a fifth resource bound on `PolyTimeAdversary`: `descBound` with four
`*TM_size_le` fields. All closure operations (`precomp`, `map`, `mapComp`, the
`coinFold` combinator, `isPolyTime_pure_ofFintype`) now take the cardinality/length
bounds needed to keep their new witnesses within the composed advice bound.

**Consequences (the honest cost)**: table-based certifications over superpolynomial
domains cannot survive the repair, so the following moved to explicit hypothesis form
(each states exactly the machine witnesses it awaits):

* `isPolyTime_uniformBitVec`, KL `isPolyTime_chooseProg` — coin folds into `BitVec`
  accumulators; the coalgebraic content (implements/steadiness/state-size) is still
  discharged via `isPolyTime_coinFold_of_witnesses`; only the four step-function
  machines are hypotheses.
* `isPolyTime_bitVecFun` — deleted: "every bitvector function is polytime,
  hypothesis-free" *was* the collapse; a genuine `f` needs a genuine machine
  (`isPolyTime_pure_of_witnesses`).
* KL `isPPT_reduceAdv` and Claim 3.11 (`secureAgainst_predictBitGame_of_eavSecure`) —
  the reduction's PPT is now an explicit `hred` hypothesis, matching the
  `eavSecure_prgEnc` `hppt` pattern.
* `PPTEavAdversary.isPPT_negateDistinguish` — see the encoding landmine below.

Discharging these needs a **base-machine library**: verified single-tape machines for
projections, bit overwrite, increment/compare/copy on encoded states. That is the
priority machine-engineering ticket; `XorFlips` (constant-cardinality accumulator)
remains the fully concrete, hypothesis-free end-to-end example.

## Round 2: the encoding-triviality finding and the canonicalization repair (landed)

A second audit round found the advice repair alone insufficient: the boundary encodings
remained **existential inside `IsPolyTime`**, and "poly-time relative to *some*
encoding" is vacuous — the caching trick `enc x := std x ++ block (f x)` certifies any
function using only an identity, a constant, a projection, and a block-extraction
machine. The last two were exactly the planned base-machine library, so building it
would have re-trivialized the class. The oracle-answer encoding was a second caching
channel. Complexity theory's resolution, now implemented: **canonical fixed-width
boundary encodings**.

* `Computability.BitEncFam` — fixed-width raw `List Bool` encoding families (binary
  index encoding for finite types, raw bits for `BitVec`, append for pairs, tag+pad for
  options); no alphabets, no one-hot relabeling on boundaries. The polynomial width
  bound is the formalized Katz–Lindell `1^n` convention (KL define PPT in input length
  and reconcile with poly(`n`) by the unary hack; poly-width boundaries make the two
  readings agree). `Computability.StrEncFam` — variable-width, length-bounded — is the
  machine-internal state representation freedom, harmless because every cached state
  bit is produced by a witnessed machine from canonical inputs/answers.
* `BoundaryData` (input/output/interface encodings) is a pinned explicit parameter of
  `IsPolyTime` and of every security statement; never existential, never
  adversary-chosen. Sole documented exemption: a multi-phase adversary's own
  cross-phase state encoding, shared between its phases (`PPTEavAdversary.encState`).
* The model was also re-factored for naturalness: `Computability.EncPolyTimeFam`
  (machine family + uniform time and advice polynomials — the reusable computability
  unit), `MachineAdversary bd` (the game-facing type; the old `steady` field is now a
  theorem), and the `oa`-indexed certificate `PolyTimeWitness bd oa` with
  `IsPolyTime bd oa := Nonempty (PolyTimeWitness bd oa)`, mirroring `PolyQueries`.
* What canonicalization bought immediately: the abstract output-map closure
  (`IsPolyTime.map`) is derivable again and `isPPT_negateDistinguish` is unconditional;
  `detTotalTime_le` is hypothesis-free; the alphabet-width side conditions vanished
  (mixed pairs are right-aligned appends); `bind`'s statement is finally well-formed
  (shared mid boundary).
* `unifSpec` has **no** fixed-width interface (queries range over all of `ℕ`), so
  `SchemePolyTime` is honestly parameterized-and-vacuous pending the
  `ProbComp → coinSpec` derandomization bridge — the textbook's algorithms run on a
  random bit tape, which is the coin oracle.
* **Non-triviality certificates** (`VCVio/OracleComp/Coinductive/PolyTimeNontrivial.lean`,
  documented sorries): a `steps = 0` sentinel and the full
  `∃ f, ¬ IsPolyTime bd (pure ∘ f)`. Both were *false* before canonicalization;
  provability is the repair's acceptance semantics. Proof staging: run factorization
  at a fixed handler (the "compiled run", also the model's soundness story) → machine
  counting/normalization → elementary growth bounds → diagonalization.

Sharpened CertiCrypt/EasyCrypt comparison: syntactic systems never had the encoding
hole because a fixed programming language fixes the value representation *implicitly*;
by grounding in machines VCVio gave that up and has now recovered it explicitly —
canonical encodings play precisely the role of pWhile's built-in value representation,
while keeping the proven (not axiomatized) per-operation costs.

## The boundary-encoding landmine (historical; repaired by round 2)

`IsPolyTime` is existential, and the bundle's encodings are part of the existential
data. Composition across a bundle boundary must read values in the *given* bundle's
encoding, but no field bounds those encoding lengths, and a polynomial-time translator
between two arbitrary injective encodings need not exist. Concretely:

* The abstract output-map closure (`IsPolyTime.map`, previously certified via a table
  over the existential `encOut`) is **not certifiable** in the advice-bounded model and
  was removed. The concrete-bundle forms (`map_of_adversary`, `mapComp` with a supplied
  sized witness) remain.
* The naive statement of sequential composition — `IsPolyTime oa → IsPolyTime ob →
  IsPolyTime (bind)` over two bare existentials — is *false as stated* for the same
  reason (`D₁.encOut` vs `D₂.encIn` are unrelated encodings).

The fix, in any architecture: pin the *boundary* encodings (I/O and interface) of
`IsPolyTime` to canonical ones, keeping state encodings existential. This is tracked
together with the `bind` closure.

## Status of `IsPolyTime.bind` (the composition wall)

Sequential composition is the one closure every nontrivial reduction needs
(`eavSecure_prgEnc`'s `hppt`, ElGamal-style reductions). Machine-level scoping:

* Composite machine `seqComp` with state `σ₁ ⊕ σ₂` and eager handoff; `stable`/
  `steady`/`encState` (via `finEncodingSum`) are routine; the `Implements`-splitting
  needs a `runK` fuel-monotonicity lemma via path-steadiness (no TM content).
* The TM witnesses are the hard part. Two discoveries change the economics:
  **fused witnesses** (`initOutTM`/`updateOutTM` computing `(output s', s')` as one
  function) remove the fanout obstruction entirely; and re-cutting the deferred
  `EncPolyTime.sumElim` against a `Γ = Bool` wrapping convention replaces the
  length-changing one-hot transducer with a small reusable Bool-machine toolkit
  (shift, dispatch, fixed-width recode). The two `sumElim` sorries in
  `ToMathlib/Computability/PolyTimeTM.lean` should be retired by interface
  replacement, not proven as typed.

## The open architecture decision (deferred to discussion)

Two candidate shapes for how users touch polynomial time:

1. **Two-level**: an inductive, structural judgment (`pure`-leaf with sized-witness
   side condition / `query` / context-threading `bind` / `map` / bounded fold),
   compositional by construction, as the `isPPT` slot of security statements; the
   machine model becomes the soundness target behind it, with the unproven bind case a
   single named `Prop` until the machine bind lands. Query-polynomiality of the
   structural class is unconditional on day one. Precedent: CertiCrypt/EasyCrypt/FCF
   all use structural cost judgments — but with axiomatized or trusted per-operation
   costs, whereas here the soundness theorem would be genuinely proven (staged).
   Statements become invariant under machine-model refinements.
2. **Single-level**: keep the existential `IsPolyTime` as the only notion and build
   the machine bind directly (SeqComp + fused witnesses + Bool toolkit). No second
   class to maintain; every future closure property is machine surgery, and statements
   stay coupled to the model during repairs.

Interim (current state): security theorems that need undischargeable closures take
them as explicit named hypotheses (`hppt`, `hred`, `hmap`) with docstrings stating
exactly what is awaited. This is the honest fallback either architecture replaces.

## What the polynomial data is for (reviewer FAQ)

* The `steps` polynomial and query-bound conjunct are consumed by
  `SecurityGame.secureAgainstPolyTime_of_advantage_le_mul_totalQueries` (per-query
  loss × polynomial rounds = negligible) and the `PolyQueries` bridge.
* `stepTime`/`sizeBound` are consumed by the total-run-time bound `detTotalTime_le`
  (polynomial total TM time against answer-bounded handlers). A compiled single-TM
  witness for a whole run is explicitly out of scope (needs machine iteration on top
  of Cslib composition).
* The query-bound conjunct of `IsPolyTime` is definitional, conjectured redundant;
  the extraction from `Implements` is genuinely hard (a counting handler is
  structurally impossible — `SPMF` has no writer; the scaled-handler
  polynomial-degree route needs power-series coefficient extraction over `ℝ≥0∞`).
  See the `IsPolyTime` docstring.
* The `steady` field quantifies over deterministic handlers deliberately: it is the
  clock for deterministic cost accounting, and both deterministic and probabilistic
  resolution are *theorems* for implementing bundles
  (`OracleMachine.Implements.steadyBy`, `Implements.runK_none_eq_zero`).

## Related resource disciplines

The library has three: query bounds (`QueryTracking/QueryBound.lean` — structural
counting, canonical for hybrid arguments), weighted query cost
(`QueryTracking/CostModel.lean` + the ElGamal `withCost` bundles — concrete-security
accounting of oracle calls, never local computation), and the TM-grounded
`IsPolyTime` (the canonical asymptotic PPT predicate, the only one pricing local
computation). They meet at the abstract `isPPT` slot of `SecurityGame.secureAgainst`;
unifying them is deliberately not attempted. Bridges: `IsPolyTime.polyQueries`
(TM → query bounds), `IsPerIndexQueryBound ↔ WorstCaseCostBound` (query ↔ cost);
cost → TM is intentionally impossible.

## Round 3: limit semantics and coalgebraic games (landed, in progress)

Round 3 de-risks the two remaining modeling questions: what the semantics of a machine
that may not terminate is, and whether challengers should themselves be coalgebraic
systems.

**Limit semantics is a semantic enrichment, not a class change.** `SPMF` now carries
the pointwise subprobability order with `failure` at the bottom and an ω-complete
partial order structure (`ToMathlib/ProbabilityTheory/SPMFOrder.lean`; chains only —
binary joins can overflow total mass, so it is deliberately not a lattice). The
fuelled run `runK` is *not* monotone in fuel (exhaustion mass sits on the value
`none`); its monotone presentation is `runKT := joinOption ∘ runK`
(`Coinductive/RunLimit.lean`), whose chain supremum `runLimit` satisfies the fixpoint
equation `runLimit_fix` — the "run forever" semantics, divergence as missing mass.
Crucially, **this adds no new soundness surface to the adversary class**:
`IsPolyTime` still demands a fuelled `Implements` witness plus query bounds, so a
machine that terminates almost surely but slowly is expressible semantically yet
still not PPT. The new relations are honest about the gap: `ImplementsAE` (limit
agreement; implied by fuelled `Implements`, converse requires explicit probabilistic
steadiness) and `ImplementsWithin oa k ε` (truncated run within `ε` of the program in
extended TV distance — the strict-PPT-with-statistical-budget form the KL-accurate
`unifSpec → coinSpec` rejection-sampling bridge produces; since truncations sit below
the limit, `ε` is exactly a difference of missing masses,
`SPMF.etvDist_eq_gap_sub_of_le`). Fuel irrelevance
(`runK_eq_of_apply_none_eq_zero`) lives in `RunLimit.lean` as the single home of the
run-extension lemma that `bind`/SeqComp and run-factorization will consume. The
truncated rejection sampler itself lives in `Coinductive/RejectionSampler.lean`: the
limit run against the fair coin is **exactly** `𝒟[$ᵗ Fin (t+1)]`
(`runLimit_rejectionMachine` — the machine terminates almost surely), while the
truncated run at strict fuel `(rejWidth t + 1) * (k + 1)` is within `2⁻⁽ᵏ⁺¹⁾` of it
(`etvDist_runKT_rejectionMachine_le`, via the per-attempt rejection rate `≤ 1/2` from
`Nat.size` minimality). The module is explicit that the unbounded sampler is *not*
polynomial time and that no expected-time ("Las Vegas") claim is made: exact
uniformity is a statement about the semantic limit only, and only the truncated
machine with its statistical budget enters PPT statements. Its `PolyTimeWitness`
integration (state cardinality `(w+1)·2^w` is polynomial in the sampled bound, so
the existing finite tables discharge the step witnesses) is the
`ApproxPolyTimeWitness` stage, scheduled after the games package's index-family
generalization.

**Games: data at Tier 1, systems at Tier 2.** Tier 1 keeps games as data on the
`SecurityGame` hub, with a per-run-sampled memoryless oracle (gen → setup × handler)
covering KL §3.5 CPA exactly — fresh encryption randomness per query means the oracle
is memoryless *given* the sampled `(k, b)`. Tier 2 makes the challenger a system:
`ProbResponder` (`Coinductive/WireK.lean`) is a Mealy coalgebra in the Kleisli
category of `SPMF` — per query, a *joint* draw of answer and successor state (a lazy
random oracle must store the very answer it returned). Wiring an adversary strategy
against one (`wireKStep`/`wireKIterate`/`wireKTranscript`) yields a Markov chain on
the product state space; constant-state responders collapse to the existing
memoryless `kleisliStep`/`kleisliIterate` runs, so the Tier-1 sampled-oracle games
embed. Stateful challengers enter via `ofQueryImpl`/`ofStateQueryImpl` — the lazy
`randomOracleResponder` and the cached asymmetric IND-CPA LR oracle
(`AsymmEncAlg.IND_CPA_challengeResponder`) are the instances. Categorically
(Spivak–Niu §4.5, §7.1.5, §8.1): deterministic responders are systems over the
internal hom `[p, y]` whose positions are exactly `OracleHandler`; `runK` is the
probabilistic shadow of the finite-run truncation and `runLimit` of the cofree limit.
Wired runs of *machine* adversaries (`runKWired`) are a deliberate ROM-driven
follow-on, as is an ITree → SPMF interpreter (trigger: first consumer needing a
program-level unbounded loop).

## Roadmap

1. Games package: `ι`-family generalization of the polytime layer, encoding-registry
   sums, the sampled-oracle `OracleGame` former, symmetric IND-CPA + PRF games, and
   the KL §3.5 landing. Then `ApproxPolyTimeWitness` (strict fuel + negligible
   statistical budget), consuming the rejection sampler's truncation bound — the
   honest fix for the vacuous `SchemePolyTime`.
2. Base-machine library (projections, bit ops, copy) → discharge the hypothesis-form
   witnesses (`uniformBitVec`, KL sampler, `isPPT_reduceAdv`).
3. Canonical boundary encodings + SeqComp semantics + Bool toolkit → `bind` →
   delete `hppt`/`hred`; unblocks ElGamal-style asymptotic corollaries. SeqComp
   consumes `runK_eq_of_apply_none_eq_zero` from `RunLimit.lean`.
4. Architecture decision (two-level vs single-level) — this note is the discussion
   artifact.
5. Usability layer (encoding-family bundles, coinFold parameter record, statement
   conventions) — planned separately; survives all of the above.
