/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import PolyFun.Control.Monad.Hom
public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.QueryTracking.CachingOracle
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Signature Algorithms

This file defines `SignatureAlg m M PK SK S`, a type representing a digital signature scheme
with computations in the monad `m`, message space `M`, public/secret key spaces `PK`/`SK`,
and signature space `S`.

## Main definitions

* `SignatureAlg`: a signature scheme as a `keygen`/`sign`/`verify` triple in a monad `m`.
* `SignatureAlg.runWithSigningOracle`: runs an adversary with its ambient oracles forwarded and a
  logged signing oracle.
* `SignatureAlg.Complete`: completeness up to an error `δ`, with `PerfectlyComplete` the `δ = 0`
  case.
* `SignatureAlg.unforgeableExperiment`, `strongUnforgeableExperiment`, `eufNmaExperiment`,
  `managedRoNmaExperiment`: the EUF-CMA, SUF-CMA, EUF-NMA, and managed-random-oracle NMA security
  experiments, with the corresponding adversary advantages.
-/

@[expose] public section

universe u v

open MeasureTheory OracleSpec OracleComp ENNReal

/-- Signature algorithm with computations in the monad `m`,
where `M` is the space of messages, `PK`/`SK` are the spaces of the public/private keys,
and `S` is the type of the final signature. -/
@[ext]
structure SignatureAlg (m : Type → Type v) [Monad m] (M PK SK S : Type) where
  keygen : m (PK × SK)
  sign (pk : PK) (sk : SK) (msg : M) : m S
  verify (pk : PK) (msg : M) (σ : S) : m Bool

namespace SignatureAlg

section signingOracle

variable {m : Type → Type v} [Monad m] {M PK SK S : Type}

/-- The signing oracle for `sigAlg` under public key `pk` and secret key `sk`: the
`QueryImpl` that answers each queried message by running `sigAlg.sign pk sk` on it.

Every successful response is recorded as its exact `(message, signature)` pair in a
`WriterT (QueryLog (M →ₒ S))` writer layer. EUF-CMA projects this trace to queried messages;
SUF-CMA checks whether the exact final pair occurs in it. -/
def signingOracle (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) :
    QueryImpl (M →ₒ S) (WriterT (QueryLog (M →ₒ S)) m) :=
  QueryImpl.withLogging (sigAlg.sign pk sk)

end signingOracle

section runWithSigningOracle

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- Run `oa` against the scheme's ambient oracles `spec` and a signing oracle for `sigAlg` under
the key pair `(pk, sk)`. Ambient queries are forwarded unchanged and signing queries are answered
by `sigAlg.signingOracle pk sk`. The result pairs the output of `oa` with the log of every
`(message, signature)` pair the signing oracle returned. -/
def runWithSigningOracle (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) (pk : PK) (sk : SK)
    {α : Type} (oa : OracleComp (spec + (M →ₒ S)) α) :
    OracleComp spec (α × QueryLog (M →ₒ S)) :=
  (simulateQ (spec.passthrough + sigAlg.signingOracle pk sk) oa).run

lemma runWithSigningOracle_def (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) (pk : PK)
    (sk : SK) {α : Type} (oa : OracleComp (spec + (M →ₒ S)) α) :
    sigAlg.runWithSigningOracle pk sk oa =
      (simulateQ (spec.passthrough + sigAlg.signingOracle pk sk) oa).run := rfl

end runWithSigningOracle

section map

variable {m : Type → Type v} [Monad m] {n : Type → Type u} [Monad n]
  {M PK SK S : Type}

/-- Transport a signature scheme across a monad morphism by mapping each algorithmic component.

This is the basic reindexing operation used by naturality theorems for generic constructions:
if a signature scheme was defined in a source monad `m`, then any monad morphism `m →ᵐ n`
induces the corresponding scheme in `n`. -/
def map (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) : SignatureAlg n M PK SK S where
  keygen := F sigAlg.keygen
  sign pk sk msg := F (sigAlg.sign pk sk msg)
  verify pk msg σ := F (sigAlg.verify pk msg σ)

@[simp]
lemma map_keygen (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) :
    (sigAlg.map F).keygen = F sigAlg.keygen := rfl

@[simp]
lemma map_sign (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (sk : SK) (msg : M) :
    (sigAlg.map F).sign pk sk msg = F (sigAlg.sign pk sk msg) := rfl

@[simp]
lemma map_verify (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) (pk : PK) (msg : M) (σ : S) :
    (sigAlg.map F).verify pk msg σ = F (sigAlg.verify pk msg σ) := rfl

/-- Mapping a signature scheme maps its complete keygen-sign-verify computation. -/
lemma map_correctnessGame (F : m →ᵐ n) (sigAlg : SignatureAlg m M PK SK S) (msg : M) :
    (do
      let (pk, sk) ← (sigAlg.map F).keygen
      let σ ← (sigAlg.map F).sign pk sk msg
      (sigAlg.map F).verify pk msg σ) =
      F (do
        let (pk, sk) ← sigAlg.keygen
        let σ ← sigAlg.sign pk sk msg
        sigAlg.verify pk msg σ) := by
  simp

end map

section correctness

variable {m : Type → Type v} [Monad m] {M PK SK S : Type}

/-- Completeness of a signature scheme with error `δ`: for every message, the canonical
keygen-sign-verify execution accepts with probability at least `1 - δ`.

The error `δ` captures all sources of failure, including both verification mismatches and
signing failures (e.g., abort in schemes like Fiat-Shamir with aborts).

`Complete sigAlg runtime 0` is equivalent to `PerfectlyComplete sigAlg runtime`. -/
def Complete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ msg : M, (1 : ℝ≥0∞) - δ ≤ runtime.evalDist (do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig) {true}

/-- Perfect completeness: the canonical keygen-sign-verify execution always accepts.
This is the special case of `Complete` with zero error. -/
def PerfectlyComplete (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, runtime.evalDist (do
    let (pk, sk) ← sigAlg.keygen
    let sig ← sigAlg.sign pk sk msg
    sigAlg.verify pk msg sig) {true} = 1

lemma perfectlyComplete_iff_complete_zero (sigAlg : SignatureAlg m M PK SK S)
    (runtime : ProbCompRuntime m) :
    sigAlg.PerfectlyComplete runtime ↔ sigAlg.Complete runtime 0 := by
  simp only [PerfectlyComplete, Complete, tsub_zero]
  constructor
  · intro h msg
    exact (h msg).ge
  · intro h msg
    exact le_antisymm (MeasureTheory.measure_le_one _ _) (h msg)

lemma Complete.mono {sigAlg : SignatureAlg m M PK SK S} {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : sigAlg.Complete runtime δ₁) (hle : δ₁ ≤ δ₂) : sigAlg.Complete runtime δ₂ :=
  fun msg => (tsub_le_tsub_left hle _).trans (h msg)

end correctness

section unforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EUF-CMA (existential unforgeability under chosen-message attack) adversary for
`sigAlg`. Given the public key, it runs in the oracle family `spec + (M →ₒ S)` — the
scheme's ambient oracles together with a signing oracle — and outputs a candidate forgery
`(message, signature)`.

The `_sigAlg` parameter indexes the adversary by a specific scheme's types but is not stored. -/
structure UnforgeableAdversary (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  /-- Given the public key, output a candidate forgery using the ambient oracles and the
  signing oracle. -/
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (M × S)

open scoped Classical in
/-- Unforgeability experiment for a signature algorithm: runs the adversary and checks whether
the adversary successfully forged a signature. The ambient oracle family is forwarded unchanged,
the signing oracle is logged, and the final check requires both signature validity and that the
forged message was never submitted to the signing oracle. -/
noncomputable def unforgeableExperiment {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((msg, σ), log) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← sigAlg.verify pk msg σ
  return !log.wasQueried msg && verified

/-- The success probability of a CMA adversary in the unforgeability experiment. -/
noncomputable def unforgeableAdvantage {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (unforgeableExperiment adv) {true}

/-- The CMA experiment with the freshness check dropped: the same body as `unforgeableExperiment`
but the final return is just the `verified` bit, ignoring whether the forged message was
queried by the adversary to the signing oracle.

Without the freshness check, an adversary trivially wins by replaying any received
signature; the bound `unforgeableAdvantage runtime adv ≤ Pr[unforgeableNoFreshExperiment ⇒ true]`
(see `unforgeableAdvantage_le_unforgeableNoFreshExperiment`) is the first game-hop in standard
CMA-to-NMA reductions. -/
noncomputable def unforgeableNoFreshExperiment
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((msg, σ), _) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
  sigAlg.verify pk msg σ

open scoped Classical in
/-- **Phase B (freshness-drop) bound.** The CMA advantage is bounded above by the success
probability of the same experiment with the freshness check dropped.

Both experiments factor through a shared prefix `joint`. The runtime map law pushes their final
Boolean projections into ordinary measurable-image events. -/
lemma unforgeableAdvantage_le_unforgeableNoFreshExperiment
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary sigAlg) :
    unforgeableAdvantage runtime adv ≤
      runtime.evalDist (unforgeableNoFreshExperiment adv) {true} := by
  let : MeasurableSpace (M × QueryLog (M →ₒ S) × Bool) := ⊤
  let joint : OracleComp spec (M × QueryLog (M →ₒ S) × Bool) := do
    let (pk, sk) ← sigAlg.keygen
    let ((msg, σ), log) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
    let verified ← sigAlg.verify pk msg σ
    pure (msg, log, verified)
  let success : M × QueryLog (M →ₒ S) × Bool → Bool :=
    fun t => !t.2.1.wasQueried t.1 && t.2.2
  let verified : M × QueryLog (M →ₒ S) × Bool → Bool := fun t => t.2.2
  have hsuccess : Measurable success := Measurable.of_discrete
  have hverified : Measurable verified := Measurable.of_discrete
  have hExp :
      runtime.evalDist (unforgeableExperiment adv) = (runtime.evalDist joint).map success := by
    rw [unforgeableExperiment, ← runtime.evalDist_bind_pure joint success hsuccess]
    congr 1
    simp only [success, joint, monad_norm]
  have hNoFresh : runtime.evalDist (unforgeableNoFreshExperiment adv) =
      (runtime.evalDist joint).map verified := by
    rw [unforgeableNoFreshExperiment, ← runtime.evalDist_bind_pure joint verified hverified]
    congr 1
    simp only [verified, joint, monad_norm]
  rw [unforgeableAdvantage, hExp, hNoFresh,
    Measure.map_apply hsuccess (measurableSet_singleton true),
    Measure.map_apply hverified (measurableSet_singleton true)]
  apply measure_mono
  intro t ht
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, success, verified] using
    Bool.and_elim_right ht

end unforgeable

section strongUnforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

section signingLogContains

variable [DecidableEq M] [DecidableEq S]

/-- Whether the signing-oracle trace contains the exact returned pair `(msg, σ)`. Unlike
`QueryLog.wasQueried`, this predicate distinguishes two signatures returned for the same message. -/
def signingLogContains (log : QueryLog (M →ₒ S)) (msg : M) (σ : S) : Bool :=
  decide (⟨msg, σ⟩ ∈ log)

@[simp]
lemma signingLogContains_nil (msg : M) (σ : S) :
    signingLogContains ([] : QueryLog (M →ₒ S)) msg σ = false := by
  simp [signingLogContains]

@[simp]
lemma signingLogContains_singleton_self (msg : M) (σ : S) :
    signingLogContains ([⟨msg, σ⟩] : QueryLog (M →ₒ S)) msg σ = true := by
  simp [signingLogContains]

/-- Exact returned-pair membership implies ordinary message membership in the same signing log. -/
lemma wasQueried_eq_true_of_signingLogContains_eq_true
    (log : QueryLog (M →ₒ S)) (msg : M) (σ : S)
    (h : signingLogContains log msg σ = true) : log.wasQueried msg = true := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq]
  rw [signingLogContains, decide_eq_true_eq] at h
  exact List.mem_map.mpr ⟨⟨msg, σ⟩, h, rfl⟩

end signingLogContains

/-- A SUF-CMA (strong unforgeability under chosen-message attack) adversary. As in EUF-CMA it
receives the public key and has access to the scheme's ambient oracles plus the signing oracle,
but its final pair is fresh when that exact `(message, signature)` pair was never returned. -/
structure StrongUnforgeableAdversary (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  /-- Given the public key, output a candidate forgery using the ambient oracles and the
  signing oracle. -/
  main (pk : PK) : OracleComp (spec + (M →ₒ S)) (M × S)

open scoped Classical in
/-- Strong unforgeability under chosen-message attack. The signing oracle logs every successful
returned `(message, signature)` pair. The adversary succeeds exactly when its final pair verifies
and that pair does not occur in the returned-pair log. -/
noncomputable def strongUnforgeableExperiment
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : StrongUnforgeableAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((msg, σ), log) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← sigAlg.verify pk msg σ
  return !signingLogContains log msg σ && verified

/-- The SUF-CMA success probability: the probability of outputting a valid pair not previously
returned by the signing oracle. -/
noncomputable def strongUnforgeableAdvantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : StrongUnforgeableAdversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (strongUnforgeableExperiment adv) {true}

/-- Forget pair freshness and regard a strong-unforgeability adversary as an ordinary
EUF-CMA adversary.  The oracle interface and adversary program are unchanged. -/
def StrongUnforgeableAdversary.toUnforgeableAdversary
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : StrongUnforgeableAdversary sigAlg) : UnforgeableAdversary sigAlg where
  main := adv.main

open scoped Classical in
/-- The extra event separating SUF-CMA from EUF-CMA: the adversary returns a valid, new signature
for a message that it did submit to the signing oracle. This event is intentionally defined
without assigning it to a cryptographic assumption; doing so is scheme-specific (for example, it
may require signature binding or a rerandomization argument). -/
noncomputable def sameMessageStrongUnforgeableExperiment
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : StrongUnforgeableAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, sk) ← sigAlg.keygen
  let ((msg, σ), log) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← sigAlg.verify pk msg σ
  return log.wasQueried msg && !signingLogContains log msg σ && verified

/-- Probability of the same-message, new-signature event in the strong-unforgeability
experiment. -/
noncomputable def sameMessageStrongUnforgeableAdvantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : StrongUnforgeableAdversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (sameMessageStrongUnforgeableExperiment adv) {true}

/-- Quantitative scheme property needed in addition to EUF-CMA for strong unforgeability: every
adversary has at most `ε` probability of returning a new valid signature for a message previously
submitted to the signing oracle.

This quantifies over *all* adversaries with no query or time bound, so it is an
information-theoretic property. It is satisfiable with small `ε` only for schemes whose valid
signatures are (statistically close to) unique per message, such as unique-signature schemes.
For schemes where an unbounded adversary can find a second valid signature — hash-based schemes
like SLH-DSA included — no `ε < 1` can hold, and quantitative results should instead consume the
per-adversary partition `strongUnforgeableAdvantage_eq_euf_add_sameMessage` directly,
bounding the same-message term for the specific reduction adversary at hand. -/
def SameMessageBinding (sigAlg : SignatureAlg (OracleComp spec) M PK SK S)
    (runtime : ProbCompRuntime (OracleComp spec)) (ε : ℝ≥0∞) : Prop :=
  ∀ adv : StrongUnforgeableAdversary sigAlg,
    sameMessageStrongUnforgeableAdvantage runtime adv ≤ ε

open scoped Classical in
/-- **Exact generic SUF-to-EUF partition.** Every strong forgery either uses a message never queried
to the signing oracle (an ordinary EUF-CMA forgery) or is a new valid signature for a previously
queried message. These events are disjoint and exhaustive inside the exact-pair-fresh success
event, so SUF-CMA equals EUF-CMA plus precisely the latter, scheme-specific same-message event.

The proof uses the runtime's measure map law and partitions the shared execution measure into two
disjoint measurable events. -/
lemma strongUnforgeableAdvantage_eq_euf_add_sameMessage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : StrongUnforgeableAdversary sigAlg) :
    strongUnforgeableAdvantage runtime adv =
      unforgeableAdvantage runtime adv.toUnforgeableAdversary +
        sameMessageStrongUnforgeableAdvantage runtime adv := by
  let : MeasurableSpace (M × S × QueryLog (M →ₒ S) × Bool) := ⊤
  let joint : OracleComp spec (M × S × QueryLog (M →ₒ S) × Bool) := do
    let (pk, sk) ← sigAlg.keygen
    let ((msg, σ), log) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
    let verified ← sigAlg.verify pk msg σ
    pure (msg, σ, log, verified)
  let suf : M × S × QueryLog (M →ₒ S) × Bool → Bool := fun t =>
    !signingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2
  let euf : M × S × QueryLog (M →ₒ S) × Bool → Bool := fun t =>
    !t.2.2.1.wasQueried t.1 && t.2.2.2
  let same : M × S × QueryLog (M →ₒ S) × Bool → Bool := fun t =>
    t.2.2.1.wasQueried t.1 && !signingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2
  have hsuf : Measurable suf := Measurable.of_discrete
  have heuf : Measurable euf := Measurable.of_discrete
  have hsame : Measurable same := Measurable.of_discrete
  have hSuf :
      runtime.evalDist (strongUnforgeableExperiment adv) = (runtime.evalDist joint).map suf := by
    rw [← runtime.evalDist_bind_pure joint suf hsuf]
    congr 1
    simp only [strongUnforgeableExperiment, suf, joint, monad_norm]
  have hEuf : runtime.evalDist (unforgeableExperiment adv.toUnforgeableAdversary) =
      (runtime.evalDist joint).map euf := by
    rw [← runtime.evalDist_bind_pure joint euf heuf]
    congr 1
    simp only [unforgeableExperiment, euf, StrongUnforgeableAdversary.toUnforgeableAdversary,
      joint, monad_norm]
  have hSame : runtime.evalDist (sameMessageStrongUnforgeableExperiment adv) =
      (runtime.evalDist joint).map same := by
    rw [← runtime.evalDist_bind_pure joint same hsame]
    congr 1
    simp only [sameMessageStrongUnforgeableExperiment, same, joint, monad_norm]
  rw [strongUnforgeableAdvantage, unforgeableAdvantage,
    sameMessageStrongUnforgeableAdvantage, hSuf, hEuf, hSame,
    Measure.map_apply hsuf (measurableSet_singleton true),
    Measure.map_apply heuf (measurableSet_singleton true),
    Measure.map_apply hsame (measurableSet_singleton true)]
  have hpartition : suf ⁻¹' {true} = euf ⁻¹' {true} ∪ same ⁻¹' {true} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union]
    by_cases hm : t.2.2.1.wasQueried t.1 = true
    · cases hp : signingLogContains t.2.2.1 t.1 t.2.1 <;>
        cases hv : t.2.2.2 <;> simp [suf, euf, same, hm, hp, hv]
    · cases hp : signingLogContains t.2.2.1 t.1 t.2.1
      · cases hv : t.2.2.2 <;> simp [suf, euf, same, hm, hp, hv]
      · exact (hm (wasQueried_eq_true_of_signingLogContains_eq_true
          t.2.2.1 t.1 t.2.1 hp)).elim
  have hdisjoint : Disjoint (euf ⁻¹' {true}) (same ⁻¹' {true}) := by
    rw [Set.disjoint_left]
    intro t he ht
    simp only [Set.mem_preimage, Set.mem_singleton_iff, euf, same] at he ht
    have hnot := Bool.and_elim_left he
    have hyes := Bool.and_elim_left (Bool.and_elim_left ht)
    simp [hyes] at hnot
  rw [hpartition, measure_union hdisjoint MeasurableSet.of_discrete]

/-- Convenient inequality corollary of the exact SUF-to-EUF partition. -/
lemma strongUnforgeableAdvantage_le_euf_add_sameMessage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : StrongUnforgeableAdversary sigAlg) :
    strongUnforgeableAdvantage runtime adv ≤
      unforgeableAdvantage runtime adv.toUnforgeableAdversary +
        sameMessageStrongUnforgeableAdvantage runtime adv :=
  (strongUnforgeableAdvantage_eq_euf_add_sameMessage runtime adv).le

/-- SUF-CMA from EUF-CMA plus a quantitative same-message binding property. -/
lemma strongUnforgeableAdvantage_le_euf_add_of_sameMessageBinding
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    {ε : ℝ≥0∞} (hbinding : sigAlg.SameMessageBinding runtime ε)
    (adv : StrongUnforgeableAdversary sigAlg) :
    strongUnforgeableAdvantage runtime adv ≤
      unforgeableAdvantage runtime adv.toUnforgeableAdversary + ε := by
  rw [strongUnforgeableAdvantage_eq_euf_add_sameMessage runtime adv]
  exact add_le_add le_rfl (hbinding adv)

end strongUnforgeable

section eufNma

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EUF-NMA (existential unforgeability under no-message attack) adversary for a
signature scheme. Unlike a CMA adversary (`UnforgeableAdversary`), the NMA adversary has NO
access to a signing oracle — it must forge a signature having only seen the public key.

In the random oracle model, the adversary still has access to the scheme's oracle spec
(e.g., the random oracle `H`), but never sees any legitimately generated signatures. -/
structure EufNmaAdversary (_sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  /-- Given the public key, output a candidate forgery using only the ambient oracles. -/
  main (pk : PK) : OracleComp spec (M × S)

/-- The EUF-NMA experiment: generate a key pair, give the public key to the adversary
(with no signing oracle), and check whether the adversary produced a valid forgery. -/
noncomputable def eufNmaExperiment {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : EufNmaAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, _) ← sigAlg.keygen
  let (msg, σ) ← adv.main pk
  sigAlg.verify pk msg σ

/-- The success probability of an EUF-NMA adversary. -/
noncomputable def eufNmaAdvantage {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : EufNmaAdversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (eufNmaExperiment adv) {true}

end eufNma

section managedRoNma

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {M PK SK S : Type}

/-- An EUF-NMA adversary with managed random oracle: the adversary returns a `QueryCache`
alongside its forgery. The experiment verifies using `withCacheOverlay`, which resolves
cached entries from the adversary's table and forwards misses to the real oracle.

This supports compositional CMA-to-NMA reductions: the CMA-to-NMA reduction programs
hash entries for signing simulation into the cache, while forwarding the inner adversary's
hash queries to the external oracle. The forking lemma (`Fork.fork`) can then replay the
external oracle queries via seeded simulation, while the programmed entries are preserved
deterministically. -/
structure ManagedRoNmaAdversary (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) where
  /-- Given the public key, output a candidate forgery together with the cache of programmed
  random-oracle entries. -/
  main (pk : PK) : OracleComp spec ((M × S) × spec.QueryCache)

/-- The managed-RO NMA experiment: generate a key pair, run the adversary to get a forgery
and a `QueryCache`, then verify the forgery through `withCacheOverlay` so that programmed
entries take priority over the real oracle. -/
noncomputable def managedRoNmaExperiment {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : ManagedRoNmaAdversary sigAlg) : OracleComp spec Bool := do
  let (pk, _) ← sigAlg.keygen
  let ((msg, σ), cache) ← adv.main pk
  withCacheOverlay cache (sigAlg.verify pk msg σ)

/-- The success probability of a managed-RO NMA adversary. -/
noncomputable def managedRoNmaAdvantage {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : ManagedRoNmaAdversary sigAlg) : ℝ≥0∞ :=
  runtime.evalDist (managedRoNmaExperiment adv) {true}

/-- Embed a standard NMA adversary as a managed-RO NMA adversary with an empty cache.
The empty cache means all queries fall through to the real oracle, recovering the
standard NMA experiment. -/
def EufNmaAdversary.toManagedRoNmaAdversary {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (adv : EufNmaAdversary sigAlg) : ManagedRoNmaAdversary sigAlg where
  main pk := (·, ∅) <$> adv.main pk

end managedRoNma

end SignatureAlg
