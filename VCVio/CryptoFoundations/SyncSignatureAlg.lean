/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.OracleComp.ProbCompLift
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Defs.Measure
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Synchronized signature algorithms, correctness, and security

Epoch-indexed algorithms specialize to ePrint 2025/055, Definition 7 (page 12), with
`E := Fin L`. A concrete scheme constructor fixes its system configuration for all three
algorithms. Correctness for a family `scheme` is expressed by
`∀ cfg, (scheme cfg).Complete runtime (errorBound cfg)`. The THF parameter sampled by GXMSS
key generation remains distinct key material. Message types can be instantiated with fixed-length
bit strings. Efficiency is not modeled.

The interface assumes no equality decision, ordering or finiteness of `E`. Consumers that
compare or enumerate epochs supply those structures where needed; concrete GXMSS uses
`Fin (2 ^ h)` for tree height `h`.

Correctness observes signing in the supplied runtime, then maps `none` to `false` and a returned
signature to deterministic verification. This preserves missing mass without a normalization.
Producibility means positive native event mass in this same runtime, not structural oracle support.
The paper's total key generator additionally requires losslessness of the chosen keygen semantics;
the per-produced-key correctness predicate itself makes no keygen termination claim.

`SyncSignatureUnforgeability` defines adaptive regular and strong unforgeability experiments
and their advantages, with one eligible signing request per epoch.
-/

public section


open ENNReal

universe v

/-- Epoch-indexed signature algorithms with system configuration fixed by the scheme instance. -/
structure SyncSignatureAlg (m : Type → Type v) [Monad m] (M PK SK S E : Type) where
  /-- Generate a public and secret key for this scheme instance. -/
  keygen : m (PK × SK)
  /-- Sign at a valid epoch; a returned `none` is an explicit signing failure. -/
  sign : SK → E → M → m (Option S)
  /-- Deterministically verify a signature at the supplied epoch. -/
  verify : PK → E → M → S → Bool

namespace SyncSignatureAlg

variable {m : Type → Type v} [Monad m] {M PK SK S E : Type}

/-- The Boolean observation of signing: explicit failure is rejected. -/
@[expose] def accepts (alg : SyncSignatureAlg m M PK SK S E)
    (pk : PK) (ep : E) (msg : M) : Option S → Bool
  | none => false
  | some sig => alg.verify pk ep msg sig

/-- A returned signing failure is never accepted. -/
@[simp] theorem accepts_none (alg : SyncSignatureAlg m M PK SK S E)
    (pk : PK) (ep : E) (msg : M) : alg.accepts pk ep msg none = false := rfl

/-- Successful returned signatures are observed by deterministic verification. -/
@[simp] theorem accepts_some (alg : SyncSignatureAlg m M PK SK S E)
    (pk : PK) (ep : E) (msg : M) (sig : S) :
    alg.accepts pk ep msg (some sig) = alg.verify pk ep msg sig := rfl

/-- A key pair is producible exactly when it has positive mass in the chosen runtime. -/
@[expose] def Generated (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) : Prop :=
  0 < runtime.evalDist ((fun ks' => ks' = ks) <$> alg.keygen) {True}

/-- The unnormalized probability of successful verification for a fixed key pair. -/
@[expose] noncomputable def successMass (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) : ℝ≥0∞ :=
  runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) {true}

/-- The measure singleton agrees with the runtime's discrete successful-output probability. -/
theorem successMass_eq_probability (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg =
      runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) {true} := rfl

/-- Successful verification has subprobability mass at most one. -/
theorem successMass_le_one (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M) :
    alg.successMass runtime ks ep msg ≤ 1 := by
  rw [successMass_eq_probability]
  exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
    (runtime.evalDist_apply_univ_le_one _)

/-- A signing-and-verification observation concentrated on rejection has no success mass. -/
theorem successMass_eq_zero_of_rejection (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) =
      MeasureTheory.Measure.dirac false) :
    alg.successMass runtime ks ep msg = 0 := by
  simp [successMass, h]

/-- A signer with entirely missing output mass has no successful verification mass. -/
theorem successMass_eq_zero_of_failure (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (ks : PK × SK) (ep : E) (msg : M)
    (h : runtime.evalDist (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) = 0) :
    alg.successMass runtime ks ep msg = 0 := by
  simp [successMass, h]

/-- Correctness for every producible key pair, epoch and message of this scheme instance.
Returned failure, verification rejection and missing mass all count against `δ`. -/
@[expose] def Complete (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) : Prop :=
  ∀ ks, alg.Generated runtime ks → ∀ ep msg,
    1 - δ ≤ alg.successMass runtime ks ep msg

/-- The fully quantified per-key characterization of correctness. -/
theorem complete_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    alg.Complete runtime δ ↔ ∀ ks,
      0 < runtime.evalDist ((fun ks' => ks' = ks) <$> alg.keygen) {True} → ∀ ep msg,
      1 - δ ≤ runtime.evalDist
        (alg.accepts ks.1 ep msg <$> alg.sign ks.2 ep msg) {true} := by
  simp only [Complete, Generated, successMass_eq_probability]

/-- Increasing the permitted error preserves correctness. -/
theorem Complete.mono {alg : SyncSignatureAlg m M PK SK S E}
    {runtime : ProbCompRuntime m} {δ₁ δ₂ : ℝ≥0∞}
    (h : alg.Complete runtime δ₁) (hle : δ₁ ≤ δ₂) : alg.Complete runtime δ₂ :=
  fun ks hks ep msg => (tsub_le_tsub_left hle 1).trans (h ks hks ep msg)

/-- Zero error is exactly unit success mass at every producible key, epoch and message. -/
theorem complete_zero_iff (alg : SyncSignatureAlg m M PK SK S E)
    (runtime : ProbCompRuntime m) :
    alg.Complete runtime 0 ↔ ∀ ks, alg.Generated runtime ks → ∀ ep msg,
      alg.successMass runtime ks ep msg = 1 := by
  constructor
  · intro h ks hks ep msg
    exact le_antisymm (alg.successMass_le_one runtime ks ep msg)
      (by simpa using h ks hks ep msg)
  · intro h ks hks ep msg
    simpa using le_of_eq (h ks hks ep msg).symm

end SyncSignatureAlg

/-!
## Synchronized unforgeability and strong unforgeability

Definition 8 and Remark 2 of ePrint 2025/055 (page 12) use one eligible signing request
per epoch and exact returned-pair freshness. `History` distinguishes unused epochs from
eligible requests returning failure. The ordinary variant compares the forged message with
the first eligible message at that same epoch, including failed requests.

Both advantages check the result of the same adaptive `interaction` after runtime evaluation.
Returned signing failure is an oracle answer, so interaction continues; actual runtime
nontermination retains missing mass. No normalization, query cutoff or efficiency claim is
implicit. Security bounds quantify over an explicitly chosen adversary class at their use sites.

The ambient `spec` describes capabilities available to both the algorithms and the adversary.
Choosing `unifSpec` provides random sampling for a standard-model probabilistic interaction;
additional public oracles require their own model justification. The signing handler alone holds
the secret key. `ExperimentResult` retains the public key, forgery and first-request history;
it is sufficient for both validity checks, but is not a chronological log of all oracle queries.
-/

namespace SyncSignatureUnforgeability

open OracleSpec OracleComp ENNReal

universe u

variable {M PK SK S E : Type}

/-- The first eligible request and its optional answer at each epoch. -/
@[expose] def History (E M S : Type) := E → Option (M × Option S)

/-- A candidate forgery contains its epoch, message and signature. -/
@[expose] def Forgery (E M S : Type) := E × M × S

/-- All epochs initially have no eligible request. -/
@[expose] def emptyHistory : History E M S := fun _ => none

/-- Insert a first request without changing any already consumed epoch. -/
@[expose] def record [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) : History E M S :=
  if history ep = none then Function.update history ep (some (msg, answer)) else history

/-- A fresh epoch records the request even when its answer is failure. -/
theorem record_unused [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep = none) :
    record history ep msg answer ep = some (msg, answer) := by
  simp [record, h, Function.update]

/-- Recording at a used epoch preserves the entire first-request history. -/
theorem record_used [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep ≠ none) :
    record history ep msg answer = history := by
  simp [record, h]

/-- A request changes no other epoch. -/
theorem record_other [DecidableEq E] (history : History E M S)
    (ep other : E) (msg : M) (answer : Option S) (h : other ≠ ep) :
    record history ep msg answer other = history other := by
  by_cases hu : history ep = none
  · simp [record, hu, h, Function.update]
  · simp [record, hu]

/-- Strong freshness excludes exactly the successfully returned pair at the forged epoch. -/
@[expose] def strongFresh [DecidableEq M] [DecidableEq S]
    (history : History E M S) (forgery : Forgery E M S) : Bool :=
  let candidate := forgery.2
  decide (history forgery.1 ≠ some (candidate.1, some candidate.2))

/-- Ordinary freshness excludes the first eligible message at the forged epoch. -/
@[expose] def fresh [DecidableEq M]
    (history : History E M S) (forgery : Forgery E M S) : Bool :=
  let candidate := forgery.2
  match history forgery.1 with
  | none => true
  | some (msg, _) => decide (candidate.1 ≠ msg)

/-- Ordinary freshness implies exact returned-pair freshness, including failed records. -/
theorem strongFresh_of_fresh [DecidableEq M] [DecidableEq S]
    (history : History E M S) (forgery : Forgery E M S)
    (h : fresh history forgery = true) : strongFresh history forgery = true := by
  cases hh : history forgery.1 with
  | none => simp [strongFresh, hh]
  | some entry =>
    rcases entry with ⟨msg, answer⟩
    simp only [fresh, hh, decide_eq_true_eq] at h
    simp [strongFresh, hh, Ne.symm h]

/-- The public key, candidate forgery and final first-request history used by validity checks. -/
@[expose] def ExperimentResult (PK E M S : Type) := PK × Forgery E M S × History E M S

variable {ι : Type u} {spec : OracleSpec ι}

/-- A signing query supplies an epoch and message and returns a signature or explicit failure. -/
abbrev signingSpec (E M S : Type) : OracleSpec (E × M) :=
  (E × M) →ₒ Option S

/-- A classical adaptive EUF-CMA/SUF-CMA adversary has the ambient oracles and the optional
signing oracle. -/
structure Adversary (spec : OracleSpec ι) (PK E M S : Type) where
  /-- The program receives the public key; its scheme instance fixes public configuration. -/
  forge : PK → OracleComp (spec + signingSpec E M S) (Forgery E M S)

/-- Reject duplicate epochs without invoking signing; returned failure records and continues. -/
@[expose] def signingOracle [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK) :
    QueryImpl (signingSpec E M S) (StateT (History E M S) (OracleComp spec)) :=
  fun ⟨ep, msg⟩ history =>
    match history ep with
    | some _ => pure (none, history)
    | none => do
      let answer ← alg.sign sk ep msg
      pure (answer, Function.update history ep (some (msg, answer)))

/-- The signing oracle at a used epoch returns failure and the unchanged history. -/
theorem signingOracle_used [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    (history : History E M S) (ep : E) (msg first : M) (answer : Option S)
    (h : history ep = some (first, answer)) :
    signingOracle alg sk (ep, msg) history = pure (none, history) := by
  simp [signingOracle, h]

/-- The signing oracle at an unused epoch runs signing once and records its optional result. -/
theorem signingOracle_unused [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    (history : History E M S) (ep : E) (msg : M) (h : history ep = none) :
    signingOracle alg sk (ep, msg) history = (do
      let answer ← alg.sign sk ep msg
      pure (answer, Function.update history ep (some (msg, answer)))) := by
  simp [signingOracle, h]

/-- Generate keys and run the adaptive adversary from empty signing history.
Ambient queries are forwarded; signing queries update the history through the signing handler.
The result remains internal to the validity check and supplies no extra oracle to the adversary. -/
@[expose] def interaction [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (adv : Adversary spec PK E M S) : OracleComp spec (ExperimentResult PK E M S) := do
  let (pk, sk) ← alg.keygen
  let impl : QueryImpl (spec + signingSpec E M S)
      (StateT (History E M S) (OracleComp spec)) :=
    (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
      (StateT (History E M S) (OracleComp spec)) + signingOracle alg sk
  let (forgery, history) ← (simulateQ impl (adv.forge pk)).run emptyHistory
  pure (pk, forgery, history)

/-- A strong forgery verifies and differs from the exact pair returned at its epoch. -/
@[expose] def strongValid [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) : Bool :=
  let result := out.2
  let forgery := result.1
  let candidate := forgery.2
  alg.verify out.1 forgery.1 candidate.1 candidate.2 && strongFresh result.2 forgery

/-- A forgery verifies and uses a fresh message at its epoch. -/
@[expose] def valid [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) : Bool :=
  let result := out.2
  let forgery := result.1
  let candidate := forgery.2
  alg.verify out.1 forgery.1 candidate.1 candidate.2 && fresh result.2 forgery

/-- Every result valid for unforgeability is also valid for strong unforgeability. -/
theorem strongValid_of_valid [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) (h : valid alg out = true) :
    strongValid alg out = true := by
  simp only [valid, Bool.and_eq_true] at h
  simp [strongValid, h.1, strongFresh_of_fresh _ _ h.2]

/-- The Boolean measure obtained by checking a winning condition on the common interaction result.
Both Boolean outcomes retain their original mass; missing execution mass is not normalized. -/
@[expose] noncomputable def outputMeasure [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool) :
    MeasureTheory.Measure Bool :=
  runtime.evalDist (winCondition <$> interaction alg adv)

/-- Regular existential unforgeability (EUF-CMA) as a Boolean winning measure.
The winning observation follows runtime interpretation and retains missing execution mass. -/
@[expose] noncomputable def unforgeableExp [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    MeasureTheory.Measure Bool :=
  outputMeasure alg runtime adv (valid alg)

/-- The public experiment is exactly the post-runtime winning measure. -/
theorem unforgeableExp_eq_outputMeasure [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    unforgeableExp alg runtime adv = outputMeasure alg runtime adv (valid alg) := rfl

/-- Strong unforgeability (SUF-CMA) as a Boolean winning measure.
The winning observation follows runtime interpretation and retains missing execution mass. -/
@[expose] noncomputable def strongUnforgeableExp [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    MeasureTheory.Measure Bool :=
  outputMeasure alg runtime adv (strongValid alg)

/-- The public experiment is exactly the post-runtime winning measure. -/
theorem strongUnforgeableExp_eq_outputMeasure [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    strongUnforgeableExp alg runtime adv = outputMeasure alg runtime adv (strongValid alg) := rfl

/-- Strong unforgeability advantage preserves all missing execution mass. -/
@[expose] noncomputable def strongAdvantage [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) : ℝ≥0∞ :=
  strongUnforgeableExp alg runtime adv {true}

/-- Unforgeability advantage uses the same runtime interaction result as strong advantage. -/
@[expose] noncomputable def advantage [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) : ℝ≥0∞ :=
  unforgeableExp alg runtime adv {true}

/-- The public measure agrees with the unnormalized probability of the checked Boolean output. -/
theorem outputMeasure_apply_singleton [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool) (b : Bool) :
    outputMeasure alg runtime adv winCondition {b} =
      runtime.evalDist (winCondition <$> interaction alg adv) {b} := rfl

/-- Checking the interaction produces a subprobability measure, preserving missing mass. -/
theorem outputMeasure_mass_le_one [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool) :
    outputMeasure alg runtime adv winCondition Set.univ ≤ 1 :=
  runtime.evalDist_apply_univ_le_one _

/-- Entirely missing runtime transcript mass produces zero winning probability. -/
theorem outputMeasure_eq_zero_of_failure [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool)
    (h : runtime.evalDist (winCondition <$> interaction alg adv) = 0) :
    outputMeasure alg runtime adv winCondition {true} = 0 := by
  simp [outputMeasure, h]

/-- The output measure is the native runtime observation of the checked surface program. -/
theorem outputMeasure_eq_runtime [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool) :
    outputMeasure alg runtime adv winCondition {true} =
      runtime.evalDist (winCondition <$> interaction alg adv) {true} := rfl

/-- Unforgeability advantage is bounded by strong advantage for the same adversary and runtime.
No runtime map law is needed because both observations follow the common evaluation. -/
theorem advantage_le_strongAdvantage
    [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    advantage alg runtime adv ≤ strongAdvantage alg runtime adv := by
  simp only [advantage, strongAdvantage, unforgeableExp, strongUnforgeableExp,
    outputMeasure]
  let : MeasurableSpace (ExperimentResult PK E M S) := ⊤
  rw [runtime.evalDist_map _ Measurable.of_discrete,
    runtime.evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  exact MeasureTheory.measure_mono fun out h => strongValid_of_valid alg out h

end SyncSignatureUnforgeability
