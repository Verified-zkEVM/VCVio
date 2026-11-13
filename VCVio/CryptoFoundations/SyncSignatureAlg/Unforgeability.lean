/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.SyncSignatureAlg.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Synchronized-signature signing histories and unforgeability

Only the first eligible request at an epoch invokes signing. Returned failure consumes that epoch,
and strong freshness records the exact successfully returned message/signature pair.
-/

public section

namespace SyncSignatureUnforgeability

open OracleSpec OracleComp ENNReal

universe u v

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

/-- Recording an unused epoch updates exactly its first request and optional answer. -/
@[simp] theorem record_eq_update [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep = none) :
    record history ep msg answer = Function.update history ep (some (msg, answer)) := by
  unfold record
  exact ite_eq_left h

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
    {m : Type → Type v} [Monad m]
    (alg : SyncSignatureAlg m M PK SK S E) (sk : SK) :
    QueryImpl (signingSpec E M S) (StateT (History E M S) m) :=
  fun ⟨ep, msg⟩ history =>
    match history ep with
    | some _ => pure (none, history)
    | none => do
      let answer ← alg.sign sk ep msg
      pure (answer, record history ep msg answer)

/-- The signing oracle at a used epoch returns failure and the unchanged history. -/
theorem signingOracle_used [DecidableEq E]
    {m : Type → Type v} [Monad m]
    (alg : SyncSignatureAlg m M PK SK S E) (sk : SK)
    (history : History E M S) (ep : E) (msg first : M) (answer : Option S)
    (h : history ep = some (first, answer)) :
    signingOracle alg sk (ep, msg) history = pure (none, history) := by
  simp [signingOracle, h]

/-- The signing oracle at an unused epoch runs signing once and records its optional result. -/
theorem signingOracle_unused [DecidableEq E]
    {m : Type → Type v} [Monad m]
    (alg : SyncSignatureAlg m M PK SK S E) (sk : SK)
    (history : History E M S) (ep : E) (msg : M) (h : history ep = none) :
    signingOracle alg sk (ep, msg) history = (do
      let answer ← alg.sign sk ep msg
      pure (answer, Function.update history ep (some (msg, answer)))) := by
  simp [signingOracle, record, h]

/-- Every issued signing request counts, including repeated epochs and returned failures. -/
@[expose] def SigningQueryBound {ι : Type} {spec : OracleSpec ι} (qs : ℕ)
    (adv : Adversary spec PK E M S) : Prop :=
  ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs

/-- Forward ambient queries and answer signing requests with a persistent first-request history. -/
@[expose] def oracles [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK) :
    QueryImpl (spec + signingSpec E M S) (StateT (History E M S) (OracleComp spec)) :=
  (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
    (StateT (History E M S) (OracleComp spec)) + signingOracle alg sk

/-- Run an ambient/signing program from an explicit first-request history. -/
@[expose] def runWithSigningOracle [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    {A : Type} (program : OracleComp (spec + signingSpec E M S) A)
    (history : History E M S) : OracleComp spec (A × History E M S) :=
  (simulateQ (oracles alg sk) program).run history

/-- Every successful first signing record satisfies the supplied output predicate. -/
@[expose] def SuccessfulHistorySatisfies (P : E → M → S → Prop)
    (history : History E M S) : Prop :=
  ∀ ep msg sig, history ep = some (msg, some sig) → P ep msg sig

/-- An empty history has no successful records. -/
theorem successfulHistorySatisfies_empty (P : E → M → S → Prop) :
    SuccessfulHistorySatisfies P emptyHistory := by
  intro ep msg sig hentry
  simp [emptyHistory] at hentry

/-- Recording a first answer preserves every old success and adds only that answer's predicate. -/
theorem SuccessfulHistorySatisfies.record [DecidableEq E] {P : E → M → S → Prop}
    {history : History E M S} (h : SuccessfulHistorySatisfies P history)
    (ep : E) (msg : M) (answer : Option S)
    (hanswer : ∀ sig, answer = some sig → P ep msg sig) :
    SuccessfulHistorySatisfies P (SyncSignatureUnforgeability.record history ep msg answer) := by
  intro ep' msg' sig' hentry
  by_cases hfresh : history ep = none
  · rw [record_eq_update _ _ _ _ hfresh] at hentry
    by_cases heq : ep' = ep
    · subst ep'
      have hp : msg = msg' ∧ answer = some sig' := by
        simpa [Function.update] using hentry
      rcases hp with ⟨rfl, hans⟩
      exact hanswer sig' hans
    · exact h ep' msg' sig' (by simpa [Function.update, heq] using hentry)
  · rw [record_used _ _ _ _ hfresh] at hentry
    exact h ep' msg' sig' hentry

/-- The honest signing handler retains every successful-record support invariant. -/
theorem signingOracle_preserves_successfulHistorySatisfies [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    (P : E → M → S → Prop)
    (hsign : ∀ ep msg sig, some sig ∈ support (alg.sign sk ep msg) → P ep msg sig)
    (q : E × M) (history : History E M S) (hinv : SuccessfulHistorySatisfies P history)
    (out : Option S × History E M S)
    (hout : out ∈ support ((signingOracle alg sk q).run history)) :
    SuccessfulHistorySatisfies P out.2 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (signingOracle alg sk (ep, msg) history) at hout
  cases hused : history ep with
  | none =>
    rw [signingOracle_unused _ _ _ _ _ hused, mem_support_bind_iff] at hout
    obtain ⟨answer, hanswer, hreturn⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    subst out
    have hrecord := hinv.record ep msg answer (fun sig heq =>
      hsign ep msg sig (heq ▸ hanswer))
    simpa only [record_eq_update _ _ _ _ hused] using hrecord
  | some entry =>
    rw [signingOracle_used _ _ _ _ _ entry.1 entry.2 hused, support_pure,
      Set.mem_singleton_iff] at hout
    exact hout ▸ hinv

/-- Running the common handler retains predicates of all successful first signing records. -/
theorem runWithSigningOracle_preserves_successfulHistorySatisfies [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    (P : E → M → S → Prop)
    (hsign : ∀ ep msg sig, some sig ∈ support (alg.sign sk ep msg) → P ep msg sig)
    {A : Type} (program : OracleComp (spec + signingSpec E M S) A)
    (history : History E M S) (hinv : SuccessfulHistorySatisfies P history)
    (out : A × History E M S) (hout : out ∈ support
      (runWithSigningOracle alg sk program history)) : SuccessfulHistorySatisfies P out.2 := by
  apply OracleComp.simulateQ_run_preservesInv (oracles alg sk)
    (SuccessfulHistorySatisfies P) ?_ program history hinv out hout
  rintro (q | q) state hs result hresult
  · simp only [oracles, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      StateT.run_liftM, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hresult
    obtain ⟨answer, _, rfl⟩ := hresult
    exact hs
  · exact signingOracle_preserves_successfulHistorySatisfies alg sk P hsign q state hs
      result hresult

/-- Generate keys and run the adaptive adversary from empty signing history.
Ambient queries are forwarded; signing queries update the history through the signing handler.
The result remains internal to the validity check and supplies no extra oracle to the adversary. -/
@[expose] def interaction [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (adv : Adversary spec PK E M S) : OracleComp spec (ExperimentResult PK E M S) := do
  let (pk, sk) ← alg.keygen
  let (forgery, history) ← runWithSigningOracle alg sk (adv.forge pk) emptyHistory
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
The runtime map law transports the common interaction observation; no bind law is needed. -/
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
