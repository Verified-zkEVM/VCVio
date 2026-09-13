/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Synchronized unforgeability and strong unforgeability

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

public section

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
  decide (history forgery.1 ≠ some (forgery.2.1, some forgery.2.2))

/-- Ordinary freshness excludes the first eligible message at the forged epoch. -/
@[expose] def fresh [DecidableEq M]
    (history : History E M S) (forgery : Forgery E M S) : Bool :=
  match history forgery.1 with
  | none => true
  | some (msg, _) => decide (forgery.2.1 ≠ msg)

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
  alg.verify out.1 out.2.1.1 out.2.1.2.1 out.2.1.2.2 && strongFresh out.2.2 out.2.1

/-- A forgery verifies and uses a fresh message at its epoch. -/
@[expose] def valid [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) : Bool :=
  alg.verify out.1 out.2.1.1 out.2.1.2.1 out.2.1.2.2 && fresh out.2.2 out.2.1

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
  𝒟[winCondition <$> runtime.evalSPMF (interaction alg adv)]

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
      Pr[= b | winCondition <$> runtime.evalSPMF (interaction alg adv)] := by
  simp [outputMeasure]

/-- Checking the interaction produces a subprobability measure, preserving missing mass. -/
theorem outputMeasure_mass_le_one [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool) :
    outputMeasure alg runtime adv winCondition Set.univ ≤ 1 :=
  evalDist_apply_univ_le_one _

/-- Entirely missing runtime transcript mass produces zero winning probability. -/
theorem outputMeasure_eq_zero_of_failure [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool)
    (h : runtime.evalSPMF (interaction alg adv) = failure) :
    outputMeasure alg runtime adv winCondition {true} = 0 := by
  simp [outputMeasure, h]

/-- Moving the observation inside the surface program requires this explicit runtime law. -/
theorem outputMeasure_eq_runtime [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S)
    (winCondition : ExperimentResult PK E M S → Bool)
    (hfactor : runtime.evalSPMF (winCondition <$> interaction alg adv) =
      winCondition <$> runtime.evalSPMF (interaction alg adv)) :
    outputMeasure alg runtime adv winCondition {true} =
      Pr[= true | runtime.evalSPMF (winCondition <$> interaction alg adv)] := by
  rw [outputMeasure_apply_singleton, hfactor]

/-- Unforgeability advantage is bounded by strong advantage for the same adversary and runtime.
No runtime map law is needed because both observations follow the common evaluation. -/
theorem advantage_le_strongAdvantage
    [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : Adversary spec PK E M S) :
    advantage alg runtime adv ≤ strongAdvantage alg runtime adv := by
  simp only [advantage, strongAdvantage, unforgeableExp, strongUnforgeableExp,
    outputMeasure_apply_singleton,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_mono fun out _ h => strongValid_of_valid alg out h

end SyncSignatureUnforgeability
