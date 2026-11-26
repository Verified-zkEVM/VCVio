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
# Unforgeability of synchronized signatures

The signing oracle answers only the first request at each epoch. A returned signing failure still
uses up its epoch, and a later request at a used epoch returns `none` without running the signer.
The oracle records each first request and its answer in a `History`.

Strong unforgeability (SUF-CMA) counts a forgery when it verifies and differs from the exact
message/signature pair returned at its epoch. Unforgeability (EUF-CMA) also requires its message
to differ from the first message requested at that epoch, even when that request failed. Both
experiments run the same adversary, and `unforgeableAdvantage_le_strongUnforgeableAdvantage`
compares them.

## References

- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), Definition 8 (SY-UF-CMA).
-/

public section

namespace SyncSignatureAlg

open OracleSpec OracleComp ENNReal

universe u v

variable {M PK SK S E : Type}

section history

/-- The first request at each epoch, with the signing oracle's answer to it. -/
@[expose] def History (E M S : Type) := E → Option (M × Option S)

/-- A candidate forgery: an epoch, a message and a signature. -/
@[expose] def Forgery (E M S : Type) := E × M × S

/-- The history before any signing request. -/
@[expose] def emptyHistory : History E M S := fun _ => none

/-- Record a request at an unused epoch; a used epoch keeps its first request. -/
@[expose] def record [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) : History E M S :=
  if history ep = none then Function.update history ep (some (msg, answer)) else history

@[simp] theorem record_eq_update [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep = none) :
    record history ep msg answer = Function.update history ep (some (msg, answer)) := by
  unfold record
  exact ite_eq_left h

/-- A request at an unused epoch is recorded even when its answer is `none`. -/
theorem record_unused [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep = none) :
    record history ep msg answer ep = some (msg, answer) := by
  simp [record, h, Function.update]

theorem record_used [DecidableEq E] (history : History E M S)
    (ep : E) (msg : M) (answer : Option S) (h : history ep ≠ none) :
    record history ep msg answer = history := by
  simp [record, h]

theorem record_other [DecidableEq E] (history : History E M S)
    (ep other : E) (msg : M) (answer : Option S) (h : other ≠ ep) :
    record history ep msg answer other = history other := by
  by_cases hu : history ep = none
  · simp [record, hu, h, Function.update]
  · simp [record, hu]

/-- Strong freshness: the forgery differs from the exact pair returned at its epoch. -/
@[expose] def strongFresh [DecidableEq M] [DecidableEq S]
    (history : History E M S) (forgery : Forgery E M S) : Bool :=
  let candidate := forgery.2
  decide (history forgery.1 ≠ some (candidate.1, some candidate.2))

/-- Freshness: the forgery's message differs from the first message requested at its epoch. -/
@[expose] def fresh [DecidableEq M]
    (history : History E M S) (forgery : Forgery E M S) : Bool :=
  let candidate := forgery.2
  match history forgery.1 with
  | none => true
  | some (msg, _) => decide (candidate.1 ≠ msg)

theorem strongFresh_of_fresh [DecidableEq M] [DecidableEq S]
    (history : History E M S) (forgery : Forgery E M S)
    (h : fresh history forgery = true) : strongFresh history forgery = true := by
  cases hh : history forgery.1 with
  | none => simp [strongFresh, hh]
  | some entry =>
    rcases entry with ⟨msg, answer⟩
    simp only [fresh, hh, decide_eq_true_eq] at h
    simp [strongFresh, hh, Ne.symm h]

/-- Every successful record in the history satisfies `P`. -/
@[expose] def SuccessfulHistorySatisfies (P : E → M → S → Prop)
    (history : History E M S) : Prop :=
  ∀ ep msg sig, history ep = some (msg, some sig) → P ep msg sig

theorem successfulHistorySatisfies_empty (P : E → M → S → Prop) :
    SuccessfulHistorySatisfies P (emptyHistory : History E M S) := by
  intro ep msg sig hentry
  simp [emptyHistory] at hentry

/-- Recording an answer whose successful values satisfy `P` preserves the invariant. -/
theorem SuccessfulHistorySatisfies.record [DecidableEq E] {P : E → M → S → Prop}
    {history : History E M S} (h : SuccessfulHistorySatisfies P history)
    (ep : E) (msg : M) (answer : Option S)
    (hanswer : ∀ sig, answer = some sig → P ep msg sig) :
    SuccessfulHistorySatisfies P (SyncSignatureAlg.record history ep msg answer) := by
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

end history

section signingOracle

/-- A signing query is an epoch and a message; the answer is a signature or `none`. -/
abbrev signingSpec (E M S : Type) : OracleSpec (E × M) :=
  (E × M) →ₒ Option S

/-- The signing oracle with an arbitrary signing callback. A request at a used epoch returns
`none` and leaves the history unchanged. A request at an unused epoch runs the callback once and
records its answer, including `none`. Reductions use this form to answer signing queries with a
simulated signer under the same epoch discipline. -/
@[expose, simps] def signingKernelOracle [DecidableEq E]
    {m : Type → Type v} [Monad m] (kernel : E → M → m (Option S)) :
    QueryImpl (signingSpec E M S) (StateT (History E M S) m) where
  toFun := fun ⟨ep, msg⟩ history =>
    match history ep with
    | some _ => pure (none, history)
    | none => do
      let answer ← kernel ep msg
      pure (answer, record history ep msg answer)

theorem signingKernelOracle_used [DecidableEq E]
    {m : Type → Type v} [Monad m] (kernel : E → M → m (Option S))
    (history : History E M S) (ep : E) (msg first : M) (answer : Option S)
    (h : history ep = some (first, answer)) :
    signingKernelOracle kernel (ep, msg) history = pure (none, history) := by
  simp [signingKernelOracle_apply, h]

theorem signingKernelOracle_unused [DecidableEq E]
    {m : Type → Type v} [Monad m] (kernel : E → M → m (Option S))
    (history : History E M S) (ep : E) (msg : M) (h : history ep = none) :
    signingKernelOracle kernel (ep, msg) history = (do
      let answer ← kernel ep msg
      pure (answer, Function.update history ep (some (msg, answer)))) := by
  simp [signingKernelOracle_apply, record, h]

/-- The scheme's signing oracle: `signingKernelOracle` with the callback `alg.sign sk`. -/
@[expose] def signingOracle [DecidableEq E]
    {m : Type → Type v} [Monad m]
    (alg : SyncSignatureAlg m M PK SK S E) (sk : SK) :
    QueryImpl (signingSpec E M S) (StateT (History E M S) m) :=
  signingKernelOracle (alg.sign sk)

theorem signingOracle_used [DecidableEq E]
    {m : Type → Type v} [Monad m]
    (alg : SyncSignatureAlg m M PK SK S E) (sk : SK)
    (history : History E M S) (ep : E) (msg first : M) (answer : Option S)
    (h : history ep = some (first, answer)) :
    alg.signingOracle sk (ep, msg) history = pure (none, history) :=
  signingKernelOracle_used _ history ep msg first answer h

theorem signingOracle_unused [DecidableEq E]
    {m : Type → Type v} [Monad m]
    (alg : SyncSignatureAlg m M PK SK S E) (sk : SK)
    (history : History E M S) (ep : E) (msg : M) (h : history ep = none) :
    alg.signingOracle sk (ep, msg) history = (do
      let answer ← alg.sign sk ep msg
      pure (answer, Function.update history ep (some (msg, answer)))) :=
  signingKernelOracle_unused _ history ep msg h

variable {ι : Type u} {spec : OracleSpec ι}

/-- Run `program` with its ambient oracles passed through and signing queries answered by
`signingKernelOracle kernel`, starting from `history`. -/
@[expose] def runWithSigningKernel [DecidableEq E]
    (kernel : E → M → OracleComp spec (Option S))
    {A : Type} (program : OracleComp (spec + signingSpec E M S) A)
    (history : History E M S) : OracleComp spec (A × History E M S) :=
  (simulateQ (spec.passthrough + signingKernelOracle kernel) program).run history

/-- Run `program` with its ambient oracles passed through and signing queries answered by
`alg.signingOracle sk`, starting from `history`. -/
@[expose] def runWithSigningOracle [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    {A : Type} (program : OracleComp (spec + signingSpec E M S) A)
    (history : History E M S) : OracleComp spec (A × History E M S) :=
  runWithSigningKernel (alg.sign sk) program history

theorem signingKernelOracle_preserves_successfulHistorySatisfies [DecidableEq E]
    (kernel : E → M → OracleComp spec (Option S))
    (P : E → M → S → Prop)
    (hsign : ∀ ep msg sig, some sig ∈ support (kernel ep msg) → P ep msg sig)
    (q : E × M) (history : History E M S) (hinv : SuccessfulHistorySatisfies P history)
    (out : Option S × History E M S)
    (hout : out ∈ support ((signingKernelOracle kernel q).run history)) :
    SuccessfulHistorySatisfies P out.2 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (signingKernelOracle kernel (ep, msg) history) at hout
  cases hused : history ep with
  | none =>
    rw [signingKernelOracle_unused _ _ _ _ hused, mem_support_bind_iff] at hout
    obtain ⟨answer, hanswer, hreturn⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hreturn
    subst out
    have hrecord := hinv.record ep msg answer (fun sig heq =>
      hsign ep msg sig (heq ▸ hanswer))
    simpa only [record_eq_update _ _ _ _ hused] using hrecord
  | some entry =>
    rw [signingKernelOracle_used _ _ _ _ entry.1 entry.2 hused, support_pure,
      Set.mem_singleton_iff] at hout
    exact hout ▸ hinv

/-- If every successful callback output satisfies `P`, so does every successful record left by a
run, from any history satisfying `P`. -/
theorem runWithSigningKernel_preserves_successfulHistorySatisfies [DecidableEq E]
    (kernel : E → M → OracleComp spec (Option S))
    (P : E → M → S → Prop)
    (hsign : ∀ ep msg sig, some sig ∈ support (kernel ep msg) → P ep msg sig)
    {A : Type} (program : OracleComp (spec + signingSpec E M S) A)
    (history : History E M S) (hinv : SuccessfulHistorySatisfies P history)
    (out : A × History E M S) (hout : out ∈ support
      (runWithSigningKernel kernel program history)) : SuccessfulHistorySatisfies P out.2 := by
  apply OracleComp.simulateQ_run_preservesInv (spec.passthrough + signingKernelOracle kernel)
    (SuccessfulHistorySatisfies P) ?_ program history hinv out hout
  rintro (q | q) state hs result hresult
  · simp only [OracleSpec.passthrough, QueryImpl.passthrough_add, QueryImpl.add_apply_inl,
      QueryImpl.liftTarget_apply, StateT.run_liftM, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff] at hresult
    obtain ⟨answer, _, rfl⟩ := hresult
    exact hs
  · exact signingKernelOracle_preserves_successfulHistorySatisfies kernel P hsign q state hs
      result hresult

theorem signingOracle_preserves_successfulHistorySatisfies [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    (P : E → M → S → Prop)
    (hsign : ∀ ep msg sig, some sig ∈ support (alg.sign sk ep msg) → P ep msg sig)
    (q : E × M) (history : History E M S) (hinv : SuccessfulHistorySatisfies P history)
    (out : Option S × History E M S)
    (hout : out ∈ support ((alg.signingOracle sk q).run history)) :
    SuccessfulHistorySatisfies P out.2 :=
  signingKernelOracle_preserves_successfulHistorySatisfies (alg.sign sk) P hsign
    q history hinv out hout

theorem runWithSigningOracle_preserves_successfulHistorySatisfies [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E) (sk : SK)
    (P : E → M → S → Prop)
    (hsign : ∀ ep msg sig, some sig ∈ support (alg.sign sk ep msg) → P ep msg sig)
    {A : Type} (program : OracleComp (spec + signingSpec E M S) A)
    (history : History E M S) (hinv : SuccessfulHistorySatisfies P history)
    (out : A × History E M S) (hout : out ∈ support
      (alg.runWithSigningOracle sk program history)) : SuccessfulHistorySatisfies P out.2 :=
  runWithSigningKernel_preserves_successfulHistorySatisfies (alg.sign sk) P hsign
    program history hinv out hout

end signingOracle

section unforgeable

variable {ι : Type u} {spec : OracleSpec ι}

/-- An adversary against unforgeability and strong unforgeability. Given the public key, it runs
with the ambient oracles `spec` and the signing oracle, and outputs a candidate forgery. -/
structure UnforgeableAdversary (spec : OracleSpec ι) (PK E M S : Type) where
  /-- Given the public key, output a candidate forgery. -/
  forge : PK → OracleComp (spec + signingSpec E M S) (Forgery E M S)

/-- The adversary makes at most `qs` signing queries, counting repeated epochs and requests
answered with `none`. The query-bound API requires an index type in `Type`. -/
@[expose] def SigningQueryBound {ι : Type} {spec : OracleSpec ι} (qs : ℕ)
    (adv : UnforgeableAdversary spec PK E M S) : Prop :=
  ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs

/-- The public key, the candidate forgery and the final signing history. -/
@[expose] def ExperimentResult (PK E M S : Type) := PK × Forgery E M S × History E M S

/-- Generate keys and run the adversary against the signing oracle from the empty history. -/
@[expose] def interaction [DecidableEq E]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (adv : UnforgeableAdversary spec PK E M S) : OracleComp spec (ExperimentResult PK E M S) := do
  let (pk, sk) ← alg.keygen
  let (forgery, history) ← alg.runWithSigningOracle sk (adv.forge pk) emptyHistory
  pure (pk, forgery, history)

/-- A strong forgery verifies and differs from the exact pair returned at its epoch. -/
@[expose] def strongValid [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) : Bool :=
  let result := out.2
  let forgery := result.1
  let candidate := forgery.2
  alg.verify out.1 forgery.1 candidate.1 candidate.2 && strongFresh result.2 forgery

/-- A forgery verifies and its message differs from the first message requested at its epoch. -/
@[expose] def valid [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) : Bool :=
  let result := out.2
  let forgery := result.1
  let candidate := forgery.2
  alg.verify out.1 forgery.1 candidate.1 candidate.2 && fresh result.2 forgery

theorem strongValid_of_valid [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (out : ExperimentResult PK E M S) (h : alg.valid out = true) :
    alg.strongValid out = true := by
  simp only [valid, Bool.and_eq_true] at h
  simp [strongValid, h.1, strongFresh_of_fresh _ _ h.2]

/-- The unforgeability (EUF-CMA) experiment. -/
@[expose] def unforgeableExperiment [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (adv : UnforgeableAdversary spec PK E M S) : OracleComp spec Bool :=
  alg.valid <$> alg.interaction adv

/-- The strong unforgeability (SUF-CMA) experiment. -/
@[expose] def strongUnforgeableExperiment [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (adv : UnforgeableAdversary spec PK E M S) : OracleComp spec Bool :=
  alg.strongValid <$> alg.interaction adv

/-- The probability that `unforgeableExperiment` returns `true`. Missing execution mass is not
renormalized. -/
@[expose] noncomputable def unforgeableAdvantage [DecidableEq E] [DecidableEq M]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary spec PK E M S) : ℝ≥0∞ :=
  runtime.evalDist (alg.unforgeableExperiment adv) {true}

/-- The probability that `strongUnforgeableExperiment` returns `true`. Missing execution mass is
not renormalized. -/
@[expose] noncomputable def strongUnforgeableAdvantage
    [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary spec PK E M S) : ℝ≥0∞ :=
  runtime.evalDist (alg.strongUnforgeableExperiment adv) {true}

/-- Every unforgeability win is a strong unforgeability win for the same adversary. -/
theorem unforgeableAdvantage_le_strongUnforgeableAdvantage
    [DecidableEq E] [DecidableEq M] [DecidableEq S]
    (alg : SyncSignatureAlg (OracleComp spec) M PK SK S E)
    (runtime : ProbCompRuntime (OracleComp spec)) (adv : UnforgeableAdversary spec PK E M S) :
    alg.unforgeableAdvantage runtime adv ≤ alg.strongUnforgeableAdvantage runtime adv := by
  simp only [unforgeableAdvantage, strongUnforgeableAdvantage, unforgeableExperiment,
    strongUnforgeableExperiment]
  let : MeasurableSpace (ExperimentResult PK E M S) := ⊤
  rw [runtime.evalDist_map _ Measurable.of_discrete,
    runtime.evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  exact MeasureTheory.measure_mono fun out h => alg.strongValid_of_valid out h

end unforgeable

end SyncSignatureAlg
