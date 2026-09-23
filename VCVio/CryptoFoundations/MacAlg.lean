/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.EvalDist.Defs.Measure.Deterministic
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.SimSemantics.Append.Core
public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Message Authentication Codes

This file defines keyed message-authentication-code algorithms together with their standard
UF-CMA security game `unforgeableExp` (message freshness) and the SUF-CMA security game
`strongUnforgeableExp` (pair freshness).

## References

- [Bellare, Namprempre, *Authenticated Encryption: Relations among Notions and Analysis of the
  Generic Composition Paradigm*, ASIACRYPT 2000](https://eprint.iacr.org/2000/025)
- [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §6.1]
  (https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
-/

@[expose] public section

universe u v

open OracleSpec OracleComp ENNReal

/-- MAC algorithm with computations in the monad `m`, where `M` is the message space, `K` the key
space, and `T` the tag space. -/
structure MacAlg (m : Type → Type v) [Monad m] (M K T : Type) where
  keygen : m K
  tag : K → M → m T
  verify : K → M → T → m Bool

namespace MacAlg
section taggingOracle

variable {m : Type → Type v} [Monad m] {M K T : Type}

/-- Oracle exposing chosen-message tagging queries while logging every queried message. -/
def taggingOracle (macAlg : MacAlg m M K T) (k : K) :
    QueryImpl (M →ₒ T) (WriterT (QueryLog (M →ₒ T)) m) :=
  QueryImpl.withLogging (fun msg => macAlg.tag k msg)

end taggingOracle

section runWithTaggingOracle

variable {ι : Type u} {spec : OracleSpec ι} {M K T : Type}

/-- Run `oa` against the ambient oracles `spec` and a tagging oracle for `macAlg` under the key
`k`. Ambient queries are forwarded unchanged and tagging queries are answered by
`macAlg.taggingOracle k`. The result pairs the output of `oa` with the log of every
`(message, tag)` pair the tagging oracle returned. -/
def runWithTaggingOracle (macAlg : MacAlg (OracleComp spec) M K T) (k : K) {α : Type}
    (oa : OracleComp (spec + (M →ₒ T)) α) : OracleComp spec (α × QueryLog (M →ₒ T)) :=
  (simulateQ (spec.passthrough + macAlg.taggingOracle k) oa).run

lemma runWithTaggingOracle_def (macAlg : MacAlg (OracleComp spec) M K T) (k : K) {α : Type}
    (oa : OracleComp (spec + (M →ₒ T)) α) :
    macAlg.runWithTaggingOracle k oa =
      (simulateQ (spec.passthrough + macAlg.taggingOracle k) oa).run := rfl

end runWithTaggingOracle

section sound

variable {m : Type → Type v} [Monad m] {M K T : Type}

/-- Perfect completeness for a MAC: honestly generated tags always verify. -/
def PerfectlyComplete (macAlg : MacAlg m M K T) (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, runtime.evalDist (do
    let k ← macAlg.keygen
    let τ ← macAlg.tag k msg
    macAlg.verify k msg τ) {true} = 1

end sound

section unforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M K T : Type}
  [DecidableEq M] [DecidableEq T]

/-- Chosen-message forger for a MAC: it has oracle access to `spec` and to the tagging oracle,
and outputs a candidate forgery `(msg, τ)`. The UF-CMA and SUF-CMA games share this interface. -/
structure UnforgeableAdversary (_macAlg : MacAlg (OracleComp spec) M K T) where
  /-- Run against `spec` and the tagging oracle, returning the candidate forgery. -/
  main : OracleComp (spec + (M →ₒ T)) (M × T)

/-- UF-CMA experiment for a MAC: the adversary succeeds iff it outputs a valid tag on a message
it never submitted to the tagging oracle. -/
noncomputable def unforgeableExp {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UnforgeableAdversary) : MeasureTheory.Measure Bool :=
  runtime.evalDist do
    let k ← macAlg.keygen
    let ((msg, τ), log) ← macAlg.runWithTaggingOracle k adversary.main
    let verified ← macAlg.verify k msg τ
    return !log.wasQueried msg && verified

/-- UF-CMA advantage for a MAC: the probability of producing a valid forgery on a fresh
message. -/
noncomputable def unforgeableAdvantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UnforgeableAdversary) : ℝ≥0∞ :=
  unforgeableExp runtime adversary {true}

end unforgeable

section strongUnforgeable

variable {ι : Type u} {spec : OracleSpec ι} {M K T : Type}
  [DecidableEq M] [DecidableEq T]

/-- Whether the tagging-oracle log contains the exact returned pair `(msg, τ)`. Unlike
`QueryLog.wasQueried`, this predicate distinguishes two tags returned for the same message. -/
def taggingLogContains (log : QueryLog (M →ₒ T)) (msg : M) (τ : T) : Bool :=
  decide (⟨msg, τ⟩ ∈ log)

@[simp]
lemma taggingLogContains_nil (msg : M) (τ : T) :
    taggingLogContains ([] : QueryLog (M →ₒ T)) msg τ = false := by
  simp [taggingLogContains]

/-- Exact returned-pair membership implies ordinary message membership in the same tagging log. -/
lemma wasQueried_eq_true_of_taggingLogContains_eq_true
    (log : QueryLog (M →ₒ T)) (msg : M) (τ : T)
    (h : taggingLogContains log msg τ = true) : log.wasQueried msg = true := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq]
  rw [taggingLogContains, decide_eq_true_eq] at h
  exact List.mem_map.mpr ⟨⟨msg, τ⟩, h, rfl⟩

/-- SUF-CMA (strong unforgeability under chosen-message attack) experiment for a MAC
(Bellare-Namprempre 2000; Boneh-Shoup, Attack Game 6.1). The adversary is as in
`unforgeableExp`, but succeeds iff it outputs a valid pair `(msg, τ)` that the tagging oracle
never returned: a new tag on a previously queried message counts as a forgery. -/
noncomputable def strongUnforgeableExp {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UnforgeableAdversary) : MeasureTheory.Measure Bool :=
  runtime.evalDist do
    let k ← macAlg.keygen
    let ((msg, τ), log) ← macAlg.runWithTaggingOracle k adversary.main
    let verified ← macAlg.verify k msg τ
    return !taggingLogContains log msg τ && verified

instance {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : macAlg.UnforgeableAdversary) :
    MeasureTheory.IsSubprobabilityMeasure (strongUnforgeableExp runtime adversary) := by
  unfold strongUnforgeableExp
  infer_instance

/-- SUF-CMA advantage for a MAC: the probability of producing a valid message-tag pair not
previously returned by the tagging oracle. -/
noncomputable def strongUnforgeableAdvantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UnforgeableAdversary) : ℝ≥0∞ :=
  strongUnforgeableExp runtime adversary {true}

/-- The run shared by `unforgeableExp` and `strongUnforgeableExp`: the candidate forgery, the
tagging log, and the verification bit. -/
def forgeryRun {macAlg : MacAlg (OracleComp spec) M K T}
    (adversary : macAlg.UnforgeableAdversary) :
    OracleComp spec ((M × T) × QueryLog (M →ₒ T) × Bool) := do
  let k ← macAlg.keygen
  let ((msg, τ), log) ← macAlg.runWithTaggingOracle k adversary.main
  let verified ← macAlg.verify k msg τ
  return ((msg, τ), log, verified)

/-- Strong unforgeability is at least as demanding as ordinary unforgeability: every UF-CMA
forgery (a valid tag on an unqueried message) is also a SUF-CMA forgery, since a pair whose
message was never queried cannot occur in the tagging log. -/
theorem unforgeableAdvantage_le_strongUnforgeableAdvantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UnforgeableAdversary) :
    unforgeableAdvantage runtime adversary ≤ strongUnforgeableAdvantage runtime adversary := by
  let : MeasurableSpace ((M × T) × QueryLog (M →ₒ T) × Bool) := ⊤
  let uf : (M × T) × QueryLog (M →ₒ T) × Bool → Bool := fun ⟨(msg, _), log, v⟩ =>
    !log.wasQueried msg && v
  let suf : (M × T) × QueryLog (M →ₒ T) × Bool → Bool := fun ⟨(msg, τ), log, v⟩ =>
    !taggingLogContains log msg τ && v
  have huf : Measurable uf := Measurable.of_discrete
  have hsuf : Measurable suf := Measurable.of_discrete
  have hUF : unforgeableExp runtime adversary =
      (runtime.evalDist (forgeryRun adversary)).map uf := by
    rw [← runtime.evalDist_bind_pure _ uf huf]
    simp only [unforgeableExp, forgeryRun, uf, monad_norm]
  have hSUF : strongUnforgeableExp runtime adversary =
      (runtime.evalDist (forgeryRun adversary)).map suf := by
    rw [← runtime.evalDist_bind_pure _ suf hsuf]
    simp only [strongUnforgeableExp, forgeryRun, suf, monad_norm]
  rw [unforgeableAdvantage, strongUnforgeableAdvantage, hUF, hSUF,
    MeasureTheory.Measure.map_apply huf (measurableSet_singleton true),
    MeasureTheory.Measure.map_apply hsuf (measurableSet_singleton true)]
  refine MeasureTheory.measure_mono fun ⟨(msg, τ), log, v⟩ ht => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, uf, suf, Bool.and_eq_true,
    Bool.not_eq_true'] at ht ⊢
  refine ⟨?_, ht.2⟩
  cases hc : taggingLogContains log msg τ
  · rfl
  · simp [wasQueried_eq_true_of_taggingLogContains_eq_true _ _ _ hc] at ht

end strongUnforgeable

end MacAlg
