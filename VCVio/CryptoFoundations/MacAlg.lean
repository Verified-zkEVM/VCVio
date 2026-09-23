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
UF-CMA security game (message freshness) and the SUF-CMA security game (pair freshness).

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

section sound

variable {m : Type → Type v} [Monad m] {M K T : Type}

/-- Perfect completeness for a MAC: honestly generated tags always verify. -/
def PerfectlyComplete (macAlg : MacAlg m M K T) (runtime : ProbCompRuntime m) : Prop :=
  ∀ msg : M, runtime.evalDist (do
    let k ← macAlg.keygen
    let τ ← macAlg.tag k msg
    macAlg.verify k msg τ) {true} = 1

end sound

section UF_CMA

variable {ι : Type u} {spec : OracleSpec ι} {M K T : Type}
  [DecidableEq M] [DecidableEq T]

/-- UF-CMA adversary for a MAC: it receives oracle access to the tagging oracle and outputs a
candidate forgery `(msg, tag)`. -/
structure UF_CMA_Adversary (_macAlg : MacAlg (OracleComp spec) M K T) where
  main : OracleComp (spec + (M →ₒ T)) (M × T)

/-- UF-CMA experiment for a MAC: the adversary succeeds iff it outputs a valid tag for a fresh
message under the challenge key. -/
noncomputable def UF_CMA_Exp {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) : MeasureTheory.Measure Bool :=
  runtime.evalDist do
    let k ← macAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ T))
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) +
        macAlg.taggingOracle k
    let sim_adv : WriterT (QueryLog (M →ₒ T)) (OracleComp spec) (M × T) :=
      simulateQ impl adversary.main
    let ((msg, τ), log) ← sim_adv.run
    let verified ← macAlg.verify k msg τ
    return !log.wasQueried msg && verified

/-- UF-CMA advantage for a MAC, represented as the probability of producing a valid forgery on a
fresh message. -/
noncomputable def UF_CMA_Advantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) : ℝ≥0∞ :=
  UF_CMA_Exp runtime adversary {true}

end UF_CMA

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
(Bellare-Namprempre 2000; Boneh-Shoup, Attack Game 6.1). The adversary has the same interface as
in `UF_CMA_Exp`, but succeeds iff it outputs a valid pair `(msg, τ)` that the tagging oracle never
returned: a new tag on a previously queried message counts as a forgery. -/
noncomputable def strongUnforgeableExp {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) : MeasureTheory.Measure Bool :=
  runtime.evalDist do
    let k ← macAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ T))
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) +
        macAlg.taggingOracle k
    let sim_adv : WriterT (QueryLog (M →ₒ T)) (OracleComp spec) (M × T) :=
      simulateQ impl adversary.main
    let ((msg, τ), log) ← sim_adv.run
    let verified ← macAlg.verify k msg τ
    return !taggingLogContains log msg τ && verified

instance {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec)) (adversary : macAlg.UF_CMA_Adversary) :
    MeasureTheory.IsSubprobabilityMeasure (strongUnforgeableExp runtime adversary) := by
  unfold strongUnforgeableExp
  infer_instance

/-- SUF-CMA advantage for a MAC: the probability of producing a valid message-tag pair not
previously returned by the tagging oracle. -/
noncomputable def strongUnforgeableAdvantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) : ℝ≥0∞ :=
  strongUnforgeableExp runtime adversary {true}

/-- Strong unforgeability is at least as demanding as ordinary unforgeability: every UF-CMA
forgery (a valid tag on an unqueried message) is also a SUF-CMA forgery, since a pair whose
message was never queried cannot occur in the tagging log. -/
theorem UF_CMA_Advantage_le_strongUnforgeableAdvantage
    {macAlg : MacAlg (OracleComp spec) M K T}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : macAlg.UF_CMA_Adversary) :
    UF_CMA_Advantage runtime adversary ≤ strongUnforgeableAdvantage runtime adversary := by
  let : MeasurableSpace (M × T × QueryLog (M →ₒ T) × Bool) := ⊤
  unfold UF_CMA_Advantage UF_CMA_Exp strongUnforgeableAdvantage strongUnforgeableExp
  set joint : OracleComp spec (M × T × QueryLog (M →ₒ T) × Bool) := do
    let k ← macAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ T))
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) +
        macAlg.taggingOracle k
    let sim_adv : WriterT (QueryLog (M →ₒ T)) (OracleComp spec) (M × T) :=
      simulateQ impl adversary.main
    let ((msg, τ), log) ← sim_adv.run
    let verified ← macAlg.verify k msg τ
    pure (msg, τ, log, verified) with hjoint_def
  let uf : M × T × QueryLog (M →ₒ T) × Bool → Bool := fun t =>
    !t.2.2.1.wasQueried t.1 && t.2.2.2
  let suf : M × T × QueryLog (M →ₒ T) × Bool → Bool := fun t =>
    !taggingLogContains t.2.2.1 t.1 t.2.1 && t.2.2.2
  have huf : Measurable uf := Measurable.of_discrete
  have hsuf : Measurable suf := Measurable.of_discrete
  have hUF : (runtime.evalDist do
        let k ← macAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ T))
            (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) +
            macAlg.taggingOracle k
        let sim_adv : WriterT (QueryLog (M →ₒ T)) (OracleComp spec) (M × T) :=
          simulateQ impl adversary.main
        let ((msg, τ), log) ← sim_adv.run
        let verified ← macAlg.verify k msg τ
        pure (!log.wasQueried msg && verified)) =
      (runtime.evalDist joint).map uf := by
    rw [← runtime.evalDist_bind_pure joint uf huf]
    congr 1
    simp only [uf, hjoint_def, monad_norm]
  have hSUF : (runtime.evalDist do
        let k ← macAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ T))
            (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ T)) (OracleComp spec)) +
            macAlg.taggingOracle k
        let sim_adv : WriterT (QueryLog (M →ₒ T)) (OracleComp spec) (M × T) :=
          simulateQ impl adversary.main
        let ((msg, τ), log) ← sim_adv.run
        let verified ← macAlg.verify k msg τ
        pure (!taggingLogContains log msg τ && verified)) =
      (runtime.evalDist joint).map suf := by
    rw [← runtime.evalDist_bind_pure joint suf hsuf]
    congr 1
    simp only [suf, hjoint_def, monad_norm]
  rw [hUF, hSUF, MeasureTheory.Measure.map_apply huf (measurableSet_singleton true),
    MeasureTheory.Measure.map_apply hsuf (measurableSet_singleton true)]
  refine MeasureTheory.measure_mono fun t ht => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, uf, suf, Bool.and_eq_true,
    Bool.not_eq_true'] at ht ⊢
  refine ⟨?_, ht.2⟩
  cases hc : taggingLogContains t.2.2.1 t.1 t.2.1
  · rfl
  · simp [wasQueried_eq_true_of_taggingLogContains_eq_true _ _ _ hc] at ht

end strongUnforgeable

end MacAlg
