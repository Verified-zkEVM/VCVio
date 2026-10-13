/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Encoding.Error
import Mathlib.Algebra.Ring.GeomSum
import ToMathlib.MeasureTheory.Measure.Bool

/-!
# Bounded first-success encoding retries

Fresh draws use one fixed sampler. Returned encoding failure advances the finite retry loop;
missing execution mass remains missing. All probability observations follow runtime evaluation.
-/

public section

namespace GXMSS.Encoding

open ENNReal

variable {PP M R E : Type} {n radix : ℕ}

/-- The canonical probability runtime preserves pure computations and sequential sampling. -/
theorem samplingLaws_probComp : SamplingLaws ProbCompRuntime.probComp where
  pure_eq x := by
    simp [ProbCompRuntime.probComp_evalDist]
  bind_eq {α} {β} c f p := by
    let : MeasurableSpace α := ⊤
    simpa only [ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_map]
      using prEvent_bind_eq_lintegral_of_discrete c f p

namespace IncomparableEncoding

section Retry

variable {m : Type → Type*} [Monad m]

/-- Draw fresh randomness on each iteration and stop at the first successful encoding.
The monadic bind preserves divergence; returned encoding failure proceeds to the next attempt. -/
@[expose] def retry (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : ℕ → m (Option (Codeword n radix × R))
  | 0 => pure none
  | k + 1 => do
      let r ← sample
      match enc.value pp msg r ep with
      | none => retry enc sample pp msg ep k
      | some word => pure (some (word, r))

/-- Zero retries perform no draw and return exhaustion. -/
theorem retry_zero (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : retry enc sample pp msg ep 0 = pure none := rfl

/-- One attempt returns exactly the optional word paired with its sampled randomizer. -/
theorem retry_one (enc : IncomparableEncoding PP M R E n radix) (sample : m R)
    (pp : PP) (msg : M) (ep : E) :
    retry enc sample pp msg ep 1 =
      sample >>= fun r => pure ((enc.value pp msg r ep).map fun word => (word, r)) := by
  simp only [retry]
  congr 1
  funext r
  cases enc.value pp msg r ep <;> rfl

end Retry

/-- Returned failure, missing sampling mass and returned success partition one attempt. -/
theorem failureMass_add_missingMass_add_successMass
    {m : Type → Type*} [Monad m] (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) :
    enc.failureMass runtime sample pp msg ep + missingMass runtime sample +
      enc.successMass runtime sample pp msg ep = 1 := by
  rw [add_right_comm, failureMass_add_successMass]
  exact tsub_add_cancel_of_le (tsub_le_self : missingMass runtime sample ≤ 1)

namespace Retry

variable {m : Type → Type*} [Monad m]

/-- A returned successful retry retains a randomizer that produces its returned word. -/
theorem value_eq_some_of_mem_retry
    [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    (enc : IncomparableEncoding PP M R E n radix)
    (sample : m R) (pp : PP) (msg : M) (ep : E)
    (k : ℕ) (word : Codeword n radix) (r : R)
    (hs : some (word, r) ∈ support (enc.retry sample pp msg ep k)) :
    enc.value pp msg r ep = some word := by
  induction k with
  | zero =>
      have heq := LawfulMonadAttach.eq_of_canReturn_pure hs
      simp at heq
  | succ k ih =>
    change MonadAttach.CanReturn
      (sample >>= fun r' => match enc.value pp msg r' ep with
        | none => enc.retry sample pp msg ep k
        | some word' => pure (some (word', r'))) (some (word, r)) at hs
    obtain ⟨r', _, hs⟩ := LawfulMonadAttach.canReturn_bind_imp' hs
    cases hv : enc.value pp msg r' ep with
    | none => exact ih (by simpa [hv] using hs)
    | some word' =>
      have hpure := LawfulMonadAttach.eq_of_canReturn_pure (by simpa [hv] using hs)
      have heq : word = word' ∧ r = r' := by simpa using hpure.symm
      rcases heq with ⟨rfl, rfl⟩
      exact hv

/-- The Boolean failure observation applied after interpreting the complete retry computation. -/
@[expose] noncomputable def failureIndicatorDist (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    MeasureTheory.Measure Bool :=
  runtime.evalDist (Option.isNone <$> enc.retry sample pp msg ep k)

/-- Returned exhaustion mass, without conditioning on termination. -/
@[expose] noncomputable def failureMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  failureIndicatorDist enc runtime sample pp msg ep k {true}

/-- Mass of returned successful word/randomizer pairs. -/
@[expose] noncomputable def successMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  failureIndicatorDist enc runtime sample pp msg ep k {false}

/-- Missing execution mass of the retry computation. -/
@[expose] noncomputable def missingMass (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) : ℝ≥0∞ :=
  1 - runtime.evalDist ((fun _ => True) <$> enc.retry sample pp msg ep k) {True}

/-- The three retry observations partition probability one, including missing mass. -/
theorem failureMass_add_missingMass_add_successMass
    (enc : IncomparableEncoding PP M R E n radix) (runtime : ProbCompRuntime m)
    (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k + missingMass enc runtime sample pp msg ep k +
      successMass enc runtime sample pp msg ep k = 1 := by
  change runtime.evalDist (Option.isNone <$> enc.retry sample pp msg ep k) {true} +
      (1 - runtime.evalDist ((fun _ => True) <$> enc.retry sample pp msg ep k) {True}) +
      runtime.evalDist (Option.isNone <$> enc.retry sample pp msg ep k) {false} = 1
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [add_right_comm,
    runtime.evalDist_map Option.isNone Measurable.of_discrete,
    MeasureTheory.Measure.apply_true_add_apply_false,
    runtime.evalDist_map (fun _ : Option (Codeword n radix × R) => True)
      Measurable.of_discrete]
  simp only [MeasureTheory.Measure.map_apply Measurable.of_discrete MeasurableSet.univ,
    Set.preimage_univ,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  have hpreimage :
      (fun _ : Option (Codeword n radix × R) => True) ⁻¹' ({True} : Set Prop) = Set.univ := by
    ext
    simp
  rw [hpreimage, add_comm]
  exact tsub_add_cancel_of_le (runtime.evalDist_apply_univ_le_one _)

/-- Exhaustion is exactly the returned `none` outcome of the interpreted computation. -/
theorem failureMass_eq_probability (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k =
      runtime.evalDist ((fun o => o = none) <$> enc.retry sample pp msg ep k) {True} := by
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [failureMass, failureIndicatorDist,
    runtime.evalDist_map Option.isNone Measurable.of_discrete,
    runtime.evalDist_map (fun o : Option (Codeword n radix × R) => o = none)
      Measurable.of_discrete]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  congr 1
  ext o
  cases o <;> simp

/-- The empty retry budget has unit exhaustion mass. -/
theorem failureMass_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : failureMass enc runtime sample pp msg ep 0 = 1 := by
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [failureMass_eq_probability, retry_zero]
  rw [runtime.evalDist_map (fun o : Option (Codeword n radix × R) => o = none)
    Measurable.of_discrete, laws.pure_eq]
  simp

/-- The empty retry budget has no missing mass because it makes no draw. -/
theorem missingMass_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : missingMass enc runtime sample pp msg ep 0 = 0 := by
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [missingMass, retry_zero]
  rw [runtime.evalDist_map (fun _ : Option (Codeword n radix × R) => True)
    Measurable.of_discrete, laws.pure_eq]
  simp

/-- The empty retry budget returns no successful output. -/
theorem successMass_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) : successMass enc runtime sample pp msg ep 0 = 0 := by
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [successMass, failureIndicatorDist, retry_zero]
  rw [runtime.evalDist_map Option.isNone Measurable.of_discrete, laws.pure_eq]
  simp

/-- Each further attempt multiplies the returned exhaustion mass by one-attempt failure. -/
theorem failureMass_succ (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep (k + 1) =
      enc.failureMass runtime sample pp msg ep * failureMass enc runtime sample pp msg ep k := by
  classical
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [failureMass_eq_probability, retry, laws.bind_eq]
  rw [IncomparableEncoding.failureMass_eq_probability,
    runtime.evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpoint (r : R) :
      runtime.evalDist ((fun o => o = none) <$> match enc.value pp msg r ep with
        | none => enc.retry sample pp msg ep k
        | some word => pure (some (word, r))) {True} =
        if enc.failed pp msg ep r then failureMass enc runtime sample pp msg ep k else 0 := by
    cases h : enc.value pp msg r ep with
    | none => simp [failed, h, failureMass_eq_probability]
    | some word =>
        rw [show enc.failed pp msg ep r = false by simp [failed, h]]
        simp only [Bool.false_eq_true, ite_false]
        rw [runtime.evalDist_map
          (fun o : Option (Codeword n radix × R) => o = none) Measurable.of_discrete,
          laws.pure_eq]
        simp
  simp_rw [hpoint]
  let s : Set R := (enc.failed pp msg ep) ⁻¹' {true}
  calc
    (∫⁻ r, if enc.failed pp msg ep r then
        failureMass enc runtime sample pp msg ep k else 0 ∂runtime.evalDist sample) =
        ∫⁻ r, s.indicator
          (fun _ => failureMass enc runtime sample pp msg ep k) r
          ∂runtime.evalDist sample := by
      apply MeasureTheory.lintegral_congr
      intro r
      cases h : enc.failed pp msg ep r <;> simp [s, h]
    _ = failureMass enc runtime sample pp msg ep k * runtime.evalDist sample s :=
      MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete _
    _ = runtime.evalDist sample s * failureMass enc runtime sample pp msg ep k :=
      mul_comm _ _

/-- Returned exhaustion has exactly the power of the one-attempt returned failure mass. -/
theorem failureMass_eq_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k =
      (enc.failureMass runtime sample pp msg ep) ^ k := by
  induction k with
  | zero => simp [failureMass_zero, laws]
  | succ k ih => rw [failureMass_succ enc runtime laws, ih, pow_succ']

private theorem successMass_eq_probability (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (sample : m R) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep k =
      runtime.evalDist
        ((fun o : Option (Codeword n radix × R) => o.isNone = false) <$>
          enc.retry sample pp msg ep k) {True} := by
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [successMass, failureIndicatorDist,
    runtime.evalDist_map Option.isNone Measurable.of_discrete,
    runtime.evalDist_map
      (fun o : Option (Codeword n radix × R) => o.isNone = false) Measurable.of_discrete]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton false),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton True)]
  congr 1
  ext o
  cases o <;> simp

private theorem successMass_succ_aux (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep (k + 1) =
      enc.successMass runtime sample pp msg ep +
        enc.failureMass runtime sample pp msg ep * successMass enc runtime sample pp msg ep k := by
  classical
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace (Option (Codeword n radix × R)) := ⊤
  rw [successMass_eq_probability, retry, laws.bind_eq]
  rw [IncomparableEncoding.successMass, IncomparableEncoding.failureMass,
    IncomparableEncoding.failureIndicatorDist,
    runtime.evalDist_map _ Measurable.of_discrete]
  rw [MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton false),
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpoint (r : R) :
      runtime.evalDist
        ((fun o : Option (Codeword n radix × R) => o.isNone = false) <$>
          match enc.value pp msg r ep with
        | none => enc.retry sample pp msg ep k
        | some word => pure (some (word, r))) {True} =
        if enc.failed pp msg ep r then successMass enc runtime sample pp msg ep k else 1 := by
    cases h : enc.value pp msg r ep with
    | none =>
        simpa [failed, h] using
          (successMass_eq_probability enc runtime sample pp msg ep k).symm
    | some word =>
        rw [runtime.evalDist_map
          (fun o : Option (Codeword n radix × R) => o.isNone = false)
          Measurable.of_discrete, laws.pure_eq]
        simp [failed, h]
  simp_rw [hpoint]
  let st : Set R := (enc.failed pp msg ep) ⁻¹' {true}
  let sf : Set R := (enc.failed pp msg ep) ⁻¹' {false}
  calc
    (∫⁻ r, if enc.failed pp msg ep r then
        successMass enc runtime sample pp msg ep k else 1 ∂runtime.evalDist sample) =
        ∫⁻ r, sf.indicator (fun _ => 1) r +
          st.indicator (fun _ => successMass enc runtime sample pp msg ep k) r
          ∂runtime.evalDist sample := by
      apply MeasureTheory.lintegral_congr
      intro r
      cases h : enc.failed pp msg ep r <;> simp [st, sf, h]
    _ = (∫⁻ r, sf.indicator (fun _ => 1) r ∂runtime.evalDist sample) +
        ∫⁻ r, st.indicator
          (fun _ => successMass enc runtime sample pp msg ep k) r
          ∂runtime.evalDist sample := by
      rw [MeasureTheory.lintegral_add_left
        (measurable_const.indicator MeasurableSet.of_discrete)]
    _ = runtime.evalDist sample sf +
        runtime.evalDist sample st * successMass enc runtime sample pp msg ep k := by
      rw [MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
        MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete]
      simp [mul_comm]

/-- Missing mass consists of missing the first draw or failing it and missing a later draw. -/
theorem missingMass_succ (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    missingMass enc runtime sample pp msg ep (k + 1) =
      IncomparableEncoding.missingMass runtime sample +
        enc.failureMass runtime sample pp msg ep * missingMass enc runtime sample pp msg ep k := by
  classical
  have hpartition := failureMass_add_missingMass_add_successMass
    enc runtime sample pp msg ep (k + 1)
  have hfailure := failureMass_succ enc runtime laws sample pp msg ep k
  have hsuccess := successMass_succ_aux enc runtime laws sample pp msg ep k
  have hkpartition := failureMass_add_missingMass_add_successMass
    enc runtime sample pp msg ep k
  have hone := IncomparableEncoding.failureMass_add_missingMass_add_successMass
    enc runtime sample pp msg ep
  rw [hfailure, hsuccess] at hpartition
  have hleft :
      (enc.failureMass runtime sample pp msg ep *
          failureMass enc runtime sample pp msg ep k +
        enc.successMass runtime sample pp msg ep +
        enc.failureMass runtime sample pp msg ep *
          successMass enc runtime sample pp msg ep k) +
        missingMass enc runtime sample pp msg ep (k + 1) = 1 := by
    simpa [add_assoc, add_left_comm, add_comm] using hpartition
  have hright :
      (enc.failureMass runtime sample pp msg ep *
          failureMass enc runtime sample pp msg ep k +
        enc.successMass runtime sample pp msg ep +
        enc.failureMass runtime sample pp msg ep *
          successMass enc runtime sample pp msg ep k) +
        (IncomparableEncoding.missingMass runtime sample +
          enc.failureMass runtime sample pp msg ep *
            missingMass enc runtime sample pp msg ep k) = 1 := by
    calc
      _ = enc.failureMass runtime sample pp msg ep *
            (failureMass enc runtime sample pp msg ep k +
              missingMass enc runtime sample pp msg ep k +
              successMass enc runtime sample pp msg ep k) +
          IncomparableEncoding.missingMass runtime sample +
          enc.successMass runtime sample pp msg ep := by ring
      _ = enc.failureMass runtime sample pp msg ep * 1 +
          IncomparableEncoding.missingMass runtime sample +
          enc.successMass runtime sample pp msg ep := by rw [hkpartition]
      _ = 1 := by simpa using hone
  have hcommon_le :
      enc.failureMass runtime sample pp msg ep *
            failureMass enc runtime sample pp msg ep k +
          enc.successMass runtime sample pp msg ep +
          enc.failureMass runtime sample pp msg ep *
            successMass enc runtime sample pp msg ep k ≤ 1 :=
    (le_add_right le_rfl).trans (le_of_eq hleft)
  have hcommon_ne_top :
      enc.failureMass runtime sample pp msg ep *
            failureMass enc runtime sample pp msg ep k +
          enc.successMass runtime sample pp msg ep +
          enc.failureMass runtime sample pp msg ep *
            successMass enc runtime sample pp msg ep k ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hcommon_le
  apply (ENNReal.add_left_inj hcommon_ne_top).mp
  simpa [add_comm] using hleft.trans hright.symm

/-- Missing execution mass accumulates along the prefixes of returned failed attempts. -/
theorem missingMass_eq_mul_sum (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    missingMass enc runtime sample pp msg ep k =
      IncomparableEncoding.missingMass runtime sample *
        ∑ j ∈ Finset.range k, (enc.failureMass runtime sample pp msg ep) ^ j := by
  induction k with
  | zero => simp [missingMass_zero, laws]
  | succ k ih =>
    rw [missingMass_succ enc runtime laws, ih, geom_sum_succ]
    simp [mul_add, mul_left_comm, add_comm]

/-- Lossless randomizer sampling gives lossless bounded retries. -/
theorem missingMass_eq_zero (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (hl : LosslessSampler runtime sample) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    missingMass enc runtime sample pp msg ep k = 0 := by
  rw [missingMass_eq_mul_sum enc runtime laws]
  have hl' : runtime.evalDist ((fun _ => True) <$> sample) {True} = 1 := hl
  have hm : IncomparableEncoding.missingMass runtime sample = 0 := by
    rw [IncomparableEncoding.missingMass, hl']
    simp
  rw [hm]
  simp

/-- A pointwise encoding error bound yields the corresponding power upper bound on exhaustion. -/
theorem failureMass_le_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (δ : ℝ≥0∞) (h : enc.ErrorAtMost runtime sample δ)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    failureMass enc runtime sample pp msg ep k ≤ δ ^ k := by
  rw [failureMass_eq_pow enc runtime laws]
  exact pow_le_pow_left' (h.2 pp msg ep) k

/-- Under losslessness, successful output mass is one minus exact exhaustion mass. -/
theorem successMass_eq_one_sub_pow (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (hl : LosslessSampler runtime sample) (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep k =
      1 - (enc.failureMass runtime sample pp msg ep) ^ k := by
  have h := failureMass_add_missingMass_add_successMass enc runtime sample pp msg ep k
  rw [missingMass_eq_zero enc runtime laws sample hl, add_zero,
    failureMass_eq_pow enc runtime laws] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top
    (le_of_add_le_left (le_of_eq h))) (add_comm _ _ |>.trans h)

/-- A further attempt either succeeds immediately or reaches a successful later attempt. -/
theorem successMass_succ (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep (k + 1) =
      enc.successMass runtime sample pp msg ep +
        enc.failureMass runtime sample pp msg ep * successMass enc runtime sample pp msg ep k := by
  exact successMass_succ_aux enc runtime laws sample pp msg ep k

/-- Successful mass accumulates along exactly the prefixes of returned failed attempts. -/
theorem successMass_eq_mul_sum (enc : IncomparableEncoding PP M R E n radix)
    (runtime : ProbCompRuntime m) (laws : SamplingLaws runtime) (sample : m R)
    (pp : PP) (msg : M) (ep : E) (k : ℕ) :
    successMass enc runtime sample pp msg ep k =
      enc.successMass runtime sample pp msg ep *
        ∑ j ∈ Finset.range k, (enc.failureMass runtime sample pp msg ep) ^ j := by
  induction k with
  | zero => simp [successMass_zero, laws]
  | succ k ih =>
    rw [successMass_succ enc runtime laws, ih, geom_sum_succ]
    simp [mul_add, mul_left_comm, add_comm]

end Retry

end IncomparableEncoding

end GXMSS.Encoding
