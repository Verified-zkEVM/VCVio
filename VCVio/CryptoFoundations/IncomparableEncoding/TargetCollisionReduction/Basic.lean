/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.TargetCollisionResistance
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTRTCR

/-!
# The encoding-to-hash bridge

`Bridge` relates an incomparable encoding to a tweakable hash. This file defines the two games the
reduction compares (`encodingProblem` and `hashProblem`), translates the encoding game's transcript
into the SM-rTCR history (`targetHistory`), and shows that a source win names an SM-rTCR
collision at the first witnessing record (`valid_implies_hash_collision`).
-/

public section

namespace IncomparableEncoding.TargetCollisionReduction

open OracleComp OracleSpec TargetCollisionResistance TweakableHash

variable {PP M R E Tweak Y : Type} {n radix : ℕ}

/-- Data needed to compare the full encoding word with one tweakable-hash output. The success law
includes returned failure, so the target-sum instance cannot silently register failed draws. -/
structure Bridge (PP M R E Tweak Y : Type) (n radix : ℕ) where
  /-- Randomized incomparable encoding connected to the message hash. -/
  enc : IncomparableEncoding PP M R E n radix
  /-- Tweakable message hash on message/randomizer pairs. -/
  th : TweakableHash PP Tweak (M × R) Y
  /-- Address of the message-hash computation for each epoch. -/
  epochToTweak : E → Tweak
  /-- Distinct epochs use distinct tweaks. -/
  epochToTweak_injective : Function.Injective epochToTweak
  /-- Test identifying hash outputs accepted by the encoding. -/
  accepts : Y → Bool
  /-- Codeword associated with each message-hash output. -/
  word : Y → Codeword n radix
  /-- Distinct hash outputs give distinct words. -/
  word_injective : Function.Injective word
  /-- The encoding succeeds exactly when the hash output is accepted, with that output's word. -/
  encode_eq : ∀ pp msg r ep,
    enc.encode pp msg r ep =
      if accepts (th.eval pp (epochToTweak ep) (msg, r)) then
        some (word (th.eval pp (epochToTweak ep) (msg, r))) else none

/-- Both games use the same public-seed draw, record capacity, and retry capacity. -/
@[expose] def encodingProblem [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) :
    TargetCollisionResistance.Problem PP M R E n radix where
  enc := bridge.enc
  paramGen := bridge.th.seedGen
  randomGen := $ᵗ R
  numRecords := p
  numRetries := K

/-- The SM-rTCR game uses the hash word and the encoding success predicate. -/
@[expose] def hashProblem (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) :
    SM_DT_RTCR_Problem PP Tweak M R Y where
  th := bridge.th
  prop := bridge.accepts
  numTargets := p
  numRetries := K

/-- A successful source record contributes its randomizer; exhaustion remains an occupied slot. -/
@[expose] def targetRecord (bridge : Bridge PP M R E Tweak Y n radix)
    (entry : TargetCollisionResistance.Record M R E n radix) : Tweak × M × Option R :=
  (bridge.epochToTweak entry.epoch, entry.message, entry.result.map Prod.snd)

/-- The target history retains every eligible source query in its original order. -/
@[expose] def targetHistory (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) :
    SM_DT_RTCR_State Tweak M R := transcript.map (targetRecord bridge)

/-- Transcript conversion preserves the cap even when a query exhausted its retries. -/
theorem targetHistory_length (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) :
    (targetHistory bridge transcript).length = transcript.length := by
  simp [targetHistory]

/-- Each accepted target keeps its source index, including failed slots. -/
theorem targetHistory_getElem? (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) (index : ℕ) :
    (targetHistory bridge transcript)[index]? =
      (transcript[index]?).map (targetRecord bridge) := by
  simp [targetHistory]

/-- Injective epoch mapping makes repeated-epoch rejection agree with reserved tweaks. -/
theorem used_iff_tweakReserved [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) (ep : E) :
    TargetCollisionResistance.used transcript ep = true ↔
      TweakReserved Prod.fst (targetHistory bridge transcript) (bridge.epochToTweak ep) := by
  simp [TargetCollisionResistance.used, TweakReserved, targetHistory, targetRecord,
    bridge.epochToTweak_injective.eq_iff]

/-- The two challenge handlers reject the same full or reused query. -/
theorem rejected_iff_target_rejected [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) (ep : E) :
    TargetCollisionResistance.rejected p transcript ep = true ↔
      p ≤ (targetHistory bridge transcript).length ∨
        TweakReserved Prod.fst (targetHistory bridge transcript) (bridge.epochToTweak ep) := by
  simp [TargetCollisionResistance.rejected, targetHistory_length,
    used_iff_tweakReserved bridge transcript ep]

/-- The source and target retry loops make the same draws. Only the returned hash word is mapped
to the full encoding word; returned exhaustion and missing mass are preserved by `map`. -/
theorem retry_eq_resample [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (pp : PP) (msg : M) (ep : E) :
    bridge.enc.retry ($ᵗ R) pp msg ep K =
      (SM_DT_RTCR_resample (hashProblem bridge p K) pp (bridge.epochToTweak ep) msg K).map
        (Option.map fun pair => (bridge.word pair.1, pair.2)) := by
  let target := hashProblem bridge p K
  have aux : ∀ k, bridge.enc.retry ($ᵗ R) pp msg ep k =
      (SM_DT_RTCR_resample target pp (bridge.epochToTweak ep) msg k).map
        (Option.map fun pair => (bridge.word pair.1, pair.2)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [IncomparableEncoding.retry_succ, SM_DT_RTCR_resample_succ, target, hashProblem,
          bridge.encode_eq, PFunctor.FreeM.map_eq_map, map_bind, ih]
        congr 1
        funext r
        by_cases h : bridge.accepts (bridge.th.eval pp (bridge.epochToTweak ep) (msg, r)) = true
        · simp [h]
        · simp [h]
  exact aux K

/-- A returned successful retry has the full word of its underlying hash evaluation. -/
theorem word_eq_of_mem_retry [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (msg : M) (ep : E) (K : ℕ) (word : Codeword n radix) (r : R)
    (hreturned : some (word, r) ∈ support (bridge.enc.retry ($ᵗ R) pp msg ep K)) :
    word = bridge.word (bridge.th.eval pp (bridge.epochToTweak ep) (msg, r)) := by
  have hvalue := IncomparableEncoding.Retry.encode_eq_some_of_mem_retry
    bridge.enc ($ᵗ R) pp msg ep K word r hreturned
  rw [bridge.encode_eq] at hvalue
  split_ifs at hvalue
  exact Option.some.inj hvalue.symm

/-- The target index is the first source record that witnesses the submitted collision. If no
record witnesses it, the index is the out-of-range value `transcript.length`. -/
@[expose] def witnessIndex [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) : ℕ :=
  transcript.findIdx (witnesses bridge.enc pp collision)

/-- Every returned successful target word is the bridge's full word for the recorded hash output.
This is an invariant of the challenge simulation, not a property of arbitrary user data. -/
@[expose] def WellFormed (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) : Prop :=
  ∀ entry ∈ transcript, ∀ word r, entry.result = some (word, r) →
    word = bridge.word (bridge.th.eval pp (bridge.epochToTweak entry.epoch)
      (entry.message, r))

/-- A well-formed source collision names an SM-rTCR target at the same issue index. -/
theorem valid_implies_hash_collision [DecidableEq M] [DecidableEq R] [DecidableEq E]
    [DecidableEq Y]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) (hformed : WellFormed bridge pp transcript)
    (hwin : TargetCollisionResistance.valid bridge.enc pp transcript collision = true) :
    SM_DT_RTCR_IsCollision (hashProblem bridge p K) pp (targetHistory bridge transcript)
      (witnessIndex bridge pp transcript collision, collision.1, collision.2.1) = true := by
  have hexists := List.any_eq_true.mp hwin
  have hindex : witnessIndex bridge pp transcript collision < transcript.length :=
    List.findIdx_lt_length_of_exists hexists
  let entry := transcript[witnessIndex bridge pp transcript collision]
  have hwitness : witnesses bridge.enc pp collision entry = true :=
    List.findIdx_getElem (w := hindex)
  have hslot : (targetHistory bridge transcript)[witnessIndex bridge pp transcript collision]? =
      some (targetRecord bridge entry) := by
    rw [targetHistory_getElem?, List.getElem?_eq_getElem hindex]
    rfl
  cases hvalue : bridge.enc.encode pp collision.1 collision.2.1 collision.2.2 with
  | none => simp [witnesses, hvalue] at hwitness
  | some candidateWord =>
      cases hresult : entry.result with
      | none => simp [witnesses, hvalue, hresult] at hwitness
      | some result =>
          rcases result with ⟨targetWord, targetRandomizer⟩
          have hconditions : entry.epoch = collision.2.2 ∧
              targetWord = candidateWord ∧
              (entry.message, targetRandomizer) ≠ (collision.1, collision.2.1) := by
            simpa only [witnesses, hvalue, hresult, decide_eq_true_eq] using hwitness
          have hold := hformed entry (List.getElem_mem hindex) targetWord targetRandomizer hresult
          have hnew : candidateWord = bridge.word
              (bridge.th.eval pp (bridge.epochToTweak collision.2.2)
                (collision.1, collision.2.1)) := by
            rw [bridge.encode_eq] at hvalue
            split_ifs at hvalue; simp_all
          have hhash : bridge.th.eval pp (bridge.epochToTweak entry.epoch)
              (entry.message, targetRandomizer) =
              bridge.th.eval pp (bridge.epochToTweak entry.epoch)
                (collision.1, collision.2.1) := by
            apply bridge.word_injective
            rw [← hold, hconditions.2.1, hnew, hconditions.1]
          simp [SM_DT_RTCR_IsCollision, hslot, targetRecord, hashProblem,
            hresult, hconditions.2.2.symm, hhash]

end IncomparableEncoding.TargetCollisionReduction
