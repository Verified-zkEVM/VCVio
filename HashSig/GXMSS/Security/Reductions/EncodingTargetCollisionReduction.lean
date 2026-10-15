/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.Encoding
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTRTCR
public import VCVio.OracleComp.SimSemantics.StateT.Basic
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# A shared bridge from encoding target collisions to SM-DT-rTCR

The bridge keeps the source transcript's failed entries and issue order. Its target history is the
VCVio history with each epoch mapped to a tweak and each successful encoding record projected to
the randomizer used by the hash challenge. The same construction applies to a checksum word and a
target-sum word when their success and projection laws are supplied separately.
-/

public section

namespace GXMSS.Encoding.TargetCollisionReduction

open OracleComp OracleSpec TargetCollisionResistance TweakableHash

variable {PP M R E Tweak Y : Type} {n radix : ℕ}

/-- Data needed to compare the full encoding word with one tweakable-hash output. The success law
includes returned failure, so the target-sum instance cannot silently register failed draws. -/
structure Bridge (PP M R E Tweak Y : Type) (n radix : ℕ) where
  /-- The encoding whose target collisions are reduced to hash collisions. -/
  enc : IncomparableEncoding PP M R E n radix
  /-- The tweakable hash evaluated on message/randomizer pairs. -/
  th : TweakableHash PP Tweak (M × R) Y
  /-- The hash tweak assigned to each epoch. -/
  epochToTweak : E → Tweak
  epochToTweak_injective : Function.Injective epochToTweak
  /-- The predicate deciding which hash outputs yield successful encodings. -/
  accepts : Y → Bool
  /-- The full codeword represented by a hash output. -/
  word : Y → Codeword n radix
  word_injective : Function.Injective word
  value_eq : ∀ pp msg r ep,
    enc.value pp msg r ep =
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

/-- The VCVio target game uses the hash word and the encoding success predicate. -/
@[expose] def hashProblem (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) :
    SM_DT_RTCR_Problem PP Tweak M R Y where
  th := bridge.th
  prop := bridge.accepts
  numTargets := p
  numRetries := K

/-- VCVio's canonical finite randomizer draw is uniform and lossless in the native runtime. -/
theorem canonicalRandomizer_uniform [Fintype R] [SampleableType R] :
    UniformSampler ProbCompRuntime.probComp ($ᵗ R) :=
  uniformSampler_uniformSample R

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
        simp only [IncomparableEncoding.retry, SM_DT_RTCR_resample, target, hashProblem,
          bridge.value_eq, PFunctor.FreeM.map_eq_map, map_bind, ih]
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
  have hvalue := IncomparableEncoding.Retry.value_eq_some_of_mem_retry
    bridge.enc ($ᵗ R) pp msg ep K word r hreturned
  rw [bridge.value_eq] at hvalue
  split_ifs at hvalue
  exact Option.some.inj hvalue.symm

/-- This is the exact source winning predicate for one transcript entry. -/
@[expose] def witnesses (bridge : Bridge PP M R E Tweak Y n radix)
    (pp : PP) (collision : M × R × E)
    [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (entry : TargetCollisionResistance.Record M R E n radix) : Bool :=
  let candidate := collision.2
  match bridge.enc.value pp collision.1 candidate.1 candidate.2, entry.result with
  | some word, some (target, r) =>
      decide (entry.epoch = candidate.2 ∧ target = word ∧
        (entry.message, r) ≠ (collision.1, candidate.1))
  | _, _ => false

/-- The target index is the first source record that witnesses the submitted collision. If no
record witnesses it, the index is the out-of-range value `transcript.length`. -/
@[expose] def witnessIndex [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) : ℕ :=
  transcript.findIdx (witnesses bridge pp collision)

/-- The source win test is precisely the existence of an entry selected by the index search. -/
theorem valid_iff_witness [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) :
    TargetCollisionResistance.valid bridge.enc pp transcript collision = true ↔
      ∃ entry ∈ transcript, witnesses bridge pp collision entry = true := by
  unfold TargetCollisionResistance.valid
  cases h : bridge.enc.value pp collision.1 collision.2.1 collision.2.2 with
  | none => simp [witnesses, h]
  | some word =>
      simp only [h, List.any_eq_true]
      constructor
      · rintro ⟨entry, hmem, hw⟩
        refine ⟨entry, hmem, ?_⟩
        cases hresult : entry.result with
        | none => simp [hresult] at hw
        | some result => simpa [witnesses, h, hresult] using hw
      · rintro ⟨entry, hmem, hw⟩
        refine ⟨entry, hmem, ?_⟩
        cases hresult : entry.result with
        | none => simp [witnesses, h, hresult] at hw
        | some result => simpa [witnesses, h, hresult] using hw

/-- Every returned successful target word is the bridge's full word for the recorded hash output.
This is an invariant of the challenge simulation, not a property of arbitrary user data. -/
@[expose] def WellFormed (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix) : Prop :=
  ∀ entry ∈ transcript, ∀ word r, entry.result = some (word, r) →
    word = bridge.word (bridge.th.eval pp (bridge.epochToTweak entry.epoch)
      (entry.message, r))

/-- A well-formed source collision names a VCVio target at the same issue index. -/
theorem valid_implies_hash_collision [DecidableEq M] [DecidableEq R] [DecidableEq E]
    [DecidableEq Y]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (transcript : TargetCollisionResistance.Transcript M R E n radix)
    (collision : M × R × E) (hformed : WellFormed bridge pp transcript)
    (hwin : TargetCollisionResistance.valid bridge.enc pp transcript collision = true) :
    SM_DT_RTCR_IsCollision (hashProblem bridge p K) pp (targetHistory bridge transcript)
      (witnessIndex bridge pp transcript collision, collision.1, collision.2.1) = true := by
  have hexists := (valid_iff_witness bridge pp transcript collision).mp hwin
  have hindex : witnessIndex bridge pp transcript collision < transcript.length :=
    List.findIdx_lt_length_of_exists hexists
  let entry := transcript[witnessIndex bridge pp transcript collision]
  have hwitness : witnesses bridge pp collision entry = true :=
    List.findIdx_getElem (w := hindex)
  have hslot : (targetHistory bridge transcript)[witnessIndex bridge pp transcript collision]? =
      some (targetRecord bridge entry) := by
    rw [targetHistory_getElem?, List.getElem?_eq_getElem hindex]
    rfl
  cases hvalue : bridge.enc.value pp collision.1 collision.2.1 collision.2.2 with
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
            rw [bridge.value_eq] at hvalue
            split_ifs at hvalue; simp_all
          have hhash : bridge.th.eval pp (bridge.epochToTweak entry.epoch)
              (entry.message, targetRandomizer) =
              bridge.th.eval pp (bridge.epochToTweak entry.epoch)
                (collision.1, collision.2.1) := by
            apply bridge.word_injective
            rw [← hold, hconditions.2.1, hnew, hconditions.1]
          simp [SM_DT_RTCR_IsCollision, hslot, targetRecord, hashProblem,
            hresult, hconditions.2.2.symm, hhash]

/-- Each source challenge query is forwarded to the corresponding hash challenge and its returned
word is lifted. Recording through `finish` retains rejected queries and exhausted entries. -/
@[expose] def challengeLift [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ) :
    QueryImpl (TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) := fun q => do
  let targetAnswer ← liftM ((unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y).query
    (.inr (bridge.epochToTweak q.2, q.1)))
  let answer := targetAnswer.map fun pair => (bridge.word pair.1, pair.2)
  modify fun s => (TargetCollisionResistance.finish p s q.1 q.2 answer).2
  return answer

/-- Private random queries pass through unchanged; challenge queries use `challengeLift`. -/
@[expose] def liftedOracles [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p : ℕ) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) :=
  (QueryImpl.ofLift unifSpec
    (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))).liftTarget
      (StateT (TargetCollisionResistance.Transcript M R E n radix)
        (OracleComp (unifSpec + SM_DT_RTCR_challengeSpec Tweak M R Y))) +
    challengeLift bridge p

/-- Flattening the nested source and hash challenge handlers exposes both ordered histories. -/
@[expose] noncomputable def coupledOracles [DecidableEq E] [DecidableEq Tweak]
    [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  ((SM_DT_RTCR_oracles (hashProblem bridge p K) pp).mapStateTBase
    (liftedOracles bridge p)).flattenStateT

/-- A direct coupled source handler mirrors the encoding challenge and records the corresponding
hash target. The second history remains a projection of the first. -/
@[expose] def sourceCoupledChallenge [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) := fun q => do
  let state ← get
  let transcript := state.1
  if TargetCollisionResistance.rejected p transcript q.2 then return none
  else
    let answer ← ((bridge.enc.retry ($ᵗ R) pp q.1 q.2 K :
      ProbComp (Option (Codeword n radix × R))) :
      StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp (Option (Codeword n radix × R)))
    let entry : TargetCollisionResistance.Record M R E n radix := ⟨q.2, q.1, answer⟩
    set (transcript ++ [entry], state.2 ++ [targetRecord bridge entry])
    return answer

/-- Private random draws have the same meaning in the direct coupled source game. -/
@[expose] def sourceCoupledOracles [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP) :
    QueryImpl (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix)
      (StateT (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) ProbComp) +
    sourceCoupledChallenge bridge p K pp

/-- The source record word and hash history agree with the pinned target game. -/
@[expose] def CoupledInv (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) : Prop :=
  state.2 = targetHistory bridge state.1 ∧ WellFormed bridge pp state.1

/-- The two histories start empty and agree. -/
theorem coupledInv_empty (bridge : Bridge PP M R E Tweak Y n radix) (pp : PP) :
    CoupledInv bridge pp ([], []) := by
  constructor
  · rfl
  · simp [WellFormed]

/-- Under the history relation, one source query and its hash simulation have identical
returned values and next states. -/
theorem coupledOracles_eq_sourceCoupled_of_inv
    [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state) :
    (coupledOracles bridge p K pp q).run state =
      (sourceCoupledOracles bridge p K pp q).run state := by
  cases q with
  | inl random =>
      have hsimple :
          (fun answer => (answer.1, state.1, answer.2)) <$>
            (SM_DT_RTCR_oracles (hashProblem bridge p K) pp (.inl random)).run state.2 =
          (fun answer => (answer, state)) <$> (unifSpec.query random : ProbComp _) := by
        simp [SM_DT_RTCR_oracles, QueryImpl.ofLift_eq_id']
      change (fun answer => (answer.1, state.1, answer.2)) <$>
          (SM_DT_RTCR_oracles (hashProblem bridge p K) pp (.inl random)).run state.2 =
        (fun answer => (answer, state)) <$> (unifSpec.query random : ProbComp _)
      exact hsimple
  | inr query =>
      rcases query with ⟨msg, ep⟩
      have hreject :
          (p ≤ state.2.length ∨
            TweakReserved Prod.fst state.2 (bridge.epochToTweak ep)) ↔
            TargetCollisionResistance.rejected p state.1 ep = true := by
        rw [hinv.1, ← rejected_iff_target_rejected bridge p state.1 ep]
      by_cases h : TargetCollisionResistance.rejected p state.1 ep = true
      · have ht := hreject.mpr h
        simp [coupledOracles, liftedOracles, challengeLift, sourceCoupledOracles,
          sourceCoupledChallenge, SM_DT_RTCR_oracles, SM_DT_RTCR_challengeOracle,
          QueryImpl.mapStateTBase, QueryImpl.flattenStateT, h, ht,
          TargetCollisionResistance.finish, hashProblem]
      · have ht : ¬ (p ≤ state.2.length ∨
            TweakReserved Prod.fst state.2 (bridge.epochToTweak ep)) := by
          intro ht
          exact h (hreject.mp ht)
        have hsimple :
            (fun answer : Option (Y × R) =>
              (answer.map fun pair => (bridge.word pair.1, pair.2),
                state.1 ++ [⟨ep, msg, answer.map fun pair => (bridge.word pair.1, pair.2)⟩],
                state.2 ++ [(bridge.epochToTweak ep, msg, answer.map Prod.snd)])) <$>
              SM_DT_RTCR_resample (hashProblem bridge p K) pp
                (bridge.epochToTweak ep) msg K =
            (fun answer : Option (Codeword n radix × R) =>
              (answer, state.1 ++ [⟨ep, msg, answer⟩],
                state.2 ++ [targetRecord bridge ⟨ep, msg, answer⟩])) <$>
              bridge.enc.retry ($ᵗ R) pp msg ep K := by
          rw [retry_eq_resample bridge p K pp msg ep]
          simp only [PFunctor.FreeM.map_eq_map, Functor.map_map,
            hashProblem, targetRecord]
          simp [Option.map_map, Function.comp_def]
        simpa [coupledOracles, liftedOracles, challengeLift, sourceCoupledOracles,
          sourceCoupledChallenge, SM_DT_RTCR_oracles, SM_DT_RTCR_challengeOracle,
          QueryImpl.mapStateTBase, QueryImpl.flattenStateT, h, ht,
          TargetCollisionResistance.finish, hashProblem] using hsimple

/-- The direct challenge handler maintains history alignment and full-word correctness on every
returned path. Missing execution mass contributes no path and is left unchanged. -/
theorem sourceCoupledChallenge_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : M × E)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : Option (Codeword n radix × R) ×
      (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((sourceCoupledChallenge bridge p K pp q).run state)) :
    CoupledInv bridge pp out.2 := by
  rcases q with ⟨msg, ep⟩
  by_cases hreject : TargetCollisionResistance.rejected p state.1 ep = true
  · have hrun : (sourceCoupledChallenge bridge p K pp (msg, ep)).run state =
        pure (none, state) := by simp [sourceCoupledChallenge, hreject]
    rw [hrun] at hout
    have heq := (mem_support_pure_iff _ _).mp hout
    subst out
    exact hinv
  · have hrun : (sourceCoupledChallenge bridge p K pp (msg, ep)).run state =
        bridge.enc.retry ($ᵗ R) pp msg ep K >>= fun answer =>
          pure (answer, (state.1 ++ [⟨ep, msg, answer⟩],
            state.2 ++ [targetRecord bridge ⟨ep, msg, answer⟩])) := by
      simp [sourceCoupledChallenge, hreject]
    rw [hrun] at hout
    obtain ⟨answer, hanswer, hreturned⟩ := (mem_support_bind_iff _ _ _).mp hout
    have heq := (mem_support_pure_iff _ _).mp hreturned
    subst out
    constructor
    · simp [hinv.1, targetHistory]
    · intro entry hmem word r hresult
      rcases List.mem_append.mp hmem with hold | hnew
      · exact hinv.2 entry hold word r hresult
      · have hentry : entry = (⟨ep, msg, answer⟩ :
            TargetCollisionResistance.Record M R E n radix) := by
          simpa using hnew
        subst entry
        have hanswer' : answer = some (word, r) := hresult
        subst answer
        exact word_eq_of_mem_retry bridge pp msg ep K word r hanswer

/-- Ordinary random draws leave both histories alone; the challenge case uses the preceding
invariant lemma. -/
theorem sourceCoupledOracles_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Range q ×
      (TargetCollisionResistance.Transcript M R E n radix ×
        SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((sourceCoupledOracles bridge p K pp q).run state)) :
    CoupledInv bridge pp out.2 := by
  cases q with
  | inl random =>
      have hrun : (sourceCoupledOracles bridge p K pp (.inl random)).run state =
          (fun answer => (answer, state)) <$> (unifSpec.query random : ProbComp _) := by
        rfl
      rw [hrun] at hout
      simp only [support_map, Set.mem_image] at hout
      obtain ⟨answer, _, heq⟩ := hout
      subst out
      exact hinv
  | inr query =>
      exact sourceCoupledChallenge_preserves_inv bridge p K pp query state hinv out hout

/-- Adaptive source and target simulations agree on the full paired state from an aligned
starting point. The theorem is an equality of partial computations, so returned failure and
unreturned mass are retained. -/
theorem coupled_run_eq_source [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state) :
    (simulateQ (coupledOracles bridge p K pp) program).run state =
      (simulateQ (sourceCoupledOracles bridge p K pp) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map, StateT.run_bind]
      rw [coupledOracles_eq_sourceCoupled_of_inv bridge p K pp q state hinv]
      apply bind_congr_of_forall_mem_support
      intro output houtput
      exact ih output.1 output.2
        (sourceCoupledOracles_preserves_inv bridge p K pp q state hinv output houtput)

/-- Forgetting the target history gives exactly the source challenge handler. -/
theorem sourceCoupledOracles_proj [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    (q : (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix).Domain)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) :
    Prod.map id Prod.fst <$> (sourceCoupledOracles bridge p K pp q).run state =
      (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp q).run state.1 := by
  cases q with
  | inl random =>
      simp [sourceCoupledOracles, TargetCollisionResistance.oracles]
  | inr query =>
      rcases query with ⟨msg, ep⟩
      by_cases h : TargetCollisionResistance.rejected p state.1 ep = true
      · simp [sourceCoupledOracles, sourceCoupledChallenge,
          TargetCollisionResistance.oracles, TargetCollisionResistance.challengeOracle,
          encodingProblem, h]
      · simp [sourceCoupledOracles, sourceCoupledChallenge,
          TargetCollisionResistance.oracles, TargetCollisionResistance.challengeOracle,
          encodingProblem, h, TargetCollisionResistance.finish]

/-- Source simulation is the first projection of the direct paired simulation. -/
theorem sourceCoupled_run_proj [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) :
    Prod.map id Prod.fst <$> (simulateQ (sourceCoupledOracles bridge p K pp) program).run state =
      (simulateQ (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp)
        program).run state.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (sourceCoupledOracles bridge p K pp)
    (TargetCollisionResistance.oracles (encodingProblem bridge p K) pp)
    Prod.fst (sourceCoupledOracles_proj bridge p K pp) program state

/-- Every returned path of an adaptive source adversary retains the coupled history invariant. -/
theorem sourceCoupled_run_preserves_inv [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α)
    (state : TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R) (hinv : CoupledInv bridge pp state)
    (out : α × (TargetCollisionResistance.Transcript M R E n radix ×
      SM_DT_RTCR_State Tweak M R))
    (hout : out ∈ support ((simulateQ (sourceCoupledOracles bridge p K pp) program).run state)) :
    CoupledInv bridge pp out.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      have heq := (mem_support_pure_iff _ _).mp hout
      subst out
      exact hinv
  | query_bind q next ih =>
      have hbind : out ∈ support
          (((sourceCoupledOracles bridge p K pp q).run state) >>= fun result =>
            (simulateQ (sourceCoupledOracles bridge p K pp) (next result.1)).run result.2) := by
        simpa [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, StateT.run_bind] using hout
      obtain ⟨result, hstep, hrest⟩ := (mem_support_bind_iff _ _ _).mp hbind
      exact ih result.1 result.2
        (sourceCoupledOracles_preserves_inv bridge p K pp q state hinv result hstep)
        hrest

/-- Flattening the hash game around the source adversary yields the same coupled program from
empty histories. This equality includes both histories and every returned failure. -/
theorem nested_run_eq_source [DecidableEq E] [DecidableEq Tweak] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ) (pp : PP)
    {α : Type}
    (program : OracleComp (unifSpec + TargetCollisionResistance.challengeSpec M R E n radix) α) :
    (simulateQ (SM_DT_RTCR_oracles (hashProblem bridge p K) pp)
      ((simulateQ (liftedOracles bridge p) program).run [])).run
        ([] : SM_DT_RTCR_State Tweak M R) =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceCoupledOracles bridge p K pp) program).run ([], []) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (coupledOracles bridge p K pp) program).run ([], []) = _
  rw [coupled_run_eq_source bridge p K pp program ([], [])
    (coupledInv_empty bridge pp)]

/-- The hash adversary runs the source adversary under the translated challenge oracle, then
reports the first successful source target's index and the same candidate pair. -/
@[expose] def reduction [SampleableType R] [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    SM_DT_RTCR_Adversary (hashProblem bridge p K) where
  main pp := do
    let (collision, transcript) ←
      (simulateQ (liftedOracles bridge p) (source.find pp)).run []
    return (witnessIndex bridge pp transcript collision, collision.1, collision.2.1)


/-- The common returned sample keeps both ordered histories without conditioning on termination. -/
@[expose] def runCoupled [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    ProbComp (PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) := do
  let pp ← bridge.th.seedGen
  let output ← (simulateQ (sourceCoupledOracles bridge p K pp) (source.find pp)).run ([], [])
  return (pp, output)

/-- Boolean source observation on the common returned sample. -/
@[expose] def sourceObservation [DecidableEq M] [DecidableEq R] [DecidableEq E]
    (bridge : Bridge PP M R E Tweak Y n radix)
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) : Bool :=
  let (pp, output) := result
  let (collision, state) := output
  TargetCollisionResistance.valid bridge.enc pp state.1 collision

/-- Boolean VCVio observation on the same sample and first witnessing index. -/
@[expose] def targetObservation [DecidableEq M] [DecidableEq R] [DecidableEq E]
    [DecidableEq Y]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R))) : Bool :=
  let (pp, output) := result
  let (collision, state) := output
  SM_DT_RTCR_IsCollision (hashProblem bridge p K) pp state.2
    (witnessIndex bridge pp state.1 collision, collision.1, collision.2.1)

/-- Every returned source win is a target win at the selected issue index. False results and
missing mass are unrestricted, which is sufficient for the native measure inequality. -/
theorem sourceObservation_implies_targetObservation
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Y]
    [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K))
    (result : PP × ((M × R × E) ×
      (TargetCollisionResistance.Transcript M R E n radix × SM_DT_RTCR_State Tweak M R)))
    (hresult : result ∈ support (runCoupled bridge p K source))
    (hwin : sourceObservation bridge result = true) :
    targetObservation bridge p K result = true := by
  unfold runCoupled at hresult
  obtain ⟨pp, _, hrest⟩ := support_bind_exists hresult
  obtain ⟨output, hrun, hpure⟩ := support_bind_exists hrest
  have heq := (mem_support_pure_iff _ _).mp hpure
  subst result
  have hinv := sourceCoupled_run_preserves_inv bridge p K pp
    (source.find pp) ([], []) (coupledInv_empty bridge pp) output hrun
  have htarget := valid_implies_hash_collision bridge p K pp output.2.1 output.1
    hinv.2 (by simpa [sourceObservation] using hwin)
  simpa [targetObservation, hinv.1] using htarget

/-- The source Boolean experiment is the first-history observation of the common sample. -/
theorem source_experiment_eq_coupled
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    TargetCollisionResistance.experiment source =
      sourceObservation bridge <$> runCoupled bridge p K source := by
  unfold TargetCollisionResistance.experiment runCoupled sourceObservation
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  apply congrArg (fun (f : PP → ProbComp Bool) => bridge.th.seedGen >>= f)
  funext pp
  rw [← sourceCoupled_run_proj bridge p K pp (source.find pp) ([], [])]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

/-- The VCVio experiment of the constructed adversary observes the same common sample. -/
theorem target_experiment_eq_coupled
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    SM_DT_RTCR_Experiment (reduction bridge p K source) =
      targetObservation bridge p K <$> runCoupled bridge p K source := by
  unfold SM_DT_RTCR_Experiment reduction runCoupled targetObservation
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind,
    map_eq_bind_pure_comp, Function.comp_def]
  apply congrArg (fun (f : PP → ProbComp Bool) => bridge.th.seedGen >>= f)
  funext pp
  rw [nested_run_eq_source bridge p K pp (source.find pp)]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rfl

/-- The unconditional native returned-mass bound for any capacities, including zero. Both games
sample the same public seed and use the canonical randomizer sampler; no mass is normalized. -/
theorem advantage_le_hash
    [DecidableEq M] [DecidableEq R] [DecidableEq E] [DecidableEq Tweak]
    [DecidableEq Y] [SampleableType R]
    (bridge : Bridge PP M R E Tweak Y n radix) (p K : ℕ)
    (source : TargetCollisionResistance.Adversary (encodingProblem bridge p K)) :
    TargetCollisionResistance.advantage source ≤
      SM_DT_RTCR_Advantage (reduction bridge p K source) := by
  unfold TargetCollisionResistance.advantage TargetCollisionResistance.outputMeasure
    SM_DT_RTCR_Advantage
  rw [source_experiment_eq_coupled bridge p K source,
    target_experiment_eq_coupled bridge p K source]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (runCoupled bridge p K source)
    (fun result => pure (sourceObservation bridge result))
    (fun result => pure (targetObservation bridge p K result))
    (measurableSet_singleton true)
  intro result hresult
  by_cases hwin : sourceObservation bridge result = true
  · have htarget := sourceObservation_implies_targetObservation
      bridge p K source result hresult hwin
    simp [hwin, htarget]
  · have hlose : sourceObservation bridge result = false := by
      cases h : sourceObservation bridge result <;> simp_all
    simp [hlose]


end GXMSS.Encoding.TargetCollisionReduction
