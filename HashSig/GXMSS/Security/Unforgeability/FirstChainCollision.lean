/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability.MerkleCollision
import all HashSig.GXMSS.Security.Unforgeability.MerkleCollision
import all HashSig.GXMSS.Security.ReductionGames.SourceGames
import all HashSig.GXMSS.Security.ReductionGames.GuessingGames
import all HashSig.GXMSS.Security.ReductionGames.CollisionReductions
import all HashSig.GXMSS.Security.ReductionGames.SplicedChain
import all HashSig.GXMSS.Security.ReductionGames.ChainHybrid
import all HashSig.GXMSS.Security.ReductionGames.JointReductions

/-!
# First chain target collision bound

The successful-record Game 2 to Game 3 difference is bounded using the fixed first-chain
target-collision reduction and a coupled returned-output measure.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-! ## First-chain successful-record hop -/

/-- The exact candidate returned by the fixed first-chain reduction after source interaction. -/
private def firstChainCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (state : ReductionGames.TCRKeyState PP T X H h v) (pp : PP)
    (out : ReductionGames.Result PP H M R h v) : ℕ × X :=
  let fallback := (0, hash.digestInput state.fallback)
  let epoch := out.forgery.1
  let forgedMessage := out.forgery.2.1
  let forgedSignature := out.forgery.2.2
  match out.history epoch with
  | some (msg, some signature) =>
    match enc.value pp msg signature.randomizer epoch,
      enc.value pp forgedMessage forgedSignature.randomizer epoch with
    | some honestWord, some forgedWord =>
      if honestWord = forgedWord then
        match Security.findUnequalCoordinate signature.ots forgedSignature.ots with
        | none => fallback
        | some i =>
          match hash.findChainCollision pp epoch i (honestWord i)
              (2 ^ w - 1 - (honestWord i).val) (signature.ots i)
              (forgedSignature.ots i) with
          | none => fallback
          | some d =>
            let tweak := hash.chainTweak (epoch, i,
              ⟨(honestWord i).val + d.val, by omega⟩)
            let first := hash.digestInput
              (hash.chain pp epoch i (honestWord i) d (signature.ots i))
            let second := hash.digestInput
              (hash.chain pp epoch i (honestWord i) d (forgedSignature.ots i))
            (ReductionGames.registeredIndex state.targets tweak first, second)
      else fallback
    | _, _ => fallback
  | _ => fallback

private def firstChainCandidateWins [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (history : List (T × X)) (candidate : ℕ × X) : Bool :=
  match history[candidate.1]? with
  | none => false
  | some (t, first) =>
    decide (candidate.2 ≠ first ∧
      (HashInstance.thf hash).eval pp t candidate.2 =
        (HashInstance.thf hash).eval pp t first)

private theorem firstChain_pureDecision [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (history : List (T × X)) (j : ℕ) (second : X) :
    (match history[j]? with
    | none => pure false
    | some (t, first) => pure (decide (second ≠ first ∧
        (ReductionGames.chainTCRProblem hash).th.eval pp t second =
          (ReductionGames.chainTCRProblem hash).th.eval pp t first)) : ProbComp Bool) =
      pure (match history[j]? with
      | none => false
      | some (t, first) =>
        !decide (second = first) &&
          decide (hash.thf.eval pp t second = hash.thf.eval pp t first)) := by
  cases hlookup : history[j]? with
  | none => simp
  | some pair =>
    rcases pair with ⟨t, first⟩
    simp only [ReductionGames.chainTCRProblem, SM_DT_TCR_Problem.standalone]
    congr 1
    exact tcrDecision_eq second first
      (hash.thf.eval pp t second = hash.thf.eval pp t first)

/-- The first unequal OTS coordinate yields a registered honest-first collision target. -/
private theorem firstChain_registeredTarget_wins
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) (ep : Fin (2 ^ h))
    (word : Codeword v (2 ^ w)) (honestOTS forgedOTS : Fin v → H)
    (hhonest : ∀ i, honestOTS i =
      hash.chain pp ep i 0 (word i) (starts ep i))
    (hend : ∀ i, hash.chain pp ep i (word i)
      (2 ^ w - 1 - (word i).val) (honestOTS i) =
        hash.chain pp ep i (word i)
          (2 ^ w - 1 - (word i).val) (forgedOTS i))
    (hne : honestOTS ≠ forgedOTS) :
    ∃ i : Fin v, ∃ d : Fin (2 ^ w - 1 - (word i).val),
      Security.findUnequalCoordinate honestOTS forgedOTS = some i ∧
      hash.findChainCollision pp ep i (word i)
        (2 ^ w - 1 - (word i).val) (honestOTS i) (forgedOTS i) = some d ∧
      let tweak := hash.chainTweak (ep, i, ⟨(word i).val + d.val, by omega⟩)
      let first := hash.digestInput (hash.chain pp ep i (word i) d (honestOTS i))
      let second := hash.digestInput (hash.chain pp ep i (word i) d (forgedOTS i))
      firstChainCandidateWins hash pp (ReductionGames.endpointTargets hash pp starts)
        (ReductionGames.registeredIndex
          (ReductionGames.endpointTargets hash pp starts) tweak first, second) = true := by
  have hisome := Security.findUnequalCoordinate_isSome honestOTS forgedOTS hne
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hisome
  have hcoord := Security.findUnequalCoordinate_sound honestOTS forgedOTS hi
  have hdSome := hash.findChainCollision_isSome pp ep i (word i)
    (2 ^ w - 1 - (word i).val) (honestOTS i) (forgedOTS i) hcoord (hend i)
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hdSome
  refine ⟨i, d, hi, hd, ?_⟩
  let j : Fin (2 ^ w - 1) := ⟨(word i).val + d.val, by omega⟩
  have hprefix : hash.chain pp ep i (word i) d (honestOTS i) =
      hash.chain pp ep i 0 j.val (starts ep i) := by
    rw [hhonest i]
    simpa [j] using (hash.chain_add pp ep i 0 (word i).val d.val (starts ep i)).symm
  have hsound := hash.findChainCollision_hash_sound pp ep i (word i)
    (2 ^ w - 1 - (word i).val) (honestOTS i) (forgedOTS i)
    (by omega) hd
  dsimp only [Security.HashCollision.Sound] at hsound
  rw [hprefix] at hsound
  have hspec := ReductionGames.chainTarget_registeredIndex_spec hash pp starts
    ep i j (ReductionGames.chainTCRProblem hash).numTargets (by
      simpa using ReductionGames.chainProblem_capacity hash)
  obtain ⟨_, hlookup, _⟩ := hspec
  dsimp [firstChainCandidateWins]
  rw [hprefix]
  simpa [j, hlookup, Security.HashCollision.Sound] using
    (show decide
      (hash.digestInput (hash.chain pp ep i (word i) d (forgedOTS i)) ≠
        hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)) ∧
       hash.thf.eval pp (hash.chainTweak (ep, i, j))
         (hash.digestInput (hash.chain pp ep i (word i) d (forgedOTS i))) =
       hash.thf.eval pp (hash.chainTweak (ep, i, j))
         (hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)))) = true from
      decide_eq_true ⟨hsound.1.symm, hsound.2.symm⟩)

/-- A returned Game 2 win removed by Game 3 makes the fixed chain candidate win. -/
private theorem firstChainCandidateWins_of_difference
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v)
    (pp : PP) (starts : Fin (2 ^ h) → Fin v → H) (fallback : H)
    (forgery : SyncSignatureUnforgeability.Forgery (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (history : SyncSignatureUnforgeability.History (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v))
    (hrun : (⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
      forgery, history⟩ : ReductionGames.Result PP H M R h v) ∈
        support (ReductionGames.runWithKeys hash enc K adv
          (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2))
    (hdiff : ReductionGames.successfulFirstChainDifference hash enc K
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩ = true) :
    let registered := ReductionGames.endpointTargets hash pp starts
    let state : ReductionGames.TCRKeyState PP T X H h v :=
      ⟨starts, GXMSS.endpoints hash pp starts, fallback, registered, fallback⟩
    let out : ReductionGames.Result PP H M R h v :=
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩
    firstChainCandidateWins hash pp registered (firstChainCandidate hash enc state pp out) =
      true := by
  let out : ReductionGames.Result PP H M R h v :=
    ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
      forgery, history⟩
  let ep := forgery.1
  let forgedSignature := forgery.2.2
  change ReductionGames.successfulFirstChainDifference hash enc K out = true at hdiff
  cases hs : ReductionGames.forgedEpochSource out with
  | unused =>
    simp only [ReductionGames.successfulFirstChainDifference, hs,
      Bool.and_false, Bool.false_eq_true] at hdiff
  | failedConsumed msg =>
    simp only [ReductionGames.successfulFirstChainDifference, hs,
      Bool.and_false, Bool.false_eq_true] at hdiff
  | successful msg sig =>
    have hrecord := ReductionGames.history_of_successful_source out msg sig hs
    change history ep = some (msg, some sig) at hrecord
    obtain ⟨wr, hsig, hword⟩ :=
      ReductionGames.runWithKeys_successful_record_signature hash enc K adv
        (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hrun ep msg sig
        hrecord
    have hsplit : ReductionGames.gameTwoObservation hash enc K out = true ∧
        (!ReductionGames.gameThreeObservation hash enc K out) = true := by
      simpa only [ReductionGames.successfulFirstChainDifference, hs,
        Bool.and_true, Bool.and_eq_true] using hdiff
    have htwo := hsplit.1
    have hthree : ReductionGames.gameThreeObservation hash enc K out = false := by
      cases h : ReductionGames.gameThreeObservation hash enc K out <;>
        simp [h] at hsplit ⊢
    have hcheck := hthree
    simp only [ReductionGames.gameThreeObservation, hs, htwo,
      Bool.true_and] at hcheck
    have hnot : ¬ ((msg, sig.randomizer) ≠
        (forgery.2.1, forgedSignature.randomizer) ∨ sig.ots = forgedSignature.ots) :=
      of_decide_eq_false hcheck
    have hpair : (msg, sig.randomizer) =
        (forgery.2.1, forgedSignature.randomizer) :=
      not_ne_iff.mp (not_or.mp hnot).1
    have hots : sig.ots ≠ forgedSignature.ots := (not_or.mp hnot).2
    have hhonestWord : enc.value pp msg sig.randomizer ep = some wr.1 := by
      simpa [out, hsig, GXMSS.keys, GXMSS.signatureOfWord] using hword
    have hforgedWord : enc.value pp forgery.2.1 forgedSignature.randomizer ep =
        some wr.1 := by
      have hm : msg = forgery.2.1 := congrArg Prod.fst hpair
      have hr : sig.randomizer = forgedSignature.randomizer := congrArg Prod.snd hpair
      simpa [← hm, ← hr] using hhonestWord
    have hwin : ReductionGames.gameOneObservation hash enc K out = true := by
      have h := htwo
      simp only [ReductionGames.gameTwoObservation, Bool.and_eq_true] at h
      exact h.1
    have hleaf := hwin
    simp only [ReductionGames.gameOneObservation, Bool.and_eq_true] at hleaf
    have hleaf' := hleaf.2
    have hleafValue : ReductionGames.forgedLeaf? hash enc out =
        some (fun i => hash.chain pp ep i (wr.1 i)
          (2 ^ w - 1 - (wr.1 i).val) (forgedSignature.ots i)) := by
      simp [ReductionGames.forgedLeaf?, out, ep, forgedSignature,
        GXMSS.keys, hforgedWord]
    rw [hleafValue] at hleaf'
    have hendpoint : GXMSS.endpoints hash pp starts ep =
        fun i => hash.chain pp ep i (wr.1 i)
          (2 ^ w - 1 - (wr.1 i).val) (forgedSignature.ots i) := by
      have hp := congrArg Prod.fst (of_decide_eq_true hleaf')
      simpa [out, GXMSS.keys] using hp
    have hhonestOTS : ∀ i, sig.ots i =
        hash.chain pp ep i 0 (wr.1 i) (starts ep i) := by
      intro i
      simp [hsig, GXMSS.signatureOfWord, GXMSS.keys]
    have hend : ∀ i, hash.chain pp ep i (wr.1 i)
        (2 ^ w - 1 - (wr.1 i).val) (sig.ots i) =
          hash.chain pp ep i (wr.1 i)
            (2 ^ w - 1 - (wr.1 i).val) (forgedSignature.ots i) := by
      intro i
      rw [hhonestOTS i, hash.chain_complete_digit]
      exact congrFun hendpoint i
    obtain ⟨i, d, hi, hd, hvalid⟩ := firstChain_registeredTarget_wins
      hash pp starts ep wr.1 sig.ots forgedSignature.ots hhonestOTS hend hots
    dsimp only
    simpa [firstChainCandidate, out, ep, forgedSignature, hrecord,
      hhonestWord, hforgedWord, hi, hd] using hvalid

private def firstChainCoupledProgram [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← (HashInstance.thf hash).seedGen
  let fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let endpoints := GXMSS.endpoints hash pp starts
  let registered := ReductionGames.endpointTargets hash pp starts
  let state : ReductionGames.TCRKeyState PP T X H h v :=
    ⟨starts, endpoints, fallback, registered, fallback⟩
  let (pk, sk) := GXMSS.keys hash pp starts
  let out ← ReductionGames.runWithKeys hash enc K adv pk sk
  pure (firstChainCandidateWins hash pp registered (firstChainCandidate hash enc state pp out))

private def firstChainCoupledDifferenceProgram [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) : ProbComp Bool := do
  let pp ← (HashInstance.thf hash).seedGen
  let _fallback ← ($ᵗ H : ProbComp H)
  let starts ← GXMSS.sampleStarts H h v
  let (pk, sk) := GXMSS.keys hash pp starts
  let out ← ReductionGames.runWithKeys hash enc K adv pk sk
  pure (ReductionGames.successfulFirstChainDifference hash enc K out)

private theorem firstChainCoupledDifference_evalDist_eq_source
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    𝒟[firstChainCoupledDifferenceProgram hash enc K adv] =
      𝒟[ReductionGames.successfulFirstChainDifference hash enc K <$>
        ReductionGames.sourceProgram hash enc K adv] := by
  unfold firstChainCoupledDifferenceProgram ReductionGames.sourceProgram GXMSS.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  simpa only [GXMSS.keys, bind_assoc, Function.comp_def] using
    (OracleComp.evalDist_bind_const ($ᵗ H : ProbComp H) (do
      let starts ← GXMSS.sampleStarts H h v
      let (pk, sk) := GXMSS.keys hash pp starts
      let out ← ReductionGames.runWithKeys hash enc K adv pk sk
      pure (ReductionGames.successfulFirstChainDifference hash enc K out)))

private theorem firstChainExperiment_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment
      (ReductionGames.firstChainTargetCollisionReduction hash enc K adv) =
        firstChainCoupledProgram hash enc K adv := by
  have hcap := ReductionGames.chainProblem_capacity hash
  unfold SM_DT_TCR_Experiment firstChainCoupledProgram
  simp only [ReductionGames.firstChainTargetCollisionReduction]
  have hsetup (pp : PP) :
      (simulateQ (SM_DT_TCR_oracles (ReductionGames.chainTCRProblem hash) pp)
        (ReductionGames.tcrChainSetup hash ((2 ^ h) * v * (2 ^ w)))).run ([], []) =
        (do
          let fallback ← ($ᵗ H : ProbComp H)
          let starts ← GXMSS.sampleStarts H h v
          let endpoints := GXMSS.endpoints hash pp starts
          let registered := ReductionGames.endpointTargets hash pp starts
          pure ((⟨starts, endpoints, fallback, registered, fallback⟩ :
            ReductionGames.TCRKeyState PP T X H h v), registered, ([] : List T))) := by
    change (simulateQ
      (SM_DT_TCR_oracles (SM_DT_TCR_Problem.standalone hash.thf
        ((2 ^ h) * v * (2 ^ w))) pp)
      (ReductionGames.tcrChainSetup hash ((2 ^ h) * v * (2 ^ w)))).run ([], []) = _
    exact ReductionGames.tcrChainSetup_run hash _ pp (by
      simpa only [ReductionGames.chainTCRProblem,
        SM_DT_TCR_Problem.standalone] using hcap)
  apply bind_congr
  intro pp
  rw [hsetup pp]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro fallback
  apply bind_congr
  intro starts
  apply bind_congr
  intro out
  cases hrecord : out.history out.forgery.1 with
  | none =>
    convert firstChain_pureDecision hash pp
      (ReductionGames.endpointTargets hash pp starts)
      0 (hash.digestInput fallback) using 1
    · rfl
    · simp [firstChainCandidate, firstChainCandidateWins, hrecord]
  | some entry =>
    rcases entry with ⟨msg, answer⟩
    cases answer with
    | none =>
      convert firstChain_pureDecision hash pp
        (ReductionGames.endpointTargets hash pp starts) _ _ using 1
      · rfl
      · simp [firstChainCandidate, firstChainCandidateWins, hrecord]
    | some signature =>
      cases hhonest : enc.value pp msg signature.randomizer out.forgery.1 with
      | none =>
        convert firstChain_pureDecision hash pp
          (ReductionGames.endpointTargets hash pp starts)
          0 (hash.digestInput fallback) using 1
        · simp only [hhonest, pure_bind]
          cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
          | none => rfl
          | some pair => cases pair; rfl
        · simp [firstChainCandidate, firstChainCandidateWins, hrecord, hhonest]
      | some honestWord =>
        cases hforged : enc.value pp out.forgery.2.1 out.forgery.2.2.randomizer
            out.forgery.1 with
        | none =>
          convert firstChain_pureDecision hash pp
            (ReductionGames.endpointTargets hash pp starts)
            0 (hash.digestInput fallback) using 1
          · simp only [hhonest, pure_bind]
            cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
            | none => rfl
            | some pair => cases pair; rfl
          · simp [firstChainCandidate, firstChainCandidateWins, hrecord,
              hhonest, hforged]
        | some forgedWord =>
          by_cases hword : honestWord = forgedWord
          · subst forgedWord
            cases hcoord : Security.findUnequalCoordinate signature.ots
                out.forgery.2.2.ots with
            | none =>
              convert firstChain_pureDecision hash pp
                (ReductionGames.endpointTargets hash pp starts)
                0 (hash.digestInput fallback) using 1
              · simp only [hhonest, hcoord, ↓reduceDIte, pure_bind]
                cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
                | none => rfl
                | some pair => cases pair; rfl
              · simp [firstChainCandidate, firstChainCandidateWins, hrecord,
                  hhonest, hforged, hcoord]
            | some i =>
              cases hcollision : hash.findChainCollision pp out.forgery.1 i
                  (honestWord i) (2 ^ w - 1 - (honestWord i).val)
                  (signature.ots i) (out.forgery.2.2.ots i) with
              | none =>
                convert firstChain_pureDecision hash pp
                  (ReductionGames.endpointTargets hash pp starts)
                  0 (hash.digestInput fallback) using 1
                · simp only [hhonest, hcoord, hcollision, ↓reduceDIte, pure_bind]
                  cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
                  | none => rfl
                  | some pair => cases pair; rfl
                · simp [firstChainCandidate, firstChainCandidateWins, hrecord,
                    hhonest, hforged, hcoord, hcollision]
              | some d =>
                simp only [hhonest, hcoord, hcollision, ↓reduceDIte, pure_bind]
                convert firstChain_pureDecision hash pp
                  (ReductionGames.endpointTargets hash pp starts) _ _ using 1
                · rfl
                · simp [firstChainCandidate, firstChainCandidateWins, hrecord,
                    hhonest, hforged, hcoord, hcollision]
          · convert firstChain_pureDecision hash pp
              (ReductionGames.endpointTargets hash pp starts)
              0 (hash.digestInput fallback) using 1
            · simp only [hhonest, hword, ↓reduceDIte, pure_bind]
              cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
              | none => rfl
              | some pair => cases pair; rfl
            · simp [firstChainCandidate, firstChainCandidateWins, hrecord,
                hhonest, hforged, hword]

/-- The faithful chain coupling sends each removed returned win to a returned TCR win. -/
private theorem firstChainCoupledDifference_le_win
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    𝒟[firstChainCoupledDifferenceProgram hash enc K adv] {true} ≤
      𝒟[firstChainCoupledProgram hash enc K adv] {true} := by
  unfold firstChainCoupledDifferenceProgram firstChainCoupledProgram
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (HashInstance.thf hash).seedGen _ _ (by measurability)
  intro pp _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    ($ᵗ H : ProbComp H) _ _ (by measurability)
  intro fallback _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (GXMSS.sampleStarts H h v) _ _ (by measurability)
  intro starts _
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (ReductionGames.runWithKeys hash enc K adv
      (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2)
    _ _ (by measurability)
  intro out hout
  obtain ⟨hpk, hsk⟩ := ReductionGames.runWithKeys_support_keys hash enc K adv
    (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hout
  cases out with
  | mk pk sk forgery history =>
    dsimp at hpk hsk
    subst pk
    subst sk
    by_cases hdiff : ReductionGames.successfulFirstChainDifference hash enc K
        ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
          forgery, history⟩ = true
    · have hwin := firstChainCandidateWins_of_difference hash enc K adv pp starts
        fallback forgery history hout hdiff
      simp [hdiff, hwin]
    · have hfalse : ReductionGames.successfulFirstChainDifference hash enc K
          ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
            forgery, history⟩ = false := Bool.eq_false_iff.mpr hdiff
      simp [hfalse]

/-- The exact successful-record first-chain difference is bounded by the fixed reduction's
authoritative stand-alone SM-DT-TCR advantage under native returned-output measures. -/
theorem successful_first_chain_difference_le_target_collision_advantage
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.successfulFirstChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (ReductionGames.firstChainTargetCollisionReduction hash enc K adv) := by
  unfold ReductionGames.successfulFirstChainDifferenceMass SM_DT_TCR_Advantage
  rw [ProbCompRuntime.probComp_evalDist,
    ← firstChainCoupledDifference_evalDist_eq_source]
  rw [firstChainExperiment_eq_coupled]
  exact firstChainCoupledDifference_le_win hash enc K adv

/-- The successful-record Game 2 to Game 3 hop uses the unchanged first-chain reduction.
Returned false and unreturned mass remain governed by the native partial computations. -/
theorem game_two_le_game_three_add_first_chain_target_collision
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.gameTwoAdvantage hash enc K adv ≤
      ReductionGames.gameThreeAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (ReductionGames.firstChainTargetCollisionReduction hash enc K adv) := by
  calc
    _ ≤ ReductionGames.gameThreeAdvantage hash enc K adv +
        ReductionGames.successfulFirstChainDifferenceMass hash enc K adv :=
      ReductionGames.gameTwoAdvantage_le_gameThree_add_successfulFirstChainDifference
        hash enc K adv
    _ ≤ _ := add_le_add_right
      (successful_first_chain_difference_le_target_collision_advantage hash enc K adv) _

end

end GXMSS.Unforgeability
