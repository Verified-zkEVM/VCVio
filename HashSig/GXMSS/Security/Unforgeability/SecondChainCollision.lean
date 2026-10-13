/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability.FirstChainCollision
import all HashSig.GXMSS.Security.Unforgeability.MerkleCollision
import all HashSig.GXMSS.Security.Unforgeability.FirstChainCollision
import all HashSig.GXMSS.Security.ReductionGames.SourceGames
import all HashSig.GXMSS.Security.ReductionGames.GuessingGames
import all HashSig.GXMSS.Security.ReductionGames.CollisionReductions
import all HashSig.GXMSS.Security.ReductionGames.SplicedChain
import all HashSig.GXMSS.Security.ReductionGames.ChainHybrid
import all HashSig.GXMSS.Security.ReductionGames.JointReductions

/-!
# Second chain target collision bound

The successful-record Game 3 to Game 4 difference is bounded using the fixed second-chain
target-collision reduction. Unused and failed-consumed histories remain in Game 4.
-/

public section

namespace GXMSS.Unforgeability

open Encoding ENNReal OracleComp OracleSpec TweakableHash

noncomputable section

variable {PP T X H M R : Type} {h w v : ℕ}

/-! ## Second-chain successful-record hop -/

/-- Exact candidate returned by the fixed second-chain reduction after source interaction. -/
private def secondChainCandidate [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (state : ReductionGames.TCRKeyState PP T X H h v) (pp : PP)
    (out : ReductionGames.Result PP H M R h v) : ℕ × X :=
  let fallback := (0, hash.digestInput state.fallback)
  let ep := out.forgery.1
  let forgedMessage := out.forgery.2.1
  let forgedSignature := out.forgery.2.2
  match out.history ep with
  | some (msg, some signature) =>
    match enc.value pp msg signature.randomizer ep,
      enc.value pp forgedMessage forgedSignature.randomizer ep with
    | some honestWord, some forgedWord =>
      match Security.findSmallerCoordinate honestWord forgedWord with
      | none => fallback
      | some i =>
        match hash.findChainCut pp ep i (forgedWord i) (honestWord i)
            (2 ^ w - 1) (signature.ots i) (forgedSignature.ots i) with
        | some (.inr d) =>
          let advanced := hash.chain pp ep i (forgedWord i)
            ((honestWord i).val - (forgedWord i).val) (forgedSignature.ots i)
          let tweak := hash.chainTweak (ep, i,
            ⟨(honestWord i).val + d.val, by omega⟩)
          let first := hash.digestInput
            (hash.chain pp ep i (honestWord i) d (signature.ots i))
          let second := hash.digestInput
            (hash.chain pp ep i (honestWord i) d advanced)
          (ReductionGames.registeredIndex state.targets tweak first, second)
        | _ => fallback
    | _, _ => fallback
  | _ => fallback

/-- A non-aligned designated cut supplies a registered honest-first target collision. -/
private theorem secondChain_registeredTarget_wins
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (starts : Fin (2 ^ h) → Fin v → H) (ep : Fin (2 ^ h))
    (honestWord forgedWord : Codeword v (2 ^ w))
    (honestOTS forgedOTS : Fin v → H) (i : Fin v)
    (hi : Security.findSmallerCoordinate honestWord forgedWord = some i)
    (hhonest : honestOTS i = hash.chain pp ep i 0 (honestWord i) (starts ep i))
    (hend : hash.chain pp ep i (honestWord i)
      (2 ^ w - 1 - (honestWord i).val) (honestOTS i) =
        hash.chain pp ep i (forgedWord i)
          (2 ^ w - 1 - (forgedWord i).val) (forgedOTS i))
    (hneCut : hash.chain pp ep i (forgedWord i)
      ((honestWord i).val - (forgedWord i).val) (forgedOTS i) ≠ honestOTS i) :
    ∃ d : Fin (2 ^ w - 1 - (honestWord i).val),
      hash.findChainCut pp ep i (forgedWord i) (honestWord i)
        (2 ^ w - 1) (honestOTS i) (forgedOTS i) = some (.inr d) ∧
      let advanced := hash.chain pp ep i (forgedWord i)
        ((honestWord i).val - (forgedWord i).val) (forgedOTS i)
      let tweak := hash.chainTweak (ep, i, ⟨(honestWord i).val + d.val, by omega⟩)
      let first := hash.digestInput (hash.chain pp ep i (honestWord i) d (honestOTS i))
      let second := hash.digestInput (hash.chain pp ep i (honestWord i) d advanced)
      firstChainCandidateWins hash pp (ReductionGames.endpointTargets hash pp starts)
        (ReductionGames.registeredIndex
          (ReductionGames.endpointTargets hash pp starts) tweak first, second) = true := by
  have hsome := hash.findChainCut_isSome_of_smallerCoordinate pp ep honestWord forgedWord
    hi (honestOTS i) (forgedOTS i) hend
  obtain ⟨cut, hcut⟩ := Option.isSome_iff_exists.mp hsome
  cases cut with
  | inl u =>
    unfold HashInstance.findChainCut at hcut
    split at hcut
    next heq => exact False.elim (hneCut heq)
    next => simp at hcut
  | inr d =>
    refine ⟨d, hcut, ?_⟩
    let j : Fin (2 ^ w - 1) := ⟨(honestWord i).val + d.val, by omega⟩
    have hprefix : hash.chain pp ep i (honestWord i) d (honestOTS i) =
        hash.chain pp ep i 0 j.val (starts ep i) := by
      rw [hhonest]
      simpa [j] using
        (hash.chain_add pp ep i 0 (honestWord i).val d.val (starts ep i)).symm
    have hsound := hash.findChainCut_hash_sound pp ep i (forgedWord i)
      (honestWord i) (2 ^ w - 1) (honestOTS i) (forgedOTS i)
      (by omega) (by omega) hcut
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
        (hash.digestInput (hash.chain pp ep i (honestWord i) d
            (hash.chain pp ep i (forgedWord i)
              ((honestWord i).val - (forgedWord i).val) (forgedOTS i))) ≠
          hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)) ∧
         hash.thf.eval pp (hash.chainTweak (ep, i, j))
           (hash.digestInput (hash.chain pp ep i (honestWord i) d
             (hash.chain pp ep i (forgedWord i)
               ((honestWord i).val - (forgedWord i).val) (forgedOTS i)))) =
         hash.thf.eval pp (hash.chainTweak (ep, i, j))
           (hash.digestInput (hash.chain pp ep i 0 j.val (starts ep i)))) = true from
        decide_eq_true ⟨hsound.1.symm, hsound.2.symm⟩)

/-- A returned Game 3 win removed by Game 4 makes the fixed second-chain candidate win. -/
private theorem secondChainCandidateWins_of_difference
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
    (hdiff : ReductionGames.successfulSecondChainDifference hash enc K
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩ = true) :
    let registered := ReductionGames.endpointTargets hash pp starts
    let state : ReductionGames.TCRKeyState PP T X H h v :=
      ⟨starts, GXMSS.endpoints hash pp starts, fallback, registered, fallback⟩
    let out : ReductionGames.Result PP H M R h v :=
      ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
        forgery, history⟩
    firstChainCandidateWins hash pp registered (secondChainCandidate hash enc state pp out) =
      true := by
  let out : ReductionGames.Result PP H M R h v :=
    ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
      forgery, history⟩
  let ep := forgery.1
  let forgedSignature := forgery.2.2
  change ReductionGames.successfulSecondChainDifference hash enc K out = true at hdiff
  cases hs : ReductionGames.forgedEpochSource out with
  | unused =>
    simp only [ReductionGames.successfulSecondChainDifference, hs,
      Bool.and_false, Bool.false_eq_true] at hdiff
  | failedConsumed msg =>
    simp only [ReductionGames.successfulSecondChainDifference, hs,
      Bool.and_false, Bool.false_eq_true] at hdiff
  | successful msg sig =>
    have hrecord := ReductionGames.history_of_successful_source out msg sig hs
    change history ep = some (msg, some sig) at hrecord
    obtain ⟨wr, hsig, hword⟩ :=
      ReductionGames.runWithKeys_successful_record_signature hash enc K adv
        (GXMSS.keys hash pp starts).1 (GXMSS.keys hash pp starts).2 out hrun ep msg sig
        hrecord
    have hhonestWord : enc.value pp msg sig.randomizer ep = some wr.1 := by
      simpa [out, hsig, GXMSS.keys, GXMSS.signatureOfWord] using hword
    have hsplit : ReductionGames.gameThreeObservation hash enc K out = true ∧
        (!ReductionGames.gameFourObservation hash enc K out) = true := by
      simpa only [ReductionGames.successfulSecondChainDifference, hs,
        Bool.and_true, Bool.and_eq_true] using hdiff
    have hthree := hsplit.1
    have htwo : ReductionGames.gameTwoObservation hash enc K out = true := by
      have h := hthree
      simp only [ReductionGames.gameThreeObservation, Bool.and_eq_true] at h
      exact h.1
    have hone : ReductionGames.gameOneObservation hash enc K out = true := by
      have h := htwo
      simp only [ReductionGames.gameTwoObservation, Bool.and_eq_true] at h
      exact h.1
    have hforged : ∃ forgedWord,
        enc.value pp forgery.2.1 forgedSignature.randomizer ep = some forgedWord := by
      have h := htwo
      simp only [ReductionGames.gameTwoObservation, hs, hone,
        Bool.true_and] at h
      change (match enc.value pp msg sig.randomizer ep,
          enc.value pp forgery.2.1 forgedSignature.randomizer ep with
        | some honestWord, some forgedWord =>
          decide ((msg, sig.randomizer) =
            (forgery.2.1, forgedSignature.randomizer) ∨ honestWord ≠ forgedWord)
        | _, _ => false) = true at h
      cases he : enc.value pp forgery.2.1 forgedSignature.randomizer ep with
      | none =>
        rw [hhonestWord, he] at h
        simp at h
      | some forgedWord => exact ⟨forgedWord, rfl⟩
    obtain ⟨forgedWord, hforgedWord⟩ := hforged
    have hleaf := hone
    simp only [ReductionGames.gameOneObservation, Bool.and_eq_true] at hleaf
    have hleaf' := hleaf.2
    have hleafValue : ReductionGames.forgedLeaf? hash enc out =
        some (fun i => hash.chain pp ep i (forgedWord i)
          (2 ^ w - 1 - (forgedWord i).val) (forgedSignature.ots i)) := by
      simp [ReductionGames.forgedLeaf?, out, ep, forgedSignature,
        GXMSS.keys, hforgedWord]
    rw [hleafValue] at hleaf'
    have hopening :
        (GXMSS.endpoints hash pp starts ep,
          hash.authPath pp (GXMSS.endpoints hash pp starts) ep) =
        ((fun i => hash.chain pp ep i (forgedWord i)
            (2 ^ w - 1 - (forgedWord i).val) (forgedSignature.ots i)),
          forgedSignature.path) := by
      simpa [out, GXMSS.keys] using (of_decide_eq_true hleaf')
    have hpath : sig.path = forgedSignature.path := by
      rw [hsig]
      exact (congrArg Prod.snd hopening)
    have hwordne : wr.1 ≠ forgedWord :=
      ReductionGames.gameThree_successful_words_ne hash enc K out msg sig
        wr.1 forgedWord hs hthree (by simpa [out, GXMSS.keys] using hhonestWord)
        (by simpa [out, GXMSS.keys] using hforgedWord) hpath
    have hisome := Security.findSmallerCoordinate_isSome_of_successes enc pp pp
      msg forgery.2.1 sig.randomizer forgedSignature.randomizer ep ep
      hhonestWord hforgedWord hwordne
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hisome
    have hcut : ReductionGames.designatedCutHolds hash enc out = false := by
      have h := hsplit.2
      simp only [ReductionGames.gameFourObservation, hthree,
        Bool.true_and] at h
      cases hc : ReductionGames.designatedCutHolds hash enc out <;>
        simp [hc] at h ⊢
    have hneCut : hash.chain pp ep i (forgedWord i)
        ((wr.1 i).val - (forgedWord i).val) (forgedSignature.ots i) ≠ sig.ots i := by
      have h := hcut
      simp only [ReductionGames.designatedCutHolds, hs] at h
      change (match enc.value pp msg sig.randomizer ep,
          enc.value pp forgery.2.1 forgedSignature.randomizer ep with
        | some honestWord, some forgedWord =>
          match Security.findSmallerCoordinate honestWord forgedWord with
          | none => false
          | some coordinate => decide (hash.chain pp ep coordinate (forgedWord coordinate)
              ((honestWord coordinate).val - (forgedWord coordinate).val)
              (forgedSignature.ots coordinate) = sig.ots coordinate)
        | _, _ => false) = false at h
      rw [hhonestWord, hforgedWord] at h
      change (match Security.findSmallerCoordinate wr.1 forgedWord with
        | none => false
        | some coordinate => decide (hash.chain pp ep coordinate (forgedWord coordinate)
            ((wr.1 coordinate).val - (forgedWord coordinate).val)
            (forgedSignature.ots coordinate) = sig.ots coordinate)) = false at h
      rw [hi] at h
      exact of_decide_eq_false h
    have hhonestOTS : sig.ots i = hash.chain pp ep i 0 (wr.1 i) (starts ep i) := by
      simp [hsig, GXMSS.signatureOfWord, GXMSS.keys]
    have hend : hash.chain pp ep i (wr.1 i)
        (2 ^ w - 1 - (wr.1 i).val) (sig.ots i) =
        hash.chain pp ep i (forgedWord i)
          (2 ^ w - 1 - (forgedWord i).val) (forgedSignature.ots i) := by
      rw [hhonestOTS, hash.chain_complete_digit]
      exact congrFun (congrArg Prod.fst hopening) i
    obtain ⟨d, hd, hvalid⟩ := secondChain_registeredTarget_wins hash pp starts ep
      wr.1 forgedWord sig.ots forgedSignature.ots i hi hhonestOTS hend hneCut
    dsimp only
    simpa [secondChainCandidate, out, ep, forgedSignature, hrecord,
      hhonestWord, hforgedWord, hi, hd] using hvalid

private def secondChainCoupledProgram [SampleableType H] [SampleableType R]
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
  pure (firstChainCandidateWins hash pp registered (secondChainCandidate hash enc state pp out))

private def secondChainCoupledDifferenceProgram [SampleableType H] [SampleableType R]
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
  pure (ReductionGames.successfulSecondChainDifference hash enc K out)

/-- The private fallback draw is invisible to the native second-chain difference measure. -/
private theorem secondChainCoupledDifference_evalDist_eq_source
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    𝒟[secondChainCoupledDifferenceProgram hash enc K adv] =
      𝒟[ReductionGames.successfulSecondChainDifference hash enc K <$>
        ReductionGames.sourceProgram hash enc K adv] := by
  unfold secondChainCoupledDifferenceProgram ReductionGames.sourceProgram GXMSS.keygen
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  apply OracleComp.evalDist_bind_congr_of_support
  intro pp _
  simpa only [GXMSS.keys, bind_assoc, Function.comp_def] using
    (OracleComp.evalDist_bind_const ($ᵗ H : ProbComp H) (do
      let starts ← GXMSS.sampleStarts H h v
      let (pk, sk) := GXMSS.keys hash pp starts
      let out ← ReductionGames.runWithKeys hash enc K adv pk sk
      pure (ReductionGames.successfulSecondChainDifference hash enc K out)))

/-- The authoritative second-chain TCR experiment has the same returned Boolean output as
the coupled source execution, including its fallback draw and ordered target history. -/
private theorem secondChainExperiment_eq_coupled
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    SM_DT_TCR_Experiment
      (ReductionGames.secondChainTargetCollisionReduction hash enc K adv) =
        secondChainCoupledProgram hash enc K adv := by
  have hcap := ReductionGames.chainProblem_capacity hash
  unfold SM_DT_TCR_Experiment secondChainCoupledProgram
  simp only [ReductionGames.secondChainTargetCollisionReduction]
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
    · simp [secondChainCandidate, firstChainCandidateWins, hrecord]
  | some entry =>
    rcases entry with ⟨msg, answer⟩
    cases answer with
    | none =>
      convert firstChain_pureDecision hash pp
        (ReductionGames.endpointTargets hash pp starts)
        0 (hash.digestInput fallback) using 1
      · rfl
      · simp [secondChainCandidate, firstChainCandidateWins, hrecord]
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
        · simp [secondChainCandidate, firstChainCandidateWins, hrecord, hhonest]
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
          · simp [secondChainCandidate, firstChainCandidateWins, hrecord,
              hhonest, hforged]
        | some forgedWord =>
          cases hcoord : Security.findSmallerCoordinate honestWord forgedWord with
          | none =>
            convert firstChain_pureDecision hash pp
              (ReductionGames.endpointTargets hash pp starts)
              0 (hash.digestInput fallback) using 1
            · simp only [hhonest, hcoord, pure_bind]
              cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
              | none => rfl
              | some pair => cases pair; rfl
            · simp [secondChainCandidate, firstChainCandidateWins, hrecord,
                hhonest, hforged, hcoord]
          | some i =>
            cases hcut : hash.findChainCut pp out.forgery.1 i (forgedWord i)
                (honestWord i) (2 ^ w - 1) (signature.ots i)
                (out.forgery.2.2.ots i) with
            | none =>
              convert firstChain_pureDecision hash pp
                (ReductionGames.endpointTargets hash pp starts)
                0 (hash.digestInput fallback) using 1
              · simp only [hhonest, hcoord, hcut, pure_bind]
                cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
                | none => rfl
                | some pair => cases pair; rfl
              · simp [secondChainCandidate, firstChainCandidateWins, hrecord,
                  hhonest, hforged, hcoord, hcut]
            | some cut =>
              cases cut with
              | inl preimage =>
                convert firstChain_pureDecision hash pp
                  (ReductionGames.endpointTargets hash pp starts)
                  0 (hash.digestInput fallback) using 1
                · simp only [hhonest, hcoord, hcut, pure_bind]
                  cases hidx : (ReductionGames.endpointTargets hash pp starts)[0]? with
                  | none => rfl
                  | some pair => cases pair; rfl
                · simp [secondChainCandidate, firstChainCandidateWins, hrecord,
                    hhonest, hforged, hcoord, hcut]
              | inr d =>
                simp only [hhonest, hcoord, hcut, pure_bind]
                convert firstChain_pureDecision hash pp
                  (ReductionGames.endpointTargets hash pp starts) _ _ using 1
                · rfl
                · simp [secondChainCandidate, firstChainCandidateWins, hrecord,
                    hhonest, hforged, hcoord, hcut]

/-- Every returned successful-record difference gives a returned second-chain TCR win. -/
private theorem secondChainCoupledDifference_le_win
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    𝒟[secondChainCoupledDifferenceProgram hash enc K adv] {true} ≤
      𝒟[secondChainCoupledProgram hash enc K adv] {true} := by
  unfold secondChainCoupledDifferenceProgram secondChainCoupledProgram
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
    by_cases hdiff : ReductionGames.successfulSecondChainDifference hash enc K
        ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
          forgery, history⟩ = true
    · have hwin := secondChainCandidateWins_of_difference hash enc K adv pp starts
        fallback forgery history hout hdiff
      simp [hdiff, hwin]
    · have hfalse : ReductionGames.successfulSecondChainDifference hash enc K
          ⟨(GXMSS.keys hash pp starts).1, (GXMSS.keys hash pp starts).2,
            forgery, history⟩ = false := Bool.eq_false_iff.mpr hdiff
      simp [hfalse]

/-- The fixed second-chain reduction charges all returned successful-record Game 3 to Game 4
differences in the authoritative SM-DT-TCR experiment. -/
theorem successful_second_chain_difference_le_target_collision_advantage
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.successfulSecondChainDifferenceMass hash enc K adv ≤
      SM_DT_TCR_Advantage
        (ReductionGames.secondChainTargetCollisionReduction hash enc K adv) := by
  unfold ReductionGames.successfulSecondChainDifferenceMass SM_DT_TCR_Advantage
  rw [ProbCompRuntime.probComp_evalDist,
    ← secondChainCoupledDifference_evalDist_eq_source]
  rw [secondChainExperiment_eq_coupled]
  exact secondChainCoupledDifference_le_win hash enc K adv

/-- Game 3 to Game 4 is bounded by the fixed second-chain target-collision reduction under
native returned-output measures, including returned false and all unreturned mass. -/
theorem game_three_le_game_four_add_second_chain_target_collision
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : ReductionGames.SchemeAdversary PP H M R h v) :
    ReductionGames.gameThreeAdvantage hash enc K adv ≤
      ReductionGames.gameFourAdvantage hash enc K adv +
        SM_DT_TCR_Advantage
          (ReductionGames.secondChainTargetCollisionReduction hash enc K adv) := by
  calc
    _ ≤ ReductionGames.gameFourAdvantage hash enc K adv +
        ReductionGames.successfulSecondChainDifferenceMass hash enc K adv :=
      ReductionGames.gameThreeAdvantage_le_gameFour_add_successfulSecondChainDifference
        hash enc K adv
    _ ≤ _ := add_le_add_right
      (successful_second_chain_difference_le_target_collision_advantage hash enc K adv) _

end

end GXMSS.Unforgeability
