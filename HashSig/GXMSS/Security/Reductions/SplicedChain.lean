/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.CollisionReductions
import all HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.GuessingGames
import all HashSig.GXMSS.Security.Reductions.CollisionReductions

/-!
# Spliced chain simulation

The challenge image is spliced into one guessed chain position. Filtered signing histories
track which successful source events survive that splice.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- Native winning mass of the successful-record Game 1 to Game 2 difference is bounded by
the exact authoritative target-collision experiment. The unused and failed-consumed cases
contribute no mass to this event; any unreturned mass remains unconditioned. -/
theorem successfulEncodingDifferenceMass_le_encodingTargetCollisionAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hbound : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    successfulEncodingDifferenceMass hash enc K adv ≤
      TargetCollisionResistance.advantage
        (encodingTargetCollisionReduction hash enc qs K adv) := by
  have hprogram :
      (successfulEncodingDifference hash enc K <$> sourceProgram hash enc K adv) =
        (fun z => successfulEncodingDifference hash enc K z.1) <$>
          encodingSourceCoupledProgram hash enc K adv := by
    rw [← encodingSourceCoupledProgram_proj hash enc K adv]
    simp only [Functor.map_map]
  unfold successfulEncodingDifferenceMass TargetCollisionResistance.advantage
    TargetCollisionResistance.outputMeasure
  rw [hprogram, encodingTargetExperiment_eq_coupled hash enc qs K adv hbound]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  apply OracleComp.evalDist_bind_apply_mono_of_support
    (encodingSourceCoupledProgram hash enc K adv)
    (fun z => pure (successfulEncodingDifference hash enc K z.1))
    (encodingTargetTail hash enc qs K) (measurableSet_singleton true)
  intro out hout
  by_cases hdiff : successfulEncodingDifference hash enc K out.1 = true
  · obtain ⟨hseed, hrecords⟩ :=
      encodingSourceCoupledProgram_support hash enc K adv out hout
    rw [encodingTargetTail_successfulDifference hash enc qs K out hseed hrecords hdiff]
    simp [hdiff]
  · have hfalse : successfulEncodingDifference hash enc K out.1 = false := by
      cases h : successfulEncodingDifference hash enc K out.1 <;> simp_all
    simp [hfalse]

private structure SingleTargetState (H : Type) (h w v : ℕ) where
  guess : Guess h w v
  answer : Option H
  starts : Epoch h → Fin v → H

private structure UDTargetState (H : Type) (h w v : ℕ) where
  guess : Guess h w v
  hybrid : Fin (2 ^ w - 1)
  answer : Option H
  starts : Epoch h → Fin v → H

/-- Chain family spliced at the guessed positive position using the challenge image itself. -/
private def splicedChainValue (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (ep : Epoch h) (i : Fin v) (position : ℕ) : H :=
  if _htarget : ep = guessedEpoch guess ∧ i = guessedChain guess then
    if position < (guessedPosition guess).val + 1 then
      hash.chain pp ep i 0 position (starts ep i)
    else hash.chain pp ep i ((guessedPosition guess).val + 1)
      (position - ((guessedPosition guess).val + 1)) answer
  else hash.chain pp ep i 0 position (starts ep i)

/-- Supplying the honest response at a cut reproduces every original chain prefix. -/
private theorem splicedChainValue_honest
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (ep : Epoch h) (i : Fin v) (position : ℕ) :
    splicedChainValue hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts ep i position =
      hash.chain pp ep i 0 position (starts ep i) := by
  unfold splicedChainValue
  split_ifs with htarget hbefore
  · rfl
  · rcases htarget with ⟨hepoch, hchain⟩
    subst ep
    subst i
    have hle : (guessedPosition guess).val + 1 ≤ position := by omega
    simpa [Nat.add_sub_of_le hle] using
      (hash.chain_add pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (position - ((guessedPosition guess).val + 1))
        (starts (guessedEpoch guess) (guessedChain guess))).symm
  · rfl

/-- Advancing a splice by one chain step leaves every later prefix unchanged when the later
answer is the hash of the earlier answer. -/
private theorem splicedChainValue_advance
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (ep : Epoch h) (i : Fin v) (position : ℕ)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hlate : (guessedPosition guess₂).val + 1 ≤ position) :
    splicedChainValue hash pp guess₁ answer starts ep i position =
      splicedChainValue hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts ep i position := by
  unfold splicedChainValue
  by_cases htarget : ep = guessedEpoch guess₁ ∧ i = guessedChain guess₁
  · have htarget₂ : ep = guessedEpoch guess₂ ∧ i = guessedChain guess₂ := by
      simpa only [← hepoch, ← hchain] using htarget
    simp only [htarget]
    have hlate₁ : ¬position < (guessedPosition guess₁).val + 1 := by omega
    have hlate₂ : ¬position < (guessedPosition guess₂).val + 1 := by omega
    simp only [hlate₁, hlate₂, ↓reduceIte]
    rcases htarget with ⟨rfl, rfl⟩
    have hcount : position - ((guessedPosition guess₁).val + 1) =
        1 + (position - ((guessedPosition guess₂).val + 1)) := by omega
    rw [hcount, hash.chain_add]
    simp [hnext, hepoch, hchain]
  · have htarget₂ : ¬(ep = guessedEpoch guess₂ ∧ i = guessedChain guess₂) := by
      simpa only [← hepoch, ← hchain] using htarget
    simp [htarget, htarget₂]

private def splicedEndpoints (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H) :
    Epoch h → Fin v → H := fun ep i =>
  splicedChainValue hash pp guess answer starts ep i (2 ^ w - 1)

private theorem splicedEndpoints_honest
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) :
    splicedEndpoints hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      GXMSS.endpoints hash pp starts := by
  funext ep i
  exact splicedChainValue_honest hash pp guess starts ep i _

private theorem splicedEndpoints_advance
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1) :
    splicedEndpoints hash pp guess₁ answer starts =
      splicedEndpoints hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts := by
  funext ep i
  apply splicedChainValue_advance hash pp guess₁ guess₂ answer starts ep i
    (2 ^ w - 1) hepoch hchain hnext
  exact (guessedPosition guess₂).isLt

/-- Splicing the final hash response makes the selected endpoint exactly the response. -/
private theorem splicedEndpoints_guess_final
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    splicedEndpoints hash pp guess answer starts
      (guessedEpoch guess) (guessedChain guess) = answer := by
  rcases guess with ⟨ep, i, pos⟩
  dsimp [guessedEpoch, guessedChain, guessedPosition] at hfinal ⊢
  simp [splicedEndpoints, splicedChainValue, guessedEpoch, guessedChain,
    guessedPosition, hfinal]

private def splicedSignatureOfWord (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) (ep : Epoch h) (wr : Codeword v (2 ^ w) × R) :
    GXMSS.Signature R H h v :=
  ⟨wr.2, fun i => splicedChainValue hash pp guess answer starts ep i (wr.1 i),
    hash.authPath pp endpoints ep⟩

private theorem splicedSignatureOfWord_honest
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R) :
    splicedSignatureOfWord hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts
      (GXMSS.endpoints hash pp starts) ep wr =
    GXMSS.signatureOfWord hash ⟨pp, starts, GXMSS.endpoints hash pp starts⟩ ep wr := by
  have hots : (fun i => splicedChainValue hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts ep i (wr.1 i)) =
      (fun i => hash.chain pp ep i 0 (wr.1 i) (starts ep i)) := by
    funext i
    exact splicedChainValue_honest hash pp guess starts ep i _
  simp only [splicedSignatureOfWord, GXMSS.signatureOfWord, hots]

/-- A signing word beyond both adjacent cuts receives the same signature in either splice. -/
private theorem splicedSignatureOfWord_advance
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (ep : Epoch h)
    (wr : Codeword v (2 ^ w) × R)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hword : ep = guessedEpoch guess₁ →
      (guessedPosition guess₂).val + 1 ≤ (wr.1 (guessedChain guess₁)).val) :
    splicedSignatureOfWord hash pp guess₁ answer starts
      (splicedEndpoints hash pp guess₁ answer starts) ep wr =
    splicedSignatureOfWord hash pp guess₂
      (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
        ((guessedPosition guess₁).val + 1) 1 answer) starts
      (splicedEndpoints hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts) ep wr := by
  have hend := splicedEndpoints_advance hash pp guess₁ guess₂ answer starts
    hepoch hchain hnext
  have hots : (fun i => splicedChainValue hash pp guess₁ answer starts ep i (wr.1 i)) =
      (fun i => splicedChainValue hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts ep i (wr.1 i)) := by
    funext i
    by_cases htarget : ep = guessedEpoch guess₁ ∧ i = guessedChain guess₁
    · have hi : (guessedPosition guess₂).val + 1 ≤ (wr.1 i).val := by
        simpa only [htarget.2] using hword htarget.1
      exact splicedChainValue_advance hash pp guess₁ guess₂ answer starts ep i
        (wr.1 i).val hepoch hchain hnext hi
    · have htarget₂ : ¬(ep = guessedEpoch guess₂ ∧ i = guessedChain guess₂) := by
        simpa only [← hepoch, ← hchain] using htarget
      simp [splicedChainValue, htarget, htarget₂]
  simp only [splicedSignatureOfWord, hots, hend]

/-- At the selected positive digit, a spliced successful signature reveals the challenge
response itself as its OTS value. -/
private theorem splicedSignatureOfWord_guess_succ
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts endpoints : Epoch h → Fin v → H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hepoch : ep = guessedEpoch guess)
    (hword : (wr.1 (guessedChain guess)).val = (guessedPosition guess).val + 1) :
    (splicedSignatureOfWord hash pp guess answer starts endpoints ep wr).ots
      (guessedChain guess) = answer := by
  subst ep
  rcases guess with ⟨ep, i, pos⟩
  dsimp [guessedEpoch, guessedChain, guessedPosition] at hword ⊢
  simp [splicedSignatureOfWord, splicedChainValue, guessedEpoch, guessedChain,
    guessedPosition, hword]

private def splicedSigningOracle [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) := fun q history =>
  match history q.1 with
  | some _ => pure (none, history)
  | none => do
      let wr ← enc.retry ($ᵗ R) pp q.2 q.1 K
      let signature := wr.map (splicedSignatureOfWord hash pp guess answer starts endpoints q.1)
      return (signature, Function.update history q.1 (some (q.2, signature)))

/-- The splice with the actual chain answer has the exact honest handler, including optional
failure and consumed-epoch history. -/
private theorem splicedSigningOracle_honest
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) :
    splicedSigningOracle hash enc K pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts
      (GXMSS.endpoints hash pp starts) =
    SyncSignatureUnforgeability.signingOracle (GXMSS.scheme hash enc K)
      ⟨pp, starts, GXMSS.endpoints hash pp starts⟩ := by
  funext q history
  rcases q with ⟨ep, msg⟩
  by_cases hused : history ep = none
  · have hsig : (splicedSignatureOfWord hash pp guess
        (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
          ((guessedPosition guess).val + 1)
          (starts (guessedEpoch guess) (guessedChain guess))) starts
        (GXMSS.endpoints hash pp starts) ep :
          Codeword v (2 ^ w) × R → GXMSS.Signature R H h v) =
        GXMSS.signatureOfWord hash
          ⟨pp, starts, GXMSS.endpoints hash pp starts⟩ ep := by
      funext wr
      exact splicedSignatureOfWord_honest hash pp guess starts ep wr
    simp [splicedSigningOracle, SyncSignatureUnforgeability.signingOracle,
      hused, GXMSS.scheme, GXMSS.sign, hsig]
  · cases hrecord : history ep with
    | none => exact False.elim (hused hrecord)
    | some record =>
      simp [splicedSigningOracle, SyncSignatureUnforgeability.signingOracle, hrecord]

/-- Whether the retained first request at the selected epoch has a successful word below the
selected forged cut. The history remembers enough to decide this even after later queries. -/
private def badSelectedHistory
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (pp : PP)
    (selector : Guess h w v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) : Bool :=
  match history (guessedEpoch selector) with
  | some (msg, some sig) =>
    match enc.value pp msg sig.randomizer (guessedEpoch selector) with
    | some word => decide ((word (guessedChain selector)).val <
        (guessedPosition selector).val + 1)
    | none => false
  | _ => false

private def selectedHistoryProjection
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (pp : PP)
    (selector : Guess h w v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) :
    Option (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) :=
  if badSelectedHistory enc pp selector history then none else some history

/-- State projection through an absorbing filter preserves each good returned output, even when
bad paths later lose mass. This deliberately asserts no equality for bad or missing outputs. -/
private theorem goodOutput_simulateQ_eq_filtered
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    [MeasurableSpace σ] [MeasurableSpace α]
    [MeasurableSingletonClass σ] [MeasurableSingletonClass α]
    (original : QueryImpl spec (StateT σ ProbComp))
    (filtered : QueryImpl spec (StateT (Option σ) ProbComp))
    (bad : σ → Bool)
    (transform : (t : spec.Domain) → spec.Range t × σ → spec.Range t)
    (htransform : ∀ t u s', bad s' = false → transform t (u, s') = u)
    (hmono : ∀ t s, bad s = true →
      ∀ z ∈ support ((original t).run s), bad z.2 = true)
    (habsorb : ∀ t, ∀ z ∈ support ((filtered t).run none), z.2 = none)
    (hstep : ∀ t s, bad s = false →
      (fun z => (transform t z, if bad z.2 then none else some z.2)) <$>
        (original t).run s = (filtered t).run (some s))
    (oa : OracleComp spec α) (s₀ : σ) (a : α) (s : σ)
    (hgood : bad s = false) :
    𝒟[(simulateQ original oa).run s₀] {(a, s)} =
      𝒟[(simulateQ filtered oa).run
        (if bad s₀ then none else some s₀)] {(a, some s)} := by
  classical
  simp only [← prEvent_eq_evalDist_singleton]
  have zeroOriginal (program : OracleComp spec α) (start : σ)
      (hbad : bad start = true) :
      𝒟[(simulateQ original program).run start] {(a, s)} = 0 := by
    rw [← prEvent_eq_evalDist_singleton]
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    intro z hz heq
    have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
      original (fun x => bad x = true) hmono program start hbad z hz
    subst z
    exact Bool.false_ne_true (hgood.symm.trans hpres)
  have zeroFiltered (program : OracleComp spec α) :
      𝒟[(simulateQ filtered program).run none] {(a, some s)} = 0 := by
    rw [← prEvent_eq_evalDist_singleton]
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    intro z hz heq
    have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
      filtered (fun x => x = none) (by
        intro t state hs z hz
        subst state
        exact habsorb t z hz) program none rfl z hz
    subst z
    cases hpres
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure x =>
    by_cases hbad : bad s₀ = true
    · have hsneq : s ≠ s₀ := by
        intro he
        subst s₀
        exact Bool.false_ne_true (hgood.symm.trans hbad)
      simpa [hbad, simulateQ_pure] using
        (fun (_ : x = a) (he : s₀ = s) => hsneq he.symm)
    · have hgood₀ : bad s₀ = false := by cases h : bad s₀ <;> simp_all
      simp [hgood₀, simulateQ_pure]
  | query_bind t cont ih =>
    by_cases hbad : bad s₀ = true
    · simpa only [hbad, ite_true, ← prEvent_eq_evalDist_singleton, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind] using
        (zeroOriginal ((liftM (OracleSpec.query t) :
          OracleComp spec (spec.Range t)) >>= cont) s₀ hbad).trans
          (zeroFiltered ((liftM (OracleSpec.query t) :
            OracleComp spec (spec.Range t)) >>= cont)).symm
    · have hgood₀ : bad s₀ = false := by cases h : bad s₀ <;> simp_all
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [hgood₀, Bool.false_eq_true, ite_false]
      rw [← hstep t s₀ hgood₀, bind_map_left]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      exact tsum_congr fun ⟨u, s'⟩ => by
        congr 1
        by_cases hbad' : bad s' = true
        · simp only [hbad', ite_true]
          simpa only [← prEvent_eq_evalDist_singleton] using
            (zeroOriginal (cont u) s' hbad').trans
              (zeroFiltered (cont (transform t (u, s')))).symm
        · have hgood' : bad s' = false := by cases h : bad s' <;> simp_all
          simpa [hgood', htransform t u s' hgood'] using ih u s'

/-- A selected win never ends with the killed successful first request. -/
private theorem jointChainObservation_not_badSelectedHistory
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    badSelectedHistory enc out.pk.seed guess out.history = false := by
  cases hs : forgedEpochSource out with
  | successful msg sig =>
    obtain ⟨honestWord, forgedWord, i, _, hhonest, _, _, hepoch, hchain,
      hposition⟩ :=
      jointChainObservation_successful_cut hash enc K guess out msg sig hs hwin
    have hrecord := history_of_successful_source out msg sig hs
    have hnot : ¬(honestWord (guessedChain guess)).val <
        (guessedPosition guess).val + 1 := by
      rw [hchain, hposition]
      omega
    simp [badSelectedHistory, hepoch, hrecord, hhonest, hnot]
  | unused =>
    have hepoch : guessedEpoch guess = out.forgery.1 := by
      have h := hwin
      simp only [jointChainObservation, hs, Bool.and_eq_true] at h
      cases hword : enc.value out.pk.seed out.forgery.2.1
          out.forgery.2.2.randomizer out.forgery.1 with
      | none => simp [hword] at h
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [hword, hi] at h
        | some i =>
          simp only [hword, hi] at h
          exact (of_decide_eq_true h.2).1
    have hnone : out.history out.forgery.1 = none := by
      cases hentry : out.history out.forgery.1 with
      | none => rfl
      | some record =>
        rcases record with ⟨m, sig⟩
        cases sig <;> simp [forgedEpochSource, hentry] at hs
    simp [badSelectedHistory, hepoch, hnone]
  | failedConsumed msg =>
    have hepoch : guessedEpoch guess = out.forgery.1 := by
      have h := hwin
      simp only [jointChainObservation, hs, Bool.and_eq_true] at h
      cases hword : enc.value out.pk.seed out.forgery.2.1
          out.forgery.2.2.randomizer out.forgery.1 with
      | none => simp [hword] at h
      | some word =>
        cases hi : findNonMaximumCoordinate word with
        | none => simp [hword, hi] at h
        | some i =>
          simp only [hword, hi] at h
          exact (of_decide_eq_true h.2).1
    have hfailed : out.history out.forgery.1 = some (msg, none) := by
      cases hentry : out.history out.forgery.1 with
      | none => simp [forgedEpochSource, hentry] at hs
      | some record =>
        rcases record with ⟨m, s⟩
        cases s with
        | none =>
          have hm : m = msg := by simpa [forgedEpochSource, hentry] using hs
          subst m
          rfl
        | some sig => simp [forgedEpochSource, hentry] at hs
    simp [badSelectedHistory, hepoch, hfailed]

/-- Kill a transcript as soon as a successful selected-epoch signing word lies before the
designated forged cut. Such a transcript cannot satisfy the enlarged selected event. The kill
state is absorbing, so the filtered interpreter retains exact returned winning mass. -/
private def filteredSplicedSigningOracle [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (selector splice : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) := fun q state =>
  match state with
  | none => pure (none, none)
  | some history =>
    match history q.1 with
    | some _ => pure (none, some history)
    | none => do
      let wr ← enc.retry ($ᵗ R) pp q.2 q.1 K
      match wr with
      | none => pure (none, some (Function.update history q.1 (some (q.2, none))))
      | some value =>
        if q.1 = guessedEpoch selector ∧
            (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1 then
          pure (none, none)
        else
          let signature := splicedSignatureOfWord hash pp splice answer starts
            endpoints q.1 value
          pure (some signature, some (Function.update history q.1
            (some (q.2, some signature))))

/-- A selected bad first request is retained because a consumed epoch is never overwritten. -/
private theorem badSelectedHistory_splicedSigningOracle_mono
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (selector splice : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H)
    (q : Epoch h × M)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hbad : badSelectedHistory enc pp selector history = true)
    (z : Option (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))
    (hz : z ∈ support ((splicedSigningOracle hash enc K pp splice answer starts
      endpoints q).run history)) :
    badSelectedHistory enc pp selector z.2 = true := by
  classical
  rcases q with ⟨ep, msg⟩
  change z ∈ support (splicedSigningOracle hash enc K pp splice answer starts
    endpoints (ep, msg) history) at hz
  have hselected : history (guessedEpoch selector) ≠ none := by
    intro hn
    simp [badSelectedHistory, hn] at hbad
  by_cases hused : history ep = none
  · have heq : ep ≠ guessedEpoch selector := by
      intro he
      exact hselected (he ▸ hused)
    simp only [splicedSigningOracle, hused, mem_support_bind_iff] at hz
    obtain ⟨wr, _, hz⟩ := hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst z
    have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
    simpa [badSelectedHistory, Function.update, heq'] using hbad
  · cases hrecord : history ep with
    | none => exact False.elim (hused hrecord)
    | some record =>
      simp only [splicedSigningOracle, hrecord, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hbad

private theorem selectedHistoryProjection_spliced_step_good
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (selector splice : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H)
    (q : Epoch h × M)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hgood : badSelectedHistory enc pp selector history = false) :
    (fun z => (if badSelectedHistory enc pp selector z.2 then none else z.1,
      selectedHistoryProjection enc pp selector z.2)) <$>
      (splicedSigningOracle hash enc K pp splice answer starts endpoints q).run history =
    (filteredSplicedSigningOracle hash enc K pp selector splice answer starts
      endpoints q).run (some history) := by
  classical
  rcases q with ⟨ep, msg⟩
  change (fun z => (if badSelectedHistory enc pp selector z.2 then none else z.1,
      selectedHistoryProjection enc pp selector z.2)) <$>
      splicedSigningOracle hash enc K pp splice answer starts endpoints
        (ep, msg) history =
    filteredSplicedSigningOracle hash enc K pp selector splice answer starts
      endpoints (ep, msg) (some history)
  by_cases hused : history ep = none
  · simp only [splicedSigningOracle, filteredSplicedSigningOracle, hused,
      map_bind]
    apply bind_congr_of_forall_mem_support
    intro wr hwr
    cases wr with
    | none =>
      have hnew : badSelectedHistory enc pp selector
          (Function.update history ep (some (msg, none))) = false := by
        by_cases heq : ep = guessedEpoch selector
        · subst ep; simp [badSelectedHistory, Function.update]
        · have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
          simpa [badSelectedHistory, Function.update, heq'] using hgood
      simp [selectedHistoryProjection, hnew]
    | some value =>
      have hvalue : enc.value pp msg value.2 ep = some value.1 :=
        IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
          ($ᵗ R) pp msg ep K value.1 value.2 hwr
      by_cases hkill : ep = guessedEpoch selector ∧
          (value.1 (guessedChain selector)).val <
            (guessedPosition selector).val + 1
      · have hnew : badSelectedHistory enc pp selector
            (Function.update history ep (some (msg, some
              (splicedSignatureOfWord hash pp splice answer starts endpoints ep value)))) =
              true := by
          rcases hkill with ⟨rfl, hlt⟩
          simp [badSelectedHistory, Function.update,
            splicedSignatureOfWord, hvalue, hlt]
        rcases hkill with ⟨rfl, hlt⟩
        simp [selectedHistoryProjection, hnew, hlt]
      · have hnew : badSelectedHistory enc pp selector
            (Function.update history ep (some (msg, some
              (splicedSignatureOfWord hash pp splice answer starts endpoints ep value)))) =
              false := by
          by_cases heq : ep = guessedEpoch selector
          · subst ep
            have hnot : ¬ (value.1 (guessedChain selector)).val <
                (guessedPosition selector).val + 1 := by
              intro hlt; exact hkill ⟨rfl, hlt⟩
            simp [badSelectedHistory, Function.update,
              splicedSignatureOfWord, hvalue, hnot]
          · have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
            simpa [badSelectedHistory, Function.update, heq'] using hgood
        have hguard : ¬(ep = guessedEpoch selector ∧
            (value.1 (guessedChain selector)).val ≤
              (guessedPosition selector).val) := by
          intro h
          exact hkill ⟨h.1, by omega⟩
        simp [hguard, selectedHistoryProjection, hnew]
  · cases hrecord : history ep with
    | none => exact False.elim (hused hrecord)
    | some record =>
      simp only [splicedSigningOracle, filteredSplicedSigningOracle, hrecord]
      simp [selectedHistoryProjection, hgood]

private theorem filteredSplicedSigningOracle_advance
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (pp : PP)
    (selector guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hselectEpoch : guessedEpoch selector = guessedEpoch guess₁)
    (hselectChain : guessedChain selector = guessedChain guess₁)
    (hselectPosition : (guessedPosition guess₂).val ≤ (guessedPosition selector).val) :
    filteredSplicedSigningOracle hash enc K pp selector guess₁ answer starts
      (splicedEndpoints hash pp guess₁ answer starts) =
    filteredSplicedSigningOracle hash enc K pp selector guess₂
      (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
        ((guessedPosition guess₁).val + 1) 1 answer) starts
      (splicedEndpoints hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts) := by
  have hend := splicedEndpoints_advance hash pp guess₁ guess₂ answer starts
    hepoch hchain hnext
  rw [← hend]
  funext q state
  cases state with
  | none => rfl
  | some history =>
    rcases q with ⟨ep, msg⟩
    by_cases hused : history ep = none
    · simp only [filteredSplicedSigningOracle, hused]
      apply bind_congr
      intro wr
      cases wr with
      | none => rfl
      | some value =>
        by_cases hbad : ep = guessedEpoch selector ∧
            (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1
        · simp [hbad]
        · have hword : ep = guessedEpoch guess₁ →
              (guessedPosition guess₂).val + 1 ≤
                (value.1 (guessedChain guess₁)).val := by
            intro hep
            have hepsel : ep = guessedEpoch selector := by
              simpa only [hselectEpoch] using hep
            have hnot : ¬(value.1 (guessedChain selector)).val <
                (guessedPosition selector).val + 1 := by
              intro hlt
              exact hbad ⟨hepsel, hlt⟩
            simpa only [hselectChain] using
              (show (guessedPosition guess₂).val + 1 ≤
                (value.1 (guessedChain selector)).val by omega)
          have hsig := splicedSignatureOfWord_advance hash pp guess₁ guess₂ answer
            starts ep value hepoch hchain hnext hword
          have hsig' := hsig
          rw [← hend] at hsig'
          simp [hsig']
    · cases hrecord : history ep with
      | none => exact False.elim (hused hrecord)
      | some record =>
        simp [filteredSplicedSigningOracle, hrecord]

private def splicedSuccessfulHistoryEncodes
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (pp : PP) (guess : Guess h w v) (answer : H)
    (starts endpoints : Epoch h → Fin v → H)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) : Prop :=
  ∀ ep msg sig, history ep = some (msg, some sig) →
    ∃ wr, sig = splicedSignatureOfWord hash pp guess answer starts endpoints ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1

/-- The spliced signing handler records the same successful retry witness that it used to
construct the returned signature. -/
private theorem splicedSigningOracle_preserves_successfulHistoryEncodes
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (pp : PP) (guess : Guess h w v) (answer : H)
    (starts endpoints : Epoch h → Fin v → H) (q : Epoch h × M)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hinv : splicedSuccessfulHistoryEncodes hash enc pp guess answer starts
      endpoints history)
    (out : Option (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v))
    (hout : out ∈ support
      ((splicedSigningOracle hash enc K pp guess answer starts endpoints q).run history)) :
    splicedSuccessfulHistoryEncodes hash enc pp guess answer starts endpoints out.2 := by
  rcases q with ⟨ep, msg⟩
  change out ∈ support (splicedSigningOracle hash enc K pp guess answer starts endpoints
    (ep, msg) history) at hout
  by_cases hused : history ep = none
  · simp only [splicedSigningOracle, hused, mem_support_bind_iff] at hout
    obtain ⟨wr?, hwr?, hret⟩ := hout
    simp only [support_pure, Set.mem_singleton_iff] at hret
    subst out
    intro ep' msg' sig' hentry
    by_cases heq : ep' = ep
    · subst ep'
      cases wr? with
      | none => simp [Function.update] at hentry
      | some wr =>
        have hpair : msg' = msg ∧
            sig' = splicedSignatureOfWord hash pp guess answer starts endpoints ep wr := by
          simpa [Function.update] using hentry.symm
        rcases hpair with ⟨hmsg, hsig⟩
        refine ⟨wr, ?_, ?_⟩
        · simp [hsig]
        · simpa [hmsg] using
            IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
              ($ᵗ R) pp msg ep K wr.1 wr.2 hwr?
    · have hold : history ep' = some (msg', some sig') := by
        simpa [Function.update, heq] using hentry
      exact hinv ep' msg' sig' hold
  · obtain ⟨first, firstAnswer, hrecord⟩ :
        ∃ first firstAnswer, history ep = some (first, firstAnswer) := by
      cases h : history ep with
      | none => exact False.elim (hused h)
      | some pair => exact ⟨pair.1, pair.2, rfl⟩
    simp only [splicedSigningOracle, hrecord] at hout
    simp only [support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hinv

private def runSpliced [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H) : ProbComp (Result PP H M R h v) := do
  let endpoints := splicedEndpoints hash pp guess answer starts
  let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      splicedSigningOracle hash enc K pp guess answer starts endpoints
  let (forgery, history) ←
    (simulateQ impl (adv.forge pk)).run SyncSignatureUnforgeability.emptyHistory
  return ⟨pk, sk, forgery, history⟩

private def runFilteredSpliced [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) : ProbComp (Option (Result PP H M R h v)) := do
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      filteredSplicedSigningOracle hash enc K pp selector splice answer starts endpoints
  let (forgery, state) ←
    (simulateQ impl (adv.forge pk)).run
      (some SyncSignatureUnforgeability.emptyHistory)
  match state with
  | none => return none
  | some history => return some ⟨pk, sk, forgery, history⟩

private theorem runFilteredSpliced_advance
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hselectEpoch : guessedEpoch selector = guessedEpoch guess₁)
    (hselectChain : guessedChain selector = guessedChain guess₁)
    (hselectPosition : (guessedPosition guess₂).val ≤ (guessedPosition selector).val) :
    runFilteredSpliced hash enc K adv pp selector guess₁ answer starts =
      runFilteredSpliced hash enc K adv pp selector guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts := by
  unfold runFilteredSpliced
  have hend := splicedEndpoints_advance hash pp guess₁ guess₂ answer starts
    hepoch hchain hnext
  have hfil := filteredSplicedSigningOracle_advance hash enc K pp selector
    guess₁ guess₂ answer starts hepoch hchain hnext hselectEpoch hselectChain
    hselectPosition
  rw [← hend] at hfil
  simp only [← hend, hfil]

/-- The full adaptive source/splice interaction and filtered interaction assign the same mass
to each good returned forgery/history pair. -/
private theorem splicedFiltered_good_raw_output
    [SampleableType R]
    [MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v))]
    [MeasurableSpace (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))]
    [MeasurableSingletonClass (SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v))]
    [MeasurableSingletonClass (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v))
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hgood : badSelectedHistory enc pp selector history = false) :
    let endpoints := splicedEndpoints hash pp splice answer starts
    let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp endpoints, pp⟩
    let original : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) ProbComp) :=
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) ProbComp) +
        splicedSigningOracle hash enc K pp splice answer starts endpoints
    let filtered : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v))) ProbComp) :=
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v))) ProbComp) +
        filteredSplicedSigningOracle hash enc K pp selector splice answer starts endpoints
    𝒟[(simulateQ original (adv.forge pk)).run
      SyncSignatureUnforgeability.emptyHistory] {(forgery, history)} =
    𝒟[(simulateQ filtered (adv.forge pk)).run
      (some SyncSignatureUnforgeability.emptyHistory)] {(forgery, some history)} := by
  classical
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp endpoints, pp⟩
  let original : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      splicedSigningOracle hash enc K pp splice answer starts endpoints
  let filtered : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      filteredSplicedSigningOracle hash enc K pp selector splice answer starts endpoints
  let bad := badSelectedHistory (H := H) enc pp selector
  let transform : (t : (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch h) M (GXMSS.Signature R H h v)).Domain) →
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v)).Range t ×
        SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v) →
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v)).Range t :=
    fun t z => match t with
      | .inl _ => z.1
      | .inr _ => if bad z.2 then none else z.1
  have htransform : ∀ t u s', bad s' = false → transform t (u, s') = u := by
    intro t u s' hs
    cases t <;> simp [transform, hs]
  have hmono : ∀ t s, bad s = true →
      ∀ z ∈ support ((original t).run s), bad z.2 = true := by
    intro t s hs z hz
    cases t with
    | inl uniform =>
      simp only [original, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, s)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      exact hs
    | inr signing =>
      exact badSelectedHistory_splicedSigningOracle_mono hash enc K pp selector
        splice answer starts endpoints signing s hs z hz
  have habsorb : ∀ t, ∀ z ∈ support ((filtered t).run none), z.2 = none := by
    intro t z hz
    cases t with
    | inl uniform =>
      simp only [filtered, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, none)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      rfl
    | inr signing =>
      simp only [filtered, QueryImpl.add_apply_inr] at hz
      change z ∈ support (filteredSplicedSigningOracle hash enc K pp selector
        splice answer starts endpoints signing none) at hz
      simp [filteredSplicedSigningOracle] at hz
      subst z
      rfl
  have hstep : ∀ t s, bad s = false →
      (fun z => (transform t z, if bad z.2 then none else some z.2)) <$>
        (original t).run s = (filtered t).run (some s) := by
    intro t s hs
    cases t with
    | inl uniform =>
      simp [original, filtered, transform, bad, hs,
        QueryImpl.add_apply_inl]
    | inr signing =>
      change (fun z => (if badSelectedHistory enc pp selector z.2 then none else z.1,
          selectedHistoryProjection enc pp selector z.2)) <$>
            (splicedSigningOracle hash enc K pp splice answer starts endpoints signing).run s =
        (filteredSplicedSigningOracle hash enc K pp selector splice answer starts
          endpoints signing).run (some s)
      exact
        selectedHistoryProjection_spliced_step_good hash enc K pp selector
          splice answer starts endpoints signing s hs
  have hinit : bad SyncSignatureUnforgeability.emptyHistory = false := by
    simp [bad, badSelectedHistory, SyncSignatureUnforgeability.emptyHistory]
  simpa [endpoints, pk, original, filtered, bad, hinit] using
    goodOutput_simulateQ_eq_filtered original filtered bad transform htransform
      hmono habsorb hstep (adv.forge pk) SyncSignatureUnforgeability.emptyHistory
      forgery history hgood

private theorem goodEvent_eq_filtered
    {α σ : Type}
    [MeasurableSpace (α × σ)] [MeasurableSpace (α × Option σ)]
    [MeasurableSingletonClass (α × σ)]
    [MeasurableSingletonClass (α × Option σ)]
    [DiscreteMeasurableSpace (α × σ)]
    [DiscreteMeasurableSpace (α × Option σ)]
    (original : ProbComp (α × σ))
    (filtered : ProbComp (α × Option σ)) (bad : σ → Bool)
    (event : α × σ → Bool)
    (hgood : ∀ z, event z = true → bad z.2 = false)
    (hpoint : ∀ z, bad z.2 = false →
      𝒟[original] {z} = 𝒟[filtered] {(z.1, some z.2)}) :
    𝒟[event <$> original] {true} =
      𝒟[(fun z => z.2.elim false (fun s => event (z.1, s))) <$> filtered] {true} := by
  classical
  let filteredEvent : α × Option σ → Bool :=
    fun z => z.2.elim false (fun s => event (z.1, s))
  change 𝒟[event <$> original] {true} = 𝒟[filteredEvent <$> filtered] {true}
  rw [evalDist_map_apply original Measurable.of_discrete (measurableSet_singleton true),
    evalDist_map_apply filtered Measurable.of_discrete (measurableSet_singleton true)]
  change 𝒟[original] {z | event z = true} =
    𝒟[filtered] {z | filteredEvent z = true}
  rw [← prEvent_eq_evalDist_of_discrete original (fun z => event z = true),
    ← prEvent_eq_evalDist_of_discrete filtered (fun z => filteredEvent z = true)]
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
  conv_rhs =>
    rw [ENNReal.tsum_prod']
  conv_lhs =>
    rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  rw [tsum_option _ ENNReal.summable]
  simp only [filteredEvent, Option.elim_none,
    Option.elim_some, Bool.false_eq_true, ite_false, zero_add]
  exact tsum_congr fun s => by
    by_cases he : event (a, s) = true
    · simp only [he, ite_true]
      simpa only [prEvent_eq_evalDist_singleton, Prod.mk.eta] using
        hpoint (a, s) (hgood (a, s) he)
    · simp [he]

/-- Filtering preserves exactly the selected true mass of a fixed spliced adaptive run. -/
private theorem runSpliced_selectedMass_eq_filtered
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) :
    𝒟[(fun out => jointChainObservation hash enc K (selector, out)) <$>
      runSpliced hash enc K adv pp splice answer starts] {true} =
    𝒟[(fun out => out.elim false
      (fun result => jointChainObservation hash enc K (selector, result))) <$>
      runFilteredSpliced hash enc K adv pp selector splice answer starts] {true} := by
  classical
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨hash.merkleRoot pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let original : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      splicedSigningOracle hash enc K pp splice answer starts endpoints
  let filtered : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      filteredSplicedSigningOracle hash enc K pp selector splice answer starts endpoints
  let raw := (simulateQ original (adv.forge pk)).run
    SyncSignatureUnforgeability.emptyHistory
  let rawFiltered := (simulateQ filtered (adv.forge pk)).run
    (some SyncSignatureUnforgeability.emptyHistory)
  let event : SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v) → Bool :=
    fun z => jointChainObservation hash enc K (selector, ⟨pk, sk, z.1, z.2⟩)
  let bad := badSelectedHistory (H := H) enc pp selector
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.History (Epoch h) M
    (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v) ×
    SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) := ⊤
  let : MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
    (GXMSS.Signature R H h v) ×
    Option (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))) := ⊤
  have hgood : ∀ z, event z = true → bad z.2 = false := by
    intro z hz
    have h := jointChainObservation_not_badSelectedHistory hash enc K selector
      (⟨pk, sk, z.1, z.2⟩ : Result PP H M R h v) hz
    simpa [bad, pk] using h
  have hpoint : ∀ z, bad z.2 = false →
      𝒟[raw] {z} = 𝒟[rawFiltered] {(z.1, some z.2)} := by
    intro z hz
    simpa only [← prEvent_eq_evalDist_singleton, raw, rawFiltered, original, filtered,
      endpoints, pk, bad] using
      splicedFiltered_good_raw_output hash enc K adv pp selector splice answer
        starts z.1 z.2 hz
  have heq := goodEvent_eq_filtered raw rawFiltered bad event hgood hpoint
  convert heq using 1
  · simp only [runSpliced, raw, event, original, endpoints, pk, sk,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  · simp only [runFilteredSpliced, rawFiltered, event, filtered, endpoints,
      pk, sk, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
    apply congrArg (fun mx : ProbComp Bool => 𝒟[mx] {true})
    apply bind_congr
    intro x
    cases x.2 <;> rfl

end GXMSS.Reductions
