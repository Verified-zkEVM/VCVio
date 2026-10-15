/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.DataEncapMech
public import VCVio.CryptoFoundations.KeyEncapMech
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
public import VCVio.CryptoFoundations.KEMDEM.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# KEM + DEM Composition

This file defines the textbook KEM+DEM public-key encryption construction and the proof-ladders A1
reduction skeleton against the repository's KEM and one-time IND-CPA interfaces. Correctness of
the composition follows from that of its components, at every possible output and with
probability one, in any monad with the corresponding semantics.
-/

@[expose] public section

universe u v

open OracleSpec OracleComp ENNReal MeasureTheory

namespace KEMScheme

variable {m : Type → Type v} {K PK SK CKEM M CDEM : Type}

/-- Textbook KEM+DEM composition. The composed scheme inherits the KEM execution method. -/
def composeWithDEM [Monad m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM) :
    AsymmEncAlg m M PK SK (CKEM × CDEM) where
  keygen := kem.keygen
  encrypt := fun pk msg => do
    let (c₁, k) ← kem.encaps pk
    let c₂ ← dem.encrypt k msg
    return (c₁, c₂)
  decrypt := fun sk c => do
    let k? ← kem.decaps sk c.1
    match k? with
    | none => return none
    | some k => return some (← dem.decrypt k c.2)

section Correct

variable [DecidableEq K] [DecidableEq M] [Monad m] [LawfulMonad m]

/-- Reachable KEM and DEM round trips that always succeed make every reachable round trip of the
composed scheme succeed. -/
theorem support_correctnessExperiment_composeWithDEM [MonadAttach m] [ExactMonadAttach m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM)
    (hkem : ∀ b ∈ support kem.correctnessExperiment, b = true)
    (hdem : ∀ k msg, ∀ b ∈ support (dem.correctnessExperiment k msg), b = true)
    (msg : M) :
    ∀ b ∈ support ((kem.composeWithDEM dem).correctnessExperiment msg), b = true := by
  intro b hb
  simp only [AsymmEncAlg.correctnessExperiment, composeWithDEM, mem_support_bind_iff,
    mem_support_pure_iff, Prod.exists] at hb
  obtain ⟨pk, sk, hks, c₁, c₂, ⟨c₁', k, hck, c₂', hc₂, hc⟩, msg', ⟨kOpt, hkOpt, hmsg'⟩, rfl⟩ := hb
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hc
  have hk : kOpt = some k := by
    have hmem : decide (kOpt = some k) ∈ support kem.correctnessExperiment := by
      simp only [KEMScheme.correctnessExperiment, mem_support_bind_iff, mem_support_pure_iff,
        Prod.exists]
      exact ⟨pk, sk, hks, c₁, k, hck, kOpt, hkOpt, rfl⟩
    simpa using hkem _ hmem
  subst hk
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hmsg'
  obtain ⟨m', hm', rfl⟩ := hmsg'
  have hmem : decide (m' = msg) ∈ support (dem.correctnessExperiment k msg) := by
    simp only [DEMScheme.correctnessExperiment, mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨c₂, hc₂, m', hm', rfl⟩
  simpa using hdem k msg _ hmem

/-- Perfect correctness composes under any lawful measure semantics: a KEM and an externally
keyed DEM that each succeed with probability `1` give a composed scheme that succeeds with
probability `1`. -/
theorem perfectlyCorrect_composeWithDEM [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    (kem : KEMScheme m K PK SK CKEM) (dem : DEMScheme m K M CDEM)
    (hkem : Pr{let b ← kem.correctnessExperiment}[b = true] = 1)
    (hdem : ∀ k msg, Pr{let b ← dem.correctnessExperiment k msg}[b = true] = 1) (msg : M) :
    Pr{let b ← (kem.composeWithDEM dem).correctnessExperiment msg}[b = true] = 1 := by
  simp only [AsymmEncAlg.correctnessExperiment, composeWithDEM, KEMScheme.correctnessExperiment,
    DEMScheme.correctnessExperiment, bind_assoc, pure_bind, expect_norm, decide_eq_true_eq]
    at hkem hdem ⊢
  refine wp_eq_one_of_prEvent_eq_one kem.keygen
    (prEvent_eq_one_of_wp_eq_one _ (fun _ => wp_le_of_forall_le _ fun _ => prEvent_le_one _) hkem)
    (fun keys hkeys => ?_) fun _ => wp_le_of_forall_le _ fun _ => wp_le_of_forall_le _ fun _ =>
      wp_le_of_forall_le _ fun _ => prEvent_le_one _
  refine wp_eq_one_of_prEvent_eq_one (kem.encaps keys.1)
    (prEvent_eq_one_of_wp_eq_one _ (fun _ => prEvent_le_one _) hkeys)
    (fun ck hck => ?_) fun _ => wp_le_of_forall_le _ fun _ => wp_le_of_forall_le _ fun _ =>
      prEvent_le_one _
  refine wp_eq_one_of_prEvent_eq_one (dem.encrypt ck.2 msg)
    (prEvent_eq_one_of_wp_eq_one _ (fun _ => prEvent_le_one _) (hdem ck.2 msg))
    (fun c hc => ?_) fun _ => wp_le_of_forall_le _ fun _ => prEvent_le_one _
  refine wp_eq_one_of_prEvent_eq_one (kem.decaps keys.2 ck.1) hck (fun k hk => ?_)
    fun _ => prEvent_le_one _
  subst hk
  simpa only [expect_norm, Option.some.injEq] using hc

end Correct

section IND_CPA

variable {ι : Type} {spec : OracleSpec ι} [SampleableType K]

/-- Left KEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. -/
def composeWithDEM_toKEMLeftReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_OneTime_Adversary (kem.composeWithDEM dem)) :
    kem.IND_CPA_Adversary where
  State := M × adversary.State
  preChallenge pk := do
    let (m₀, _m₁, st) ← adversary.chooseMessages pk
    return (m₀, st)
  postChallenge st kc k := do
    let dc ← dem.encrypt k st.1
    adversary.distinguish st.2 (kc, dc)

/-- Right KEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. -/
def composeWithDEM_toKEMRightReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_OneTime_Adversary (kem.composeWithDEM dem)) :
    kem.IND_CPA_Adversary where
  State := M × adversary.State
  preChallenge pk := do
    let (_m₀, m₁, st) ← adversary.chooseMessages pk
    return (m₁, st)
  postChallenge st kc k := do
    let dc ← dem.encrypt k st.1
    adversary.distinguish st.2 (kc, dc)

/-- DEM reduction from a one-time IND-CPA adversary against the composed KEM+DEM PKE. It samples
the public key and KEM ciphertext during the message-selection phase so that the simulatee sees
the same `encaps`-then-`encrypt` effect order as the composed scheme. -/
def composeWithDEM_toDEMReduction
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (adversary : AsymmEncAlg.IND_CPA_OneTime_Adversary (kem.composeWithDEM dem)) :
    dem.IND_CPA_Adversary where
  State := CKEM × adversary.State
  chooseMessages := do
    let (pk, _sk) ← kem.keygen
    let (m₀, m₁, st) ← adversary.chooseMessages pk
    let (kc, _k) ← kem.encaps pk
    return (m₀, m₁, (kc, st))
  distinguish st dc := do
    adversary.distinguish st.2 (st.1, dc)

/-- Proof-ladders A1 reduction statement: the one-time IND-CPA advantage of textbook KEM+DEM is
bounded by two KEM IND-CPA advantages plus one DEM IND-CPA advantage, using the canonical
left/right and DEM reductions defined above.

The probability-free games and shared hybrid argument live in
`VCVio.CryptoFoundations.KEMDEM.Measure`. This theorem calibrates them to the bundled runtime.

The runtime coherence hypotheses state directly that its measures preserve `pure` and measurable
binds, agree with the canonical `ProbComp` measure on lifted public randomness, and are total on
the Boolean games used below. -/
theorem ind_cpa_one_time_bias_advantage_compose_with_dem_le
    (kem : KEMScheme (OracleComp spec) K PK SK CKEM)
    (dem : DEMScheme (OracleComp spec) K M CDEM)
    (runtime : ProbCompRuntime (OracleComp spec))
    (adversary : AsymmEncAlg.IND_CPA_OneTime_Adversary (kem.composeWithDEM dem))
    (heval_pure : ∀ {α : Type} [MeasurableSpace α] (a : α),
        runtime.evalDist (pure a : OracleComp spec α) = Measure.dirac a)
    (heval_bind : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
        (mx : OracleComp spec α) (f : α → OracleComp spec β),
        Measurable (fun a => runtime.evalDist (f a)) →
        runtime.evalDist (mx >>= f) =
          Measure.bind (runtime.evalDist mx) fun a => runtime.evalDist (f a))
    (heval_liftProbComp : ∀ {α : Type} [MeasurableSpace α] (pc : ProbComp α),
        runtime.evalDist (runtime.liftProbComp pc) = 𝒟[pc])
    (hno_fail : ∀ (mx : OracleComp spec Bool),
        runtime.evalDist mx {true} + runtime.evalDist mx {false} = 1) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (kem.composeWithDEM dem) runtime adversary ≤
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMLeftReduction dem adversary) +
      kem.IND_CPA_Advantage runtime (kem.composeWithDEM_toKEMRightReduction dem adversary) +
      dem.IND_CPA_Advantage runtime
        (kem.composeWithDEM_toDEMReduction dem adversary) := by
  let : MeasurableSpace K := ⊤
  let : MeasurableSpace (CKEM × K) := ⊤
  let : MeasurableSpace (PK × M × M × adversary.State) := ⊤
  let : EvalDistSemantics (OracleComp spec) := {
    denote mx := runtime.evalDist mx
    apply_univ_le_one mx := runtime.evalDist_apply_univ_le_one mx }
  let : LawfulEvalDistSemantics (OracleComp spec) := {
    denote_pure a := heval_pure a
    denote_bind mx f hf := heval_bind mx f hf }
  have evalDist_eq_runtime {α : Type} [MeasurableSpace α] (mx : OracleComp spec α) :
      𝒟[mx] = runtime.evalDist mx := rfl
  let prepare : OracleComp spec (PK × M × M × adversary.State) := do
    let (pk, _) ← kem.keygen
    let (m₀, m₁, st) ← adversary.chooseMessages pk
    pure (pk, m₀, m₁, st)
  let encaps (p : PK × M × M × adversary.State) := kem.encaps p.1
  let finish (p : PK × M × M × adversary.State) (kc : CKEM) (k : K) (side : Bool) := do
    let dc ← dem.encrypt k (if side then p.2.1 else p.2.2.1)
    adversary.distinguish p.2.2.2 (kc, dc)
  have hcoin (b : Bool) : 𝒟[runtime.liftProbComp ($ᵗ Bool)] {b} = 1 / 2 := by
    rw [evalDist_eq_runtime, heval_liftProbComp, SampleableType.evalDist_uniformSample,
      ProbabilityTheory.uniformOn_univ_apply_singleton]
    simp [Fintype.card_bool]
  have hkey : 𝒟[runtime.liftProbComp ($ᵗ K)] Set.univ = 1 := by
    rw [evalDist_eq_runtime, heval_liftProbComp, SampleableType.evalDist_uniformSample]
    simp
  have htotal (real side : Bool) :
      𝒟[KEMDEM.hybrid prepare encaps finish (runtime.liftProbComp ($ᵗ K)) real side] {true} +
      𝒟[KEMDEM.hybrid prepare encaps finish (runtime.liftProbComp ($ᵗ K)) real side] {false} =
        1 := by
    exact hno_fail
      (KEMDEM.hybrid prepare encaps finish (runtime.liftProbComp ($ᵗ K)) real side)
  have h := KEMDEM.bias_compose_le prepare encaps finish
    (runtime.liftProbComp ($ᵗ Bool)) (runtime.liftProbComp ($ᵗ K))
    (hcoin true) (hcoin false) hkey htotal
  have hnot (b : Bool) (x y : M) : (if !b then x else y) = (if b then y else x) := by
    cases b <;> rfl
  simpa only [evalDist_eq_runtime, Measure.boolBias,
    AsymmEncAlg.IND_CPA_OneTime_Advantage, KEMScheme.IND_CPA_Advantage,
    DEMScheme.IND_CPA_Advantage,
    AsymmEncAlg.IND_CPA_OneTime_Game, KEMScheme.IND_CPA_Game, DEMScheme.IND_CPA_Game,
    KEMDEM.composedGame, KEMDEM.kemGame, KEMDEM.demGame, prepare, encaps, finish,
    composeWithDEM, composeWithDEM_toKEMLeftReduction, composeWithDEM_toKEMRightReduction,
    composeWithDEM_toDEMReduction, bind_assoc, pure_bind, ite_true, Bool.false_eq_true,
    ite_false, hnot] using h

end IND_CPA

end KEMScheme
