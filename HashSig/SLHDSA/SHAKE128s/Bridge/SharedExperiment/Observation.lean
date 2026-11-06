/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Defs
public import HashSig.SLHDSA.SHAKE128s.Statement.FIPS205
public import HashSig.SLHDSA.Security.WeakKeyBound

import all HashSig.SLHDSA.Security.WeakKeyBound

/-!
# Complete source observations under one cached interpretation

The full original outcome and source vector follow from the recorded program equality.
A single arbitrary cached handler and continuation retain the joint result and final cache.
-/

public section

open OracleComp OracleSpec
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal

universe v

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

/-- The original outcome and complete source vector agree as one free-oracle program. -/
theorem fullProgram {Output PK SK : Type} (scheme : Game.ExternalScheme Output PK SK)
    (adversary : Game.Adversary Output PK) :
    Game.experimentBySource scheme adversary =
      legacyObservation <$> canonicalExperiment scheme adversary := rfl

/-- The same cached handler and continuation observe the full same result and final cache. -/
theorem sharedContinuation {Output PK SK Cache β : Type} {m : Type → Type v}
    [Monad m] [LawfulMonad m] (scheme : Game.ExternalScheme Output PK SK)
    (adversary : Game.Adversary Output PK)
    (handler : QueryImpl (Game.World Output) (StateT Cache m)) (initial : Cache)
    (next : (Game.Outcome × SourceCounts) × Cache → m β) :
    ((simulateQ handler (canonicalExperiment scheme adversary)).run initial >>=
      fun result => next (legacyObservation result.1, result.2)) =
      ((simulateQ handler (Game.experimentBySource scheme adversary)).run initial >>= next) := by
  have equality := congrArg (fun program =>
    ((simulateQ handler program).run initial >>= next)) (fullProgram scheme adversary)
  simpa only [simulateQ_map, StateT.run_map, bind_map_left] using equality.symm


/-! ## Original byte key-generation interfaces -/

/-- The actual empty-cache key-generation marginal retains the complete coherent key pair. -/
theorem evalDist_original_fips_keygen_keys :
  letI : MeasurableSpace (SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core) := ⊤
  𝒟[Prod.fst <$> ((simulateQ
    (RandomOracleModel.impl (List Byte) FIPS205.Answer)
    FIPS205.scheme.keygen).run ∅)] =
  𝒟[(do
    let pkSeed ← $ᵗ FIPS205.core.PkSeed
    let skSeed ← $ᵗ FIPS205.core.SkSeed
    let skPrf ← $ᵗ FIPS205.core.SkPrf
    let root ← $ᵗ FIPS205.core.Y
    pure ((⟨skSeed, skPrf, pkSeed, root⟩ : SecretKeyCore FIPS205.core),
      (⟨pkSeed, root⟩ : PublicKeyCore FIPS205.core)) :
    ProbComp (SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core))] := by
  let : MeasurableSpace (SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core) := ⊤
  let e : FIPS205.core.SkSeed ≃ FIPS205.core.Y := Equiv.refl _
  apply EvalDistEq.evalDist_eq
  change Prod.fst <$> ((simulateQ (shakeSpec FIPS205.params).romImpl
    (Prod.swap <$> simulateQ (encImpl FIPS205.params)
      (romScheme FIPS205.core e FIPS205.deterministicRand
        ($ᵗ FIPS205.core.PkSeed)).keygen)).run ∅) =ᵈ _
  rw [romScheme_keygen]
  simp only [simulateQ_map, StateT.run_map, simulateQ_bind, StateT.run_bind,
    simulateQ_encImpl_liftM, simulateQ_romImpl_liftM_run,
    map_bind, bind_map_left, Functor.map_map, bind_pure_comp]
  apply EvalDistEq.bind_right
  intro pkSeed
  apply EvalDistEq.bind_right
  intro skSeed
  apply EvalDistEq.bind_right
  intro skPrf
  have root := (keygen_encoded_fresh_root FIPS205.params
    (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds
    (by decide) pkSeed skSeed).2
  simpa only [Functor.map_map, Function.comp_def, Prod.swap, e] using
    root.map (fun root => ((⟨skSeed, skPrf, pkSeed, root⟩ : SecretKeyCore FIPS205.core),
      (⟨pkSeed, root⟩ : PublicKeyCore FIPS205.core)))

/-- The union-ledger and secret-address count for SLH-DSA-SHAKE-128s. -/
private theorem honestAdrsCount_fips205 :
    honestAdrsCount FIPS205.params = 1591788895347057694892543 := by
  have length : FIPS205.params.params.len = 35 := by decide
  have trees : xmssTreeCount FIPS205.params.params = 18049651735527937 := by
    have h := xmssTreeCount_mul_pred FIPS205.params.params FIPS205.params.valid
    change xmssTreeCount FIPS205.params.params * (2 ^ 9 - 1) = 2 ^ 63 - 1 at h
    generalize xmssTreeCount FIPS205.params.params = total at h ⊢
    norm_num at h
    omega
  rw [honestAdrsCount_eq]
  simp only [targetCount, wotsInstanceCount_eq_xmssTreeCount_mul, trees, length, Params.w]
  norm_num [FIPS205.params, FipsParameterSet.validatedParams, FipsParameterSet.params]

/-- An arbitrary continuation shares the actual byte cache and retains the original key pair. -/
theorem prEvent_original_fips_keygen_then_isWeakKey_le :
  ∀ {α : Type}
    (continuation : (SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core) →
      StateT ((shakeSpec FIPS205.params).QueryCache) ProbComp α),
    Pr{let z ← ((do
      let keys ← simulateQ
        (RandomOracleModel.impl (List Byte) FIPS205.Answer)
        FIPS205.scheme.keygen
      let value ← continuation keys
      pure (keys, value)).run ∅)}[
        IsWeakKey FIPS205.params z.1.1.2] ≤
      (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  intro α continuation
  let : MeasurableSpace (SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core) := ⊤
  have forgotten : (fun z => z.1.1) <$> ((do
      let keys ← simulateQ (RandomOracleModel.impl (List Byte) FIPS205.Answer)
        FIPS205.scheme.keygen
      let value ← continuation keys
      pure (keys, value)).run ∅) =ᵈ
      Prod.fst <$> ((simulateQ (RandomOracleModel.impl (List Byte) FIPS205.Answer)
        FIPS205.scheme.keygen).run ∅) := by
    simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    simpa only [bind_pure_comp] using EvalDistEq.bind_right
      ((simulateQ (RandomOracleModel.impl (List Byte) FIPS205.Answer)
        FIPS205.scheme.keygen).run ∅) (fun z =>
          OracleComp.EvalDistEq.map_const ((continuation z.1).run z.2) z.1)
  have keys := EvalDistEq.of_evalDist_eq evalDist_original_fips_keygen_keys
  have equal := (forgotten.trans keys).prEvent_eq
    (fun keys => IsWeakKey FIPS205.params keys.2)
  simp only [prEvent_norm] at equal
  simp only [bind_pure_comp]
  rw [equal]
  let : MeasurableSpace FIPS205.core.PkSeed := ⊤
  rw [prEvent_bind _ _ Measurable.of_discrete]
  simp only [OracleComp.prEvent_bind_const]
  have count := honestAdrsCount_fips205
  simpa only [count, weakKeyMass, Nat.cast_pow, Nat.cast_ofNat] using
    (lintegral_weakKeyMass_le (vp := FIPS205.params) (by decide))

/-- A same-state continuation keeps the weak mass of the initial generated public key. -/
theorem prEvent_deferred_fips_lab_keygen_then_isWeakKey_le :
  ∀ {alpha : Type}
    (continuation : FIPS205.core.PkSeed →
      ((PublicKeyCore FIPS205.core) × (PublicKeyCore FIPS205.core)) →
      StateT (LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core))
        ProbComp alpha),
    Pr{let result ← (do
       let sampledPublicSeed ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let z ← ((do
         let keys ← simulateQ (slhGraph FIPS205.core sampledPublicSeed).deferredImpl
           (labScheme FIPS205.core FIPS205.deterministicRand sampledPublicSeed).keygen
         let value ← continuation sampledPublicSeed keys
         pure (keys, value)).run ((∅, ∅), []))
       pure (sampledPublicSeed, z))}[
      IsWeakKey FIPS205.params result.2.1.1.1] ≤
      (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  intro alpha continuation
  let : MeasurableSpace
    (PublicKeyCore FIPS205.core × PublicKeyCore FIPS205.core) := ⊤
  have root :
    ∀ (sampledPublicSeed : FIPS205.core.PkSeed),
      (fun result => result.1) <$>
        ((simulateQ (slhGraph FIPS205.core sampledPublicSeed).deferredImpl
          (labScheme FIPS205.core FIPS205.deterministicRand sampledPublicSeed).keygen).run
            ((∅, ∅), [])) =ᵈ
        (do
          let root ← ($ᵗ FIPS205.core.Y : ProbComp FIPS205.core.Y)
          pure ((⟨sampledPublicSeed, root⟩ : PublicKeyCore FIPS205.core),
            (⟨sampledPublicSeed, root⟩ : PublicKeyCore FIPS205.core))) := by
    intro sampledPublicSeed
    have root := evalDist_deferred_labKeygen_eq_uniform FIPS205.core sampledPublicSeed
      (rootKeySeparated_shakeCore
        (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds)
    simpa only [labScheme, simulateQ_bind, simulateQ_pure, simulateQ_map,
      StateT.run_map, StateT.run_bind,
      StateT.run_pure, map_bind, map_pure, bind_pure_comp, Functor.map_map,
      Function.comp_def] using root.map (fun root =>
        ((⟨sampledPublicSeed, root⟩ : PublicKeyCore FIPS205.core),
          (⟨sampledPublicSeed, root⟩ : PublicKeyCore FIPS205.core)))
  have forgotten (s : FIPS205.core.PkSeed) :
      (fun z => z.1.1) <$> ((do
        let keys ← simulateQ (slhGraph FIPS205.core s).deferredImpl
          (labScheme FIPS205.core FIPS205.deterministicRand s).keygen
        let value ← continuation s keys
        pure (keys, value)).run ((∅, ∅), [])) =ᵈ
      Prod.fst <$> ((simulateQ (slhGraph FIPS205.core s).deferredImpl
        (labScheme FIPS205.core FIPS205.deterministicRand s).keygen).run
          ((∅, ∅), [])) := by
    simp only [StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    simpa only [bind_pure_comp] using EvalDistEq.bind_right
      ((simulateQ (slhGraph FIPS205.core s).deferredImpl
        (labScheme FIPS205.core FIPS205.deterministicRand s).keygen).run ((∅, ∅), []))
      (fun z => OracleComp.EvalDistEq.map_const ((continuation s z.1).run z.2) z.1)
  have equal (s : FIPS205.core.PkSeed) :=
    ((forgotten s).trans (root s)).prEvent_eq
      (fun keys => IsWeakKey FIPS205.params keys.1)
  simp only [prEvent_norm] at equal
  let : MeasurableSpace FIPS205.core.PkSeed := ⊤
  simp only [prEvent_norm]
  rw [prEvent_bind _ _ Measurable.of_discrete]
  simp only [prEvent_norm, equal]
  have count := honestAdrsCount_fips205
  simpa only [count, weakKeyMass, Nat.cast_pow, Nat.cast_ofNat] using
    (lintegral_weakKeyMass_le (vp := FIPS205.params) (by decide))

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
