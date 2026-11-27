/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Encoding.ActivatedClash
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Observation

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.SampleSpaces

/-! # Weak-key probability at the deferred key sampler -/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open scoped SLHDSA.SHAKE128s.Bridge.SharedExperiment.SampleSpaces
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

/-- Averaging the initial key of the filled, guarded experiment costs one honest-address mass. -/
theorem deferred_weak_mass (adv : Game.Adversary FIPS205.Answer PK) (reserve : Bool)
    (caps : Nat × Nat) (fallback : (s : FIPS205.core.PkSeed) →
      (input : LabCommon.Domain) → LabCommon.Range input) :
    (∫⁻ s, Pr{let r ← ((slhGraph FIPS205.core s).deferredFillDraw ($ᵗ Secret)
      (labProgram s adv reserve true caps (fallback s)))}[
        IsWeakKey FIPS205.params r.1.1.1.1.1.1.1]
      ∂𝒟[($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)]) ≤
      (1591788895347057694892543 : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  let graphKeygen := fun s : FIPS205.core.PkSeed =>
    (simulateQ (slhGraph FIPS205.core s).deferredImpl
      ((labScheme FIPS205.core FIPS205.deterministicRand s).keygen)).run ((∅, ∅), [])
  have rand : FIPS205.deterministicRand = (fun pk => pure pk.pkSeed) := by
    funext pk
    rfl
  have weakTapes (s : FIPS205.core.PkSeed) (a b : List HashOutput) :
      Pr{let t ← Native.nativeRun s adv reserve caps (fallback s) a b}[
        IsWeakKey FIPS205.params t.1.1.1] =
      Pr{let t ← graphKeygen s}[IsWeakKey FIPS205.params t.1.1] := by
    have h := (Native.native_initial_public_key_marginal s adv reserve caps (fallback s) a b
      ).prEvent_eq (IsWeakKey FIPS205.params)
    simpa only [graphKeygen, rand, prEvent_map] using h
  have fixed (s : FIPS205.core.PkSeed) :
      Pr{let r ← ((slhGraph FIPS205.core s).deferredFillDraw ($ᵗ Secret)
        (labProgram s adv reserve true caps (fallback s)))}[
          IsWeakKey FIPS205.params r.1.1.1.1.1.1.1] =
      Pr{let t ← graphKeygen s}[IsWeakKey FIPS205.params t.1.1] := by
    rw [labProgram_eq_native]
    let G := slhGraph FIPS205.core s
    let prg := Native.deferredProgram s adv reserve caps (fallback s)
    have forget : (fun r : Filled => r.1.1.1.1.1.1.1) <$> G.deferredFillDraw ($ᵗ Secret) prg =ᵈ
        (fun t => t.1.1.1.1.1.1) <$> (simulateQ G.deferredImpl prg).run ((∅, ∅), []) := by
      simp only [CanonicalGraph.deferredFillDraw, map_bind, map_pure]
      rw [map_eq_bind_pure_comp]
      apply EvalDistEq.bind_right
      intro x
      exact (OracleComp.EvalDistEq.bind_const _ _).trans (OracleComp.EvalDistEq.bind_const _ _)
    have kept := forget.prEvent_eq (IsWeakKey FIPS205.params)
    simp only [prEvent_map] at kept
    rw [kept]
    have h := (Native.native_deferred_marginal s adv reserve caps (fallback s) 0 0).prEvent_eq
      (fun t => IsWeakKey FIPS205.params t.1.1.1.1.1.1)
    rw [← h, prEvent_map]
    simpa only [NoticingTape.blockRunOf, DigestTape.padding, pure_bind, prEvent_map] using
      weakTapes s [] []
  simp_rw [fixed]
  rw [← prEvent_bind_bind_eq_lintegral_of_discrete]
  have weak := prEvent_deferred_fips_lab_keygen_then_isWeakKey_le
    (fun _ _ => (pure PUnit.unit : StateT
      (LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕ NodeKey FIPS205.core))
      ProbComp PUnit))
  simpa only [graphKeygen, FIPS205.deterministicRand, StateT.run_bind, StateT.run_pure,
    StateT.run_map, map_bind, map_pure, bind_pure_comp, prEvent_norm] using weak

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
