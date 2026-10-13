/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Independent correctness probes

A one-epoch unit-message scheme suffices to distinguish the quantifiers of Definition 7.
The mixed scheme draws one fair bit: the true key always verifies and the false key never does.
Thus averaging accepts with probability one half, but the false key violates correctness at
error one half. All observations use the canonical `ProbComp` runtime.

A Boolean configuration is captured by all three algorithms of a separate family. Its correctness
holds for every configuration and every epoch type, without epoch equality or finiteness
assumptions.
-/

public section

namespace SyncSignatureProbe

open ENNReal OracleComp SyncSignatureAlg

/-- One-epoch honest signing always returns the accepted unit signature. -/
@[expose] def honest : SyncSignatureAlg ProbComp Unit Unit Unit Unit (Fin 1) where
  keygen := pure ((), ())
  sign _ _ _ := pure (some ())
  verify _ _ _ _ := true

/-- One-epoch signing always returns an explicit failure. -/
@[expose] def alwaysFails : SyncSignatureAlg ProbComp Unit Unit Unit Unit (Fin 1) where
  keygen := pure ((), ())
  sign _ _ _ := pure none
  verify _ _ _ _ := true

/-- A fair bit selects either an always-accepted or always-rejected public key. -/
@[expose] def mixed : SyncSignatureAlg ProbComp Unit Bool Unit Unit (Fin 1) where
  keygen := (fun b => (b, ())) <$> ($ᵗ Bool)
  sign _ _ _ := pure (some ())
  verify pk _ _ _ := pk

/-- The honest scheme's concrete key has probability one. -/
theorem honest_key_probability :
    ProbCompRuntime.probComp.evalDist
      ((fun ks => ks = ((), ())) <$> honest.keygen) {True} = 1 := by
  simp [honest]

/-- Every epoch and message under the honest key has acceptance mass one. -/
theorem honest_success (ep : Fin 1) (msg : Unit) :
    honest.successMass ProbCompRuntime.probComp ((), ()) ep msg = 1 := by
  simp [successMass, honest, accepts]

/-- Honest signing has zero correctness error. -/
theorem honest_complete_zero : honest.Complete ProbCompRuntime.probComp 0 := by
  intro ks hks ep msg
  simpa using le_of_eq (honest_success ep msg).symm

/-- Explicit failure has zero acceptance mass even with an always-true verifier. -/
theorem alwaysFails_success (ep : Fin 1) (msg : Unit) :
    alwaysFails.successMass ProbCompRuntime.probComp ((), ()) ep msg = 0 := by
  simp [successMass, alwaysFails, accepts]

/-- A returned-failure signer cannot satisfy zero-error correctness. -/
theorem not_alwaysFails_complete_zero : ¬ alwaysFails.Complete ProbCompRuntime.probComp 0 := by
  intro h
  have hkey : alwaysFails.Generated ProbCompRuntime.probComp ((), ()) := by
    simp [Generated, alwaysFails]
  have hbad := h ((), ()) hkey 0 ()
  simp [alwaysFails_success] at hbad

/-- Both mixed-scheme keys have probability exactly one half. -/
theorem mixed_key_probability (b : Bool) :
    ProbCompRuntime.probComp.evalDist
      ((fun ks => ks = (b, ())) <$> mixed.keygen) {True} = 2⁻¹ := by
  rw [ProbCompRuntime.probComp_evalDist]
  simp only [mixed, Functor.map_map, Prod.mk.injEq, and_true]
  rw [← prEvent_eq_evalDist_map]
  exact SampleableType.prEvent_uniformSample_eq_singleton b

/-- Both mixed-scheme keys are producible, including the bad key. -/
theorem mixed_generated (b : Bool) : mixed.Generated ProbCompRuntime.probComp (b, ()) := by
  rw [Generated, mixed_key_probability]
  norm_num

/-- The good key accepts with probability one. -/
theorem mixed_good_success (ep : Fin 1) (msg : Unit) :
    mixed.successMass ProbCompRuntime.probComp (true, ()) ep msg = 1 := by
  simp [successMass, mixed, accepts]

/-- The bad key accepts with probability zero. -/
theorem mixed_bad_success (ep : Fin 1) (msg : Unit) :
    mixed.successMass ProbCompRuntime.probComp (false, ()) ep msg = 0 := by
  simp [successMass, mixed, accepts]

/-- Averaging fixed-key verification observations over the generated key distribution. -/
@[expose] noncomputable def mixedAverage (ep : Fin 1) (msg : Unit) : ℝ≥0∞ :=
  ProbCompRuntime.probComp.evalDist (do
    let ks ← mixed.keygen
    let out ← mixed.sign ks.2 ep msg
    return mixed.accepts ks.1 ep msg out) {true}

/-- Averaged acceptance of the mixed scheme is exactly one half. -/
theorem mixed_average_probability (ep : Fin 1) (msg : Unit) : mixedAverage ep msg = 2⁻¹ := by
  simp [mixedAverage, mixed, accepts]

/-- The canonical surface keygen-sign-verify execution also accepts with probability one half. -/
theorem mixed_runtime_average_probability (ep : Fin 1) (msg : Unit) :
    ProbCompRuntime.probComp.evalDist (do
      let ks ← mixed.keygen
      let out ← mixed.sign ks.2 ep msg
      pure (mixed.accepts ks.1 ep msg out)) {true} = (2⁻¹ : ℝ≥0∞) := by
  simp [mixed, accepts]

/-- The average bound at error one half holds at every epoch and message. -/
theorem mixed_average_half : ∀ ep msg, 1 - (2⁻¹ : ℝ≥0∞) ≤ mixedAverage ep msg := by
  intro ep msg
  rw [mixed_average_probability]
  norm_num

/-- The per-key correctness bound at error one half fails at the producible bad key. -/
theorem not_mixed_complete_half : ¬ mixed.Complete ProbCompRuntime.probComp (2⁻¹) := by
  intro h
  have hbad := h (false, ()) (mixed_generated false) 0 ()
  rw [mixed_bad_success] at hbad
  norm_num at hbad

/-- Average correctness at error one half does not imply per-key correctness. -/
theorem mixed_separates :
    (∀ ep msg, 1 - (2⁻¹ : ℝ≥0∞) ≤ mixedAverage ep msg) ∧
      ¬ mixed.Complete ProbCompRuntime.probComp (2⁻¹) :=
  ⟨mixed_average_half, not_mixed_complete_half⟩

/-- A configuration captured by key generation, signing and verification at arbitrary epochs. -/
@[expose] def configured (E : Type) (cfg : Bool) :
    SyncSignatureAlg ProbComp Unit Bool Bool Bool E where
  keygen := pure (cfg, cfg)
  sign sk _ _ := pure (some (cfg && sk))
  verify pk _ _ sig := (pk == cfg) && (sig == (cfg && pk))

/-- The configured family produces exactly the key pair determined by its configuration. -/
theorem configured_generated_iff (E : Type) (cfg : Bool) (ks : Bool × Bool) :
    (configured E cfg).Generated ProbCompRuntime.probComp ks ↔ ks = (cfg, cfg) := by
  by_cases h : ks = (cfg, cfg)
  · simp [Generated, configured, h]
  · simp [Generated, configured, h, Ne.symm h]

/-- Every configuration has zero correctness error, without any structure on its epoch type. -/
theorem configured_complete_zero (E : Type) :
    ∀ cfg, (configured E cfg).Complete ProbCompRuntime.probComp 0 := by
  intro cfg ks hks ep msg
  have hkey : ks = (cfg, cfg) := (configured_generated_iff E cfg ks).mp hks
  subst ks
  simp [successMass, configured, accepts]

end SyncSignatureProbe
