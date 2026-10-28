/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Games
public import VCVio.Schemes.BLS.Guess

/-! # Identifying BLS EUF-CMA advantage with the indexed game

The standard ROM experiment and the indexed execution share one lazy hash cache across
direct queries, signing, and final verification. Bilinear nondegeneracy identifies the
verification equation with the honest signature equation used for extraction.
-/

public section

open OracleComp OracleSpec

namespace BLS

private theorem realOracle_run_hash {F G M : Type} [SMul F G]
    [SampleableType G] [DecidableEq M] (x : F) (msg : M)
    (s : List M × (M →ₒ G).QueryCache) :
    (realOracle x (.inl (.inr msg))).run s =
      (fun z => (z.1, s.1, z.2)) <$> ((M →ₒ G).randomOracle msg).run s.2 := by
  simp only [realOracle, QueryImpl.flattenStateT, OracleSpec.romImpl,
    QueryImpl.add_apply_inl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
    StateT.run_monadLift, monadLift_self, StateT.run_map, StateT.run_mk,
    Functor.map_map, bind_pure_comp]
  rfl

private theorem realOracle_withFinalHash {F G M : Type} [SMul F G]
    [SampleableType G] [DecidableEq M] (x : F)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) (M × G))
    (s : List M × (M →ₒ G).QueryCache) :
    (simulateQ (realOracle x) (withFinalHash oa)).run s =
      (simulateQ (realOracle x) oa).run s >>= fun z =>
        (fun h => ((z.1, h.1), z.2.1, h.2)) <$>
          ((M →ₒ G).randomOracle z.1.1).run z.2.2 := by
  simp only [withFinalHash, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  apply bind_congr
  intro z
  rw [realOracle_run_hash]
  simp only [bind_pure_comp, Functor.map_map]

private theorem verify_run_realOracle {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) (x : F)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) (M × G₁))
    (c : (M →ₒ G₁).QueryCache) (valid : G₁ → G₁ → Bool) :
    (simulateQ (M →ₒ G₁).romImpl (do
      let (out, log) ← (scheme e g₁ g₂).runWithSigningOracle pk x oa
      let h ← (M →ₒ G₁).query out.1
      return decide (out.1 ∉ log.map (fun entry => entry.1)) && valid out.2 h)).run' c =
    (fun z => decide (z.1.1.1 ∉ z.2.1) && valid z.1.1.2 z.1.2) <$>
      (simulateQ (realOracle x) (withFinalHash oa)).run ([], c) := by
  rw [realOracle_withFinalHash, ← runWithSigningOracle_realOracle e g₁ g₂ pk x oa c []]
  simp only [List.nil_append, map_bind, bind_map_left, Functor.map_map]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_pure_comp]
  apply bind_congr
  intro z
  rw [simulateQ_map]
  rw [show simulateQ (M →ₒ G₁).romImpl ((M →ₒ G₁).query z.1.1.1) =
    (M →ₒ G₁).randomOracle z.1.1.1 from roSim.simulateQ_liftM_spec_query _ _]
  simp only [StateT.run_map, Functor.map_map]

/-- The standard EUF-CMA advantage is the real shared-cache game, including the final
verification hash and the signing-log freshness test. -/
theorem unforgeableAdvantage_eq_realOracle {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂)) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁)) A =
      Pr{let x ← ($ᵗ F : ProbComp F)
         let z ← (simulateQ (realOracle x)
           (withFinalHash (A.main (x • g₁, x • g₂)))).run ([], ∅)}[
        z.1.1.1 ∉ z.2.1 ∧ e z.1.1.2 g₂ = e z.1.2 (x • g₂)] := by
  classical
  rw [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← prEvent_eq_evalDist_singleton]
  have hexp : SignatureAlg.unforgeableExperiment A = do
      let x ← (liftM ($ᵗ F : ProbComp F) : OracleComp (unifSpec + (M →ₒ G₁)) F)
      let (out, log) ← (scheme e g₁ g₂).runWithSigningOracle
        (x • g₁, x • g₂) x (A.main (x • g₁, x • g₂))
      let h ← (M →ₒ G₁).query out.1
      return decide (out.1 ∉ log.map (fun entry => entry.1)) &&
        decide (e out.2 g₂ = e h (x • g₂)) := by
    simp only [SignatureAlg.unforgeableExperiment, scheme, bind_assoc, pure_bind,
      QueryLog.wasQueried_eq_decide_mem_map_fst, decide_not]
    apply bind_congr
    intro x
    apply bind_congr
    intro z
    apply bind_congr
    intro h
    congr 3
    rw [decide_eq_decide]
  rw [hexp, simulateQ_bind, roSim.run'_liftM_bind]
  simp only [map_bind]
  congr 1
  apply bind_congr
  intro x
  have hrun := verify_run_realOracle e g₁ g₂ (x • g₁, x • g₂) x
    (A.main (x • g₁, x • g₂)) ∅ (fun σ h => decide (e σ g₂ = e h (x • g₂)))
  have hm := congrArg (fun oc : ProbComp Bool => (fun b => b = true) <$> oc) hrun
  simpa only [Functor.map_map, Bool.and_eq_true, decide_eq_true_eq] using hm

/-- Under generator bijectivity and a nonzero generator pairing, the standard advantage is
the scalar-sampled indexed winning game used by the co-CDH reduction. -/
theorem unforgeableAdvantage_eq_indexed {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂))
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁)) A =
      Pr{let x ← ($ᵗ F : ProbComp F)
         let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • g₁)
           (fun ρ => x • (ρ • g₁)) none)
           (withFinalHash (A.main (x • g₁, x • g₂)))).run OracleState.empty}[
        Winning (x • ·) z] := by
  rw [unforgeableAdvantage_eq_realOracle]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro x
  have hproj := simulateQ_indexedOracle_realOracle_proj x none
    (withFinalHash (A.main (x • g₁, x • g₂))) OracleState.empty
  have hempty : valueCache (OracleState.empty : OracleState G₁ M) = ∅ := rfl
  simp only [show (OracleState.empty : OracleState G₁ M).signed = [] from rfl, hempty] at hproj
  rw [← hproj]
  simp only [prEvent_map, pairing_eq_iff e g₁ g₂ hg₁.2 he]
  have hmap := simulateQ_indexedOracle_map_evalDistEq (· • g₁ : F → G₁)
    (fun _ => $ᵗ F) (fun _ => $ᵗ G₁) (fun _ => smul_uniformSample_evalDistEq g₁ hg₁)
    id (x • ·) none (withFinalHash (A.main (x • g₁, x • g₂))) OracleState.empty
  have hmempty : (OracleState.empty : OracleState F M).map (· • g₁) = OracleState.empty := by
    apply OracleState.ext <;> simp [OracleState.map, OracleState.empty]
    rfl
  rw [hmempty] at hmap
  have hp := hmap.prEvent_eq (Winning (x • ·))
  simp only [prEvent_map, Winning, OracleState.map, Function.comp_def, id_eq] at hp ⊢
  exact hp.symm

end BLS
