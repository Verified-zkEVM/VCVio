/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Aggregate.Execution
public import VCVio.Schemes.BLS.GameIdentification

/-! # Identifying aggregate BLS chosen-key advantage

The chosen-key experiment shares one lazy random-oracle cache across direct queries,
signing, and the aggregate verification hashes. Changing its uniformly sampled group
answers to scalar multiples of a generator gives the indexed game used by the reduction.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

/-- The indexed chosen-key winning event: an unsigned message under the honest key,
distinct listed messages, and acceptance of the aggregate pairing equation. -/
@[expose] def Winning {F G₁ G₂ Gₜ M V : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ pk : G₂)
    (z : ((List (G₂ × M) × G₁) × Gₜ) × OracleState V M) : Prop :=
  (∃ msg, (pk, msg) ∈ z.1.1.1 ∧ msg ∉ z.2.signed) ∧
    (z.1.1.1.map Prod.snd).Nodup ∧ e z.1.1.2 g₂ = z.1.2

private theorem realOracle_hashes {F G M α : Type} [SMul F G]
    [SampleableType G] [DecidableEq M] (x : F) (oa : OracleComp (M →ₒ G) α)
    (l : List M) (c : (M →ₒ G).QueryCache) :
    (simulateQ (realOracle x)
      (simulateQ (fun msg => (liftM (((unifSpec + (M →ₒ G)) + (M →ₒ G)).query
        (.inl (.inr msg))) : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) G)) oa)).run (l, c) =
      (fun z => (z.1, l, z.2)) <$> (simulateQ (M →ₒ G).randomOracle oa).run c := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply
    (impl := fun msg => realOracle x (.inl (.inr msg)))
    (fun msg => simulateQ_spec_query (realOracle x) (.inl (.inr msg)))]
  have h := map_run_simulateQ_eq_of_query_map_eq (M →ₒ G).randomOracle
    (fun msg => realOracle x (.inl (.inr msg))) (fun c => (l, c))
    (fun msg c => (BLS.realOracle_run_hash x msg (l, c)).symm) oa c
  exact h.symm

private theorem realOracle_withFinalPairings {F G₁ G₂ Gₜ M : Type}
    [Field F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (x : F)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁))
      (List (G₂ × M) × G₁)) (s : List M × (M →ₒ G₁).QueryCache) :
    (simulateQ (realOracle x) (withFinalPairings e oa)).run s =
      (simulateQ (realOracle x) oa).run s >>= fun z =>
        (fun h => ((z.1, h.1), z.2.1, h.2)) <$>
          (simulateQ (M →ₒ G₁).randomOracle (pairingSum e z.1.1)).run z.2.2 := by
  simp only [withFinalPairings, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  apply bind_congr
  intro z
  rw [realOracle_hashes]
  simp only [bind_pure_comp, Functor.map_map]

private theorem runWithSigningOracle_eq {F G₁ G₂ Gₜ M α : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ pk : G₂) (x : F)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)) α) :
    (scheme e g₂).toSignatureAlg.runWithSigningOracle pk x oa =
      (BLS.scheme e g₁ g₂).runWithSigningOracle (0, pk) x oa := rfl

private theorem aggregateVerify_evalDistEq {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₂ : G₂) (pairs : List (G₂ × M)) (σ : G₁)
    (c : (M →ₒ G₁).QueryCache) :
    (simulateQ (M →ₒ G₁).romImpl ((scheme e g₂).aggregateVerify pairs σ)).run' c =ᵈ
      (fun z => decide (pairs.map Prod.snd).Nodup && decide (e σ g₂ = z.1)) <$>
        (simulateQ (M →ₒ G₁).randomOracle (pairingSum e pairs)).run c := by
  by_cases hd : (pairs.map Prod.snd).Nodup
  · simp only [scheme, hd, not_true_eq_false, ↓reduceIte, StateT.run'_eq,
      bind_pure_comp, decide_true, Bool.true_and, simulateQ_map, StateT.run_map,
      Functor.map_map]
    rw [OracleSpec.romImpl, QueryImpl.simulateQ_add_liftM_right]
  · simp only [scheme, hd, not_false_eq_true, ↓reduceIte, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure, decide_false, Bool.false_and]
    exact (OracleComp.EvalDistEq.map_const _ false).symm

open scoped Classical in
private theorem verify_run_realOracle {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ pk : G₂) (x : F)
    (oa : OracleComp ((unifSpec + (M →ₒ G₁)) + (M →ₒ G₁))
      (List (G₂ × M) × G₁)) (c : (M →ₒ G₁).QueryCache) :
    (simulateQ (M →ₒ G₁).romImpl (do
      let (out, log) ← (scheme e g₂).toSignatureAlg.runWithSigningOracle pk x oa
      let verified ← (scheme e g₂).aggregateVerify out.1 out.2
      return decide (∃ msg, (pk, msg) ∈ out.1 ∧ msg ∉ log.map (fun entry => entry.1)) &&
        verified)).run' c =ᵈ
      (fun z => decide (∃ msg, (pk, msg) ∈ z.1.1.1 ∧ msg ∉ z.2.1) &&
        (decide (z.1.1.1.map Prod.snd).Nodup && decide (e z.1.1.2 g₂ = z.1.2))) <$>
          (simulateQ (realOracle x) (withFinalPairings e oa)).run ([], c) := by
  classical
  rw [realOracle_withFinalPairings,
    ← BLS.runWithSigningOracle_realOracle e g₁ g₂ (0, pk) x oa c [],
    ← runWithSigningOracle_eq]
  simp only [List.nil_append, map_bind, bind_map_left, Functor.map_map]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_pure_comp]
  apply EvalDistEq.bind_right
  intro z
  have hv := (aggregateVerify_evalDistEq e g₂ z.1.1.1 z.1.1.2 z.2).map
    (fun verified => decide (∃ msg, (pk, msg) ∈ z.1.1.1 ∧
      msg ∉ z.1.2.map (fun entry => entry.1)) && verified)
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using hv

private theorem unforgeableAdvantage_eq_realOracle {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} (g₁ : G₁) {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂)) :
    AggregateSignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁)) A =
      Pr{let x ← ($ᵗ F : ProbComp F)
         let z ← (simulateQ (realOracle x)
           (withFinalPairings e (A.main (x • g₂)))).run ([], ∅)}[
        (∃ msg, (x • g₂, msg) ∈ z.1.1.1 ∧ msg ∉ z.2.1) ∧
          (z.1.1.1.map Prod.snd).Nodup ∧ e z.1.1.2 g₂ = z.1.2] := by
  classical
  rw [AggregateSignatureAlg.unforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← prEvent_eq_evalDist_singleton]
  have hexp : AggregateSignatureAlg.unforgeableExperiment A = do
      let x ← (liftM ($ᵗ F : ProbComp F) : OracleComp (unifSpec + (M →ₒ G₁)) F)
      let (out, log) ← (scheme e g₂).toSignatureAlg.runWithSigningOracle
        (x • g₂) x (A.main (x • g₂))
      let verified ← (scheme e g₂).aggregateVerify out.1 out.2
      return decide (∃ msg, (x • g₂, msg) ∈ out.1 ∧
        msg ∉ log.map (fun entry => entry.1)) && verified := by
    simp only [AggregateSignatureAlg.unforgeableExperiment,
      show (scheme (M := M) e g₂).keygen = (do
        let x ← (liftM ($ᵗ F : ProbComp F) : OracleComp (unifSpec + (M →ₒ G₁)) F)
        return (x • g₂, x)) from rfl, bind_assoc, pure_bind]
    apply bind_congr
    intro x
    apply bind_congr
    intro z
    apply bind_congr
    intro verified
    congr 2
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_false_iff_not]
    constructor
    · rintro ⟨⟨pk, msg⟩, hm, rfl, hf⟩
      exact ⟨msg, hm, hf⟩
    · rintro ⟨msg, hm, hf⟩
      exact ⟨(x • g₂, msg), hm, rfl, hf⟩
  rw [hexp, simulateQ_bind, roSim.run'_liftM_bind]
  simp only [map_bind]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro x
  have hp := (verify_run_realOracle e g₁ g₂ (x • g₂) x (A.main (x • g₂)) ∅).prEvent_eq
    (fun b => b = true)
  simpa only [prEvent_map, Bool.and_eq_true, decide_eq_true_eq] using hp

/-- The BGLS chosen-key advantage equals the scalar-sampled indexed game, including all
final verification hashes. Generator bijectivity transports uniform scalar answers to
uniform first-source answers; the pairing equation is retained unchanged. -/
theorem unforgeableAdvantage_eq_indexed {F G₁ G₂ Gₜ M : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} (g₁ : G₁) {g₂ : G₂}
    (A : AggregateSignatureAlg.UnforgeableAdversary (scheme (M := M) e g₂))
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) :
    AggregateSignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁)) A =
      Pr{let x ← ($ᵗ F : ProbComp F)
         let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • g₁)
           (fun ρ => x • (ρ • g₁)) none)
           (withFinalPairings e (A.main (x • g₂)))).run OracleState.empty}[
        Winning e g₂ (x • g₂) z] := by
  rw [unforgeableAdvantage_eq_realOracle g₁]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro x
  have hproj := simulateQ_indexedOracle_realOracle_proj x none
    (withFinalPairings e (A.main (x • g₂))) OracleState.empty
  have hempty : valueCache (OracleState.empty : OracleState G₁ M) = ∅ := rfl
  simp only [show (OracleState.empty : OracleState G₁ M).signed = [] from rfl, hempty] at hproj
  rw [← hproj]
  simp only [prEvent_map]
  have hmap := simulateQ_indexedOracle_map_evalDistEq (· • g₁ : F → G₁)
    (fun _ => $ᵗ F) (fun _ => $ᵗ G₁) (fun _ => smul_uniformSample_evalDistEq g₁ hg₁)
    id (x • ·) none (withFinalPairings e (A.main (x • g₂))) OracleState.empty
  have hmempty : (OracleState.empty : OracleState F M).map (· • g₁) = OracleState.empty := by
    apply OracleState.ext <;> simp [OracleState.map, OracleState.empty]
    rfl
  rw [hmempty] at hmap
  have hp := hmap.prEvent_eq (Winning e g₂ (x • g₂))
  simp only [prEvent_map, Winning, OracleState.map, Function.comp_def, id_eq] at hp ⊢
  exact hp.symm

end BLS.Aggregate
