/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Game
public import VCVio.Schemes.Proximity.Tables
import all VCVio.Schemes.Proximity.Collision

/-! # Joint finite-table laws for Proximity

The real execution and its fresh-collision observation use the same chronological table
semantics. Scalar programming is justified by a bijection onto the first source group.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.Weighted

/-- Linear interpretations commute with the weighted list sum. -/
theorem value_map {F I R V : Type} [Semiring F]
    [AddCommMonoid R] [Module F R] [AddCommMonoid V] [Module F V]
    (f : R →ₗ[F] V) (table : I → R) (ts : List (I × F)) :
    value (fun i => f (table i)) ts = f (value table ts) := by
  simp only [value, map_list_sum, List.map_map, Function.comp_def, map_smul]

/-- Extending a scalar table and then interpreting it as a group table commutes with fallback. -/
theorem extendTable_smul {F I G : Type} [Semiring F] [AddCommMonoid G]
    [Module F G] [DecidableEq I] (S : Finset I) (ρ : S → F) (g : G) :
    extendTable S 0 (fun i => ρ i • g) = fun i => extendTable S 0 ρ i • g := by
  funext i
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> simp

/-- A covered chronological execution has the uniform scalar-table law. -/
theorem oracle_scalar_table {F I M G α : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq I]
    (terms : M → List (I × F)) (target : α → M) (g : G)
    (hg : Function.Bijective (· • g : F → G)) (κ : F)
    (oa : OracleComp (interfaceSpec I M G) α) (S : Finset I)
    (hS : Covered terms S target oa) :
    (simulateQ (I →ₒ G).romImpl
      ((simulateQ (oracle terms id (fun r : G => κ • r)) oa).run [])).run' ∅ =ᵈ (do
      let ρ ← $ᵗ (S → F)
      fixedRun (fun i => extendTable S 0 ρ i • g)
        (fun m => value (extendTable S 0 ρ) (terms m) • (κ • g)) oa) := by
  have h := simulateQ_romImpl_evalDistEq_finite_table S _
    (oracle_covered terms S target id (fun r : G => κ • r) oa hS) (0 : G)
  simp only [oracle_table] at h
  refine h.trans ?_
  have hu := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (Function.Bijective.piMap (fun _ : S => hg))
  have ht := hu.bind_left (fun table : S → G =>
    fixedRun (extendTable S 0 table)
      (fun m => κ • value (extendTable S 0 table) (terms m)) oa)
  simp only [bind_map_left] at ht
  refine ht.symm.trans ?_
  apply _root_.EvalDistEq.bind_right
  intro ρ
  have he : GroupModel.LinearFunctional.extendTable S (0 : G)
      (Pi.map (fun _ : S => (· • g : F → G)) ρ) =
      fun i => GroupModel.LinearFunctional.extendTable S 0 ρ i • g := by
    exact extendTable_smul S ρ g
  rw [he]
  have hv (ts : List (I × F)) : value (fun i => extendTable S 0 ρ i • g) ts =
      value (extendTable S 0 ρ) ts • g :=
    value_map ((LinearMap.id : F →ₗ[F] F).smulRight g) _ _
  simp only [hv, smul_smul, mul_comm]
  exact _root_.EvalDistEq.refl _

/-- The scalar-table law holds jointly with the final verification target. -/
theorem targetProgram_scalar_table {F I M G α : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq I]
    (terms : M → List (I × F)) (target : α → M) (g : G)
    (hg : Function.Bijective (· • g : F → G)) (κ : F)
    (oa : OracleComp (interfaceSpec I M G) α) (S : Finset I)
    (hS : Covered terms S target oa) :
    (simulateQ (I →ₒ G).romImpl
      (targetProgram terms target id (fun r : G => κ • r) oa)).run' ∅ =ᵈ (do
      let ρ ← $ᵗ (S → F)
      let z ← fixedRun (fun i => extendTable S 0 ρ i • g)
        (fun m => value (extendTable S 0 ρ) (terms m) • (κ • g)) oa
      return (z.1, z.2, value (extendTable S 0 ρ) (terms (target z.1)) • g)) := by
  have h := simulateQ_romImpl_evalDistEq_finite_table S _
    (targetProgram_covered terms S target id (fun r : G => κ • r) oa hS) (0 : G)
  simp only [targetProgram_table] at h
  refine h.trans ?_
  have hu := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (Function.Bijective.piMap (fun _ : S => hg))
  have ht := hu.bind_left (fun table : S → G => do
    let z ← fixedRun (extendTable S 0 table)
      (fun m => κ • value (extendTable S 0 table) (terms m)) oa
    return (z.1, z.2, value (extendTable S 0 table) (terms (target z.1))))
  simp only [bind_map_left, bind_pure_comp] at ht
  refine ht.symm.trans ?_
  apply _root_.EvalDistEq.bind_right
  intro ρ
  have he : GroupModel.LinearFunctional.extendTable S (0 : G)
      (Pi.map (fun _ : S => (· • g : F → G)) ρ) =
      fun i => GroupModel.LinearFunctional.extendTable S 0 ρ i • g := by
    exact extendTable_smul S ρ g
  rw [he]
  have hv (ts : List (I × F)) : value (fun i => extendTable S 0 ρ i • g) ts =
      value (extendTable S 0 ρ) ts • g :=
    value_map ((LinearMap.id : F →ₗ[F] F).smulRight g) _ _
  simp only [hv, smul_smul, mul_comm, bind_pure_comp]
  exact _root_.EvalDistEq.refl _

end Proximity.Weighted

namespace Proximity.AGM

/-- The real EUF-CMA advantage is the success event of the joint scalar-table execution. -/
theorem unforgeableAdvantage_eq_table {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁))
    (S : Finset (Index Slot dimension))
    (hS : ∀ κ : F, Weighted.Covered terms S (fun out => out.value.data)
      (A.rawMain (κ • g₂))) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (Index Slot dimension →ₒ G₁))
      A.toUnforgeableAdversary =
    Pr{let κ ← ($ᵗ F : ProbComp F); let ρ ← $ᵗ (S → F)
       let z ← Weighted.fixedRun (fun i => extendTable S 0 ρ i • g₁)
         (fun m => Weighted.value (extendTable S 0 ρ) (terms m) • (κ • g₁))
         (A.rawMain (κ • g₂))}[
      z.1.value.data ∉ signedMessages z.2 ∧
      e (forgery z.1).2 g₂ =
        e (Weighted.value (extendTable S 0 ρ) (terms z.1.value.data) • g₁) (κ • g₂)] := by
  classical
  rw [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.rom_evalDist]
  have hx : SignatureAlg.unforgeableExperiment A.toUnforgeableAdversary = (do
      let κ ← (liftM ($ᵗ F) : OracleComp (unifSpec + (Index Slot dimension →ₒ G₁)) F)
      (fun z => decide (z.1.value.data ∉ signedMessages z.2.1) &&
        decide (e (forgery z.1).2 g₂ = e z.2.2 (κ • g₂))) <$>
        Weighted.targetProgram terms (fun out => out.value.data) id (fun r : G₁ => κ • r)
          (A.rawMain (κ • g₂))) := by
    rw [unforgeableExperiment_eq]
    simp only [Weighted.targetProgram, map_bind, hash, bind_pure_comp, Functor.map_map]
    congr!
  rw [hx]
  rw [← prEvent_eq_evalDist_singleton]
  simp only [simulateQ_bind, romImpl]
  rw [roSim.run'_liftM_bind]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_norm,
    Bool.and_eq_true, decide_eq_true_eq]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro κ
  simpa only [StateT.run'_eq, prEvent_norm] using
    (Weighted.targetProgram_scalar_table terms (fun out => out.value.data) g₁ hg₁ κ
      (A.rawMain (κ • g₂)) S (hS κ)).prEvent_eq
      (fun z => z.1.value.data ∉ signedMessages z.2.1 ∧
        e (forgery z.1).2 g₂ = e z.2.2 (κ • g₂))

/-- The source fresh-collision event is observed in the same finite scalar-table execution. -/
theorem collisionGame_eq_table {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁))
    (S : Finset (Index Slot dimension))
    (hS : ∀ κ : F, Weighted.Covered terms S (fun out => out.value.data)
      (A.rawMain (κ • g₂))) :
    Pr{let b ← collisionGame A}[b = true] =
    Pr{let κ ← ($ᵗ F : ProbComp F); let ρ ← $ᵗ (S → F)
       let z ← Weighted.fixedRun (fun i => extendTable S 0 ρ i • g₁)
         (fun m => Weighted.value (extendTable S 0 ρ) (terms m) • (κ • g₁))
         (A.rawMain (κ • g₂))}[FreshCollision z.1 z.2] := by
  classical
  simp only [collisionGame, bind_pure_comp, simulateQ_bind, romImpl]
  rw [roSim.run'_liftM_bind]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_norm, decide_eq_true_eq]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro κ
  simpa only [StateT.run'_eq, prEvent_norm] using
    (Weighted.oracle_scalar_table terms (fun out => out.value.data) g₁ hg₁ κ
    (A.rawMain (κ • g₂)) S (hS κ)).prEvent_eq (fun z => FreshCollision z.1 z.2)

end Proximity.AGM
