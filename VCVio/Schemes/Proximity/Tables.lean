/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Reductions
public import VCVio.Schemes.Proximity.Cover

/-! # Finite-table laws for Proximity's lazy reductions

A finite cover of the adaptive public program covers signing and final-target base
lookups. The named reductions retain their executable lazy caches over arbitrary slots.
Only their probability laws use a finite table. The same cover can be selected for every
secret key because both the scalar field and the oracle-answer types are finite.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.AGM

/-- All generated public keys share a finite cover of every base used on every reply path,
including signing and final-target bases, even when the slot type is infinite. -/
theorem exists_base_cover {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [Finite F] [AddCommGroup G₁] [Module F G₁] [Finite G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) :
    ∃ S : Finset (Index Slot dimension), ∀ κ : F,
      WeightedInterfaceCovered S terms (fun out => out.value.data) (A.rawMain (κ • g₂)) :=
  exists_weightedInterfaceCovered terms (fun out => out.value.data)
    (fun κ : F => A.rawMain (κ • g₂))

/-- The actual lazy good reduction has the finite scalar-table law on any public cover. -/
theorem goodReduction_table {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (κ : F)
    (S : Finset (Index Slot dimension))
    (hS : WeightedInterfaceCovered S terms (fun out => out.value.data) (A.rawMain (κ • g₂))) :
    goodReduction A g₁ (κ • g₁) g₂ (κ • g₂) =ᵈ (do
      let table ← $ᵗ (S → F)
      let ρ := extendTable S 0 table
      let z ← weightedFixedRun (fun i => ρ i • g₁)
        (fun m => Weighted.value ρ (terms m) • (κ • g₁)) (A.rawMain (κ • g₂))
      let repr := evaluate (coefficients z.1) ([(1, 0)] ++ z.2.map
        (Sum.elim (fun i => (ρ i, (0 : F)))
          (fun m => ((0 : F), Weighted.value ρ (terms m)))))
      return repr.1 / (Weighted.value ρ (terms z.1.value.data) - repr.2)) := by
  have h := (Weighted.extractionProgram_evalDistEq_finite_table terms S
    (fun out => out.value.data) (fun ρ : F => ρ • g₁) (fun ρ => ρ • (κ • g₁))
    (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0)]
    (A.rawMain (κ • g₂)) hS 0).map (fun z =>
      (evaluate (coefficients z.1) z.2.1).1 /
        (z.2.2 - (evaluate (coefficients z.1) z.2.1).2))
  simpa only [goodReduction, goodProgram, program, AlgebraicAdversary.rawMain,
    bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    map_bind, map_pure, Function.comp_def] using h

/-- At a chosen signing key the lazy affine program has one finite pair-table law.
The challenge scalar and signing secret are independent parameters of this identity. -/
theorem badProgram_rom_table {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (α κ : F)
    (S : Finset (Index Slot dimension))
    (hS : WeightedInterfaceCovered S terms (fun out => out.value.data) (A.rawMain (κ • g₂))) :
    (simulateQ (Index Slot dimension →ₒ (F × F)).romImpl
      (badProgram A.toAdversary g₁ (α • g₁) g₂ κ)).run' ∅ =ᵈ (do
      let table ← $ᵗ (S → F × F)
      let ab := extendTable S (0, 0) table
      let point := fun r : F × F => r.1 • (α • g₁) + r.2 • g₁
      let z ← weightedFixedRun (point ∘ ab)
        (fun m => κ • point (Weighted.value ab (terms m))) (A.rawMain (κ • g₂))
      let repr := evaluate (coefficients z.1) ([(0, 0)] ++ z.2.map
        (Sum.elim (fun _ => ((0 : F), (0 : F))) (fun m => Weighted.value ab (terms m))))
      let target := Weighted.value ab (terms z.1.value.data)
      return (repr.2 - target.2) / (target.1 - repr.1)) := by
  have h := (Weighted.extractionProgram_evalDistEq_finite_table terms S
    (fun out => out.value.data) (fun r : F × F => r.1 • (α • g₁) + r.2 • g₁)
    (fun r : F × F => κ • (r.1 • (α • g₁) + r.2 • g₁))
    (fun _ => ((0 : F), (0 : F))) id [(0, 0)] (A.rawMain (κ • g₂)) hS (0, 0)).map
      (fun z => ((evaluate (coefficients z.1) z.2.1).2 - z.2.2.2) /
        (z.2.2.1 - (evaluate (coefficients z.1) z.2.1).1))
  simpa only [badProgram, program, AlgebraicAdversary.rawMain,
    bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    map_bind, map_pure, Function.comp_def, id_eq] using h

end Proximity.AGM
