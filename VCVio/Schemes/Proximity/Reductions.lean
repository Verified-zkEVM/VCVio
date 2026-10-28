/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Adversary
public import VCVio.CryptoFoundations.HardnessAssumptions.DLog11
public import VCVio.Schemes.Proximity.Weighted

/-! # Proximity's two discrete-logarithm reductions

The good reduction programs bases as known multiples of the first generator and signs using
the first challenge point. The bad reduction samples its own signing secret and programs each
base as an independently masked affine function of the challenge. Both use the existing lazy
random-oracle cache, with no enumeration of slots. Explanations retain chronological positions,
including repeated hash and signing queries.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Proximity.AGM

/-- The coefficient vector explaining the first signature point, with zero for a missing output. -/
@[expose] def coefficients {F Slot G₁ G₂ : Type} {dimension : ℕ}
    (out : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂)) : List F :=
  if (out.value.groups false).isEmpty then [] else (out.coefficients false).headD []

/-- Run the algebraic program with explicitly supplied source generators and public key. -/
@[expose] def program {F Slot G₁ G₂ : Type} {dimension : ℕ} [Zero F]
    [AddMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    (A : Adversary F (Group G₁ G₂) Unit (Query F Slot dimension) Reply
      (Proximity.Message F Slot dimension)) (g₁ : G₁) (g₂ pk : G₂) :
    OracleComp (rawSpec F Slot G₁ dimension)
      (Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂)) :=
  simulateQ (fun q => oracle q.value) (A.main (initialInput g₁ g₂ pk))

/-- The scalar-table program for the good reduction, before the shared cache is interpreted. -/
@[expose] def goodProgram {F Slot G₁ G₂ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (A : Adversary F (Group G₁ G₂) Unit (Query F Slot dimension) Reply
      (Proximity.Message F Slot dimension)) (g X : G₁) (h Y : G₂) :
    OracleComp (unifSpec + (Index Slot dimension →ₒ F)) F := do
  let (out, basis, target) ← weightedExtractionProgram terms (fun out => out.value.data)
    (fun ρ : F => ρ • g) (fun ρ => ρ • X)
    (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0)]
    (program A g h Y)
  let repr := evaluate (coefficients out) basis
  return repr.1 / (target - repr.2)

/-- The affine-table program for the bad reduction, using an independently chosen signing key. -/
@[expose] def badProgram {F Slot G₁ G₂ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (A : Adversary F (Group G₁ G₂) Unit (Query F Slot dimension) Reply
      (Proximity.Message F Slot dimension)) (g X : G₁) (h : G₂) (κ : F) :
    OracleComp (unifSpec + (Index Slot dimension →ₒ (F × F))) F := do
  let point := fun r : F × F => r.1 • X + r.2 • g
  let (out, basis, target) ← weightedExtractionProgram terms (fun out => out.value.data)
    point (fun r => κ • point r) (fun _ => ((0 : F), (0 : F))) id [(0, 0)]
    (program A g h (κ • h))
  let repr := evaluate (coefficients out) basis
  return (repr.2 - target.2) / (target.1 - repr.1)

/-- At a fixed scalar table the good program divides the constant representation by its gap. -/
theorem goodProgram_table {F Slot G₁ G₂ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (A : Adversary F (Group G₁ G₂) Unit (Query F Slot dimension) Reply
      (Proximity.Message F Slot dimension)) (g X : G₁) (h Y : G₂)
    (ρ : Index Slot dimension → F) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn ρ)) (goodProgram A g X h Y) =
      (fun z =>
        let repr := evaluate (coefficients z.1) ([(1, 0)] ++ z.2.map
          (Sum.elim (fun i => (ρ i, (0 : F)))
            (fun m => ((0 : F), Weighted.value ρ (terms m)))))
        repr.1 / (Weighted.value ρ (terms z.1.value.data) - repr.2)) <$>
      weightedFixedRun (fun i => ρ i • g) (fun m => Weighted.value ρ (terms m) • X)
        (program A g h Y) := by
  simp [goodProgram, Weighted.extractionProgram_table, Function.comp_def]

/-- At a fixed affine table the bad program extracts from the signing coefficients' gap. -/
theorem badProgram_table {F Slot G₁ G₂ : Type} {dimension : ℕ} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (A : Adversary F (Group G₁ G₂) Unit (Query F Slot dimension) Reply
      (Proximity.Message F Slot dimension)) (g X : G₁) (h : G₂) (κ : F)
    (ab : Index Slot dimension → F × F) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn ab)) (badProgram A g X h κ) =
      (fun z =>
        let repr := evaluate (coefficients z.1) ([(0, 0)] ++ z.2.map
          (Sum.elim (fun _ => ((0 : F), (0 : F)))
            (fun m => Weighted.value ab (terms m))))
        let target := Weighted.value ab (terms z.1.value.data)
        (repr.2 - target.2) / (target.1 - repr.1)) <$>
      weightedFixedRun (fun i => (ab i).1 • X + (ab i).2 • g)
        (fun m => κ • ((Weighted.value ab (terms m)).1 • X +
          (Weighted.value ab (terms m)).2 • g)) (program A g h (κ • h)) := by
  simp [badProgram, Weighted.extractionProgram_table, Function.comp_def]

end Proximity.AGM

namespace Proximity

/-- Program uniform scalar bases and solve the nonzero verification-gap branch using the
first challenge point for signing. The second challenge point is the public key. -/
@[expose] def goodReduction {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h Y =>
    (simulateQ (Index Slot dimension →ₒ F).romImpl
      (AGM.goodProgram A.toAdversary g X h Y)).run' ∅

/-- Choose a signing key and independently mask every base using the first challenge point;
solve the zero-gap branch from the affine signing coefficients. -/
@[expose] def badReduction {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h _ => do
    let κ ← $ᵗ F
    (simulateQ (Index Slot dimension →ₒ (F × F)).romImpl
      (AGM.badProgram A.toAdversary g X h κ)).run' ∅

end Proximity
