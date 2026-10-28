/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionExtraction
public import VCVio.CryptoFoundations.GroupModel.DLog11
import all VCVio.Schemes.BLS.AGM.Adversary
import all VCVio.Schemes.BLS.AGM.Reductions
import all VCVio.Schemes.BLS.Generic.Adversary
import all VCVio.Schemes.BLS.Generic.ReductionPrograms
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Exact generic realizations of the BLS algebraic reductions

Private zero allocations and virtual handles implement the same extraction programs as the
certified algebraic reductions, with one shared scalar random oracle.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M G₁ G₂ Gₜ : Type}

attribute [local implicit_reducible] spec PFam

/-- The good algebraic reduction of the certified translation is the named generic program. -/
theorem goodReduction_toAlgebraic [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M]
    [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (A : Adversary F M) (hA : FollowsProtocol A)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ X : G₁) (g₂ Y : G₂) :
    BLS.goodReduction (A.toAlgebraic hA e g₁ g₂) g₁ X g₂ Y =
      DLog11.Adversary.ofGeneric e (goodProgram A) g₁ X g₂ Y := by
  let g : (b : Bool) → AGM.Group G₁ G₂ b := fun | false => g₁ | true => g₂
  let x : (b : Bool) → AGM.Group G₁ G₂ b := fun | false => X | true => Y
  let root := sourceChallengeTable (T := Gₜ) g x
  let tbl := fun s => root s ++ [0]
  have hhash := realizesPoint_smul (G := AGM.Group G₁ G₂) e root 0
    (by simp [root, sourceChallengeTable]) (id : F → F)
  have hsign := realizesPoint_smul (G := AGM.Group G₁ G₂) e root 1
    (by simp [root, sourceChallengeTable]) (id : F → F)
  have hhash' : RealizesPoint (F := F) (G := AGM.Group G₁ G₂) e root
      (fun r => (genSpec F pairingSig).query (.inl (.smul .g₁ r 0))) (fun r : F => r • g₁) := by
    convert hhash using 1 <;> rfl
  have hsign' : RealizesPoint (F := F) (G := AGM.Group G₁ G₂) e root
      (fun r => (genSpec F pairingSig).query (.inl (.smul .g₁ r 1))) (fun r : F => r • X) := by
    convert hsign using 1 <;> rfl
  have hz := runGen_reductionZeros (G := AGM.Group G₁ G₂) e g x
  have hex := run'_reductionExtract (G := AGM.Group G₁ G₂) e A sourceZeroHandles 1 1
    _ _ (fun r : F => r • g₁) (fun r => r • X)
    (fun r => (r, 0)) (fun r => (0, r)) [(1, 0), (0, 1)]
    root tbl (initialRealReductionState g x) hhash' hsign' (reductionRelated_good g x)
  have halg := extractionProgram_toAlgebraic e A hA g₁ g₂ (X, Y)
    (fun r : F => r • g₁) (fun r => r • X)
    (fun r => (r, 0)) (fun r => (0, r)) [(1, 0), (0, 1)]
  have hex' := hex.trans halg.symm
  have hfinal := congrArg (fun p =>
    (simulateQ (M →ₒ F).romImpl ((fun t : F × F × F => t.1 / (t.2.2 - t.2.1)) <$> p)).run' ∅) hex'
  change _ = Prod.fst <$> runGen (pairingReal e) (fun _ => id) (goodProgram A) root
  rw [goodProgram, run_closeReduction]
  simpa only [goodReduction, reductionRun, coefficients, simulateQ_bind, simulateQ_pure,
    simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_pure, StateT.run_map,
    openImpl_reductionLift, root, hz, liftM_pure, pure_bind,
    map_pure, map_bind, bind_map_left, bind_pure_comp, Functor.map_map, tbl] using hfinal.symm

/-- The bad algebraic reduction of the certified translation is the named generic program. -/
theorem badReduction_toAlgebraic [Field F] [DecidableEq F] [SampleableType F] [DecidableEq M]
    [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (A : Adversary F M) (hA : FollowsProtocol A)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ X : G₁) (g₂ Y : G₂) :
    BLS.badReduction (A.toAlgebraic hA e g₁ g₂) g₁ X g₂ Y =
      DLog11.Adversary.ofGeneric e (badProgram A) g₁ X g₂ Y := by
  let g : (b : Bool) → AGM.Group G₁ G₂ b := fun | false => g₁ | true => g₂
  let x : (b : Bool) → AGM.Group G₁ G₂ b := fun | false => X | true => Y
  let root := sourceChallengeTable (T := Gₜ) g x
  let tbl : F → Tbl (PFam G₁ G₂ Gₜ) := fun κ =>
    fun | .g₁ => [g₁, X, 0, κ • g₁] | .g₂ => [g₂, Y, 0, κ • g₂] | .gₜ => [0]
  have hhash := realizesPoint_maskedPoint (G := AGM.Group G₁ G₂) e root
    (by simp [root, sourceChallengeTable])
  have hhash' : RealizesPoint (F := F) (G := AGM.Group G₁ G₂) e root maskedPoint
      (fun r : F × F => r.1 • X + r.2 • g₁) := by
    convert hhash using 1
    rfl
  have hz := runGen_reductionZeros (G := AGM.Group G₁ G₂) e g x
  change _ = Prod.fst <$> runGen (pairingReal e) (fun _ => id) (badProgram A) root
  rw [badProgram, run_closeReduction]
  simp only [badReduction, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure,
    openImpl_liftM,
    OracleSpec.simulateQ_romImpl_liftM_run, map_bind, bind_map_left,
    openImpl_reductionLift, root, hz, liftM_pure, pure_bind, map_pure]
  apply bind_congr
  intro κ
  have hex := run'_reductionExtract (G := AGM.Group G₁ G₂) e A sourceZeroHandles 3 3
    _ _ (fun r : F × F => r.1 • X + r.2 • g₁) (fun r => κ • (r.1 • X + r.2 • g₁))
    (fun _ => (0, 0)) id [(0, 0), (0, 1)]
    root (tbl κ) (initialRealReductionState g (fun b => κ • g b))
    hhash' (hhash'.smul (fun _ => κ)) (reductionRelated_bad g x κ)
  have halg := extractionProgram_toAlgebraic e A hA g₁ g₂ (κ • g₁, κ • g₂)
    (fun r : F × F => r.1 • X + r.2 • g₁) (fun r => κ • (r.1 • X + r.2 • g₁))
    (fun _ => (0, 0)) id [(0, 0), (0, 1)]
  have hpk : (fun b => κ • g b) =
      (fun b : Bool => (match b with | false => κ • g₁ | true => κ • g₂) :
        (b : Bool) → AGM.Group G₁ G₂ b) := by
    funext b
    cases b <;> rfl
  rw [hpk] at hex
  have hex' := hex.trans halg.symm
  have hfinal := congrArg (fun p =>
    (simulateQ (M →ₒ F × F).romImpl
      ((fun t : F × F × (F × F) => (t.2.1 - t.2.2.2) / (t.2.2.1 - t.1)) <$> p)).run' ∅) hex'
  simp only [reductionRun, coefficients, simulateQ_pure,
    simulateQ_map, StateT.run'_eq, StateT.run_pure, StateT.run_map,
    openImpl_smul, pure_bind, bind_pure_comp,
    Functor.map_map, tbl, sourceChallengeTable, append, lookup, g, x] at hfinal ⊢
  convert hfinal.symm using 1
  congr 4
  funext s
  cases s <;> simp <;> rfl

end BLS.Generic
