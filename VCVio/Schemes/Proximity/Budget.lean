/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Distribution
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-! # Query budgets for Proximity's fresh-collision term

The fresh-collision probability explicitly records at most `qh` direct hash replies and
`qs` signing replies. Under the adversary's pathwise query bounds this is exactly the source
collision probability. It is a linear-relation event, not a collision of random-oracle
answers, so a birthday estimate cannot replace it.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional
open scoped ENNReal

namespace Proximity.Weighted

/-- A reply predicate charges public hashing and signing, and never private randomness. -/
@[expose] def replyPredicate {I M : Type} (p : I ⊕ M → Bool) :
    (ℕ ⊕ I) ⊕ M → Prop
  | .inl (.inl _) => False
  | .inl (.inr i) => p (.inl i) = true
  | .inr m => p (.inr m) = true

/-- A pathwise public query budget bounds the corresponding chronological reply count. -/
theorem fixedRun_count_le {I M G α : Type} (hash : I → G) (sign : M → G)
    (oa : OracleComp (interfaceSpec I M G) α) (p : I ⊕ M → Bool) (n : ℕ)
    [DecidablePred (replyPredicate p)]
    (h : IsQueryBoundP oa (replyPredicate p) n)
    (z : α × Transcript I M) (hz : z ∈ support (weightedFixedRun hash sign oa)) :
    z.2.countP p ≤ n := by
  classical
  have hstep (q : (interfaceSpec I M G).Domain) (tr : Transcript I M)
      (w : (interfaceSpec I M G).Range q × Transcript I M)
      (hw : w ∈ support ((weightedFixedOracle hash sign q).run tr)) :
      (w.2.countP p : ℕ∞) ≤ tr.countP p + if replyPredicate p q then 1 else 0 := by
    rcases q with ((n | i) | m)
    · obtain ⟨r, _, rfl⟩ := by
        simpa only [weightedFixedOracle, StateT.run, support_map, Set.mem_image] using hw
      simp [replyPredicate]
    · have he : w = (hash i, tr ++ [.inl i]) := by
        simpa only [weightedFixedOracle, StateT.run, support_pure, Set.mem_singleton_iff] using hw
      subst w
      by_cases hp : p (.inl i) <;> simp [replyPredicate, hp]
    · have he : w = (sign m, tr ++ [.inr m]) := by
        simpa only [weightedFixedOracle, StateT.run, support_pure, Set.mem_singleton_iff] using hw
      subst w
      by_cases hp : p (.inr m) <;> simp [replyPredicate, hp]
  have hb := h.resource_le_add_of_mem_support_run_simulateQ
    (fun tr => (tr.countP p : ℕ∞)) hstep hz
  simpa using hb

end Proximity.Weighted

namespace Proximity

/-- The actual fresh linear-collision probability, with explicit direct-hash and signing
reply budgets. Internal base lookups of signing are excluded from these public counts. -/
noncomputable def freshCollisionProbability {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (qh qs : ℕ) : ℝ≥0∞ :=
  Pr{let κ ← ($ᵗ F : ProbComp F)
     let z ← ((simulateQ (Index Slot dimension →ₒ G₁).romImpl
       ((simulateQ (Weighted.oracle terms id (fun r : G₁ => κ • r))
         (A.rawMain (κ • g₂))).run [])).run' ∅)}[
    AGM.FreshCollision z.1 z.2 ∧ z.2.countP Sum.isLeft ≤ qh ∧ z.2.countP Sum.isRight ≤ qs]

/-- Certified public query budgets make the budgeted collision term equal the original event. -/
theorem freshCollisionProbability_eq {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [SampleableType F] [DecidableEq Slot]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (qh qs : ℕ)
    (hqueries : A.QueryBound qh qs) (hg₁ : Function.Bijective (· • g₁ : F → G₁)) :
    freshCollisionProbability A qh qs = Pr{let b ← freshCollisionExperiment A}[b = true] := by
  classical
  obtain ⟨S, hS⟩ := AGM.exists_base_cover A
  rw [AGM.freshCollisionExperiment_eq_table A hg₁ S hS, freshCollisionProbability]
  let : MeasurableSpace F := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro κ
  rw [(Weighted.oracle_scalar_table terms (fun out => out.value.data) g₁ hg₁ κ
    (A.rawMain (κ • g₂)) S (hS κ)).prEvent_eq]
  let : MeasurableSpace (S → F) := ⊤
  simp only [prEvent_norm]
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_congr
  intro ρ
  apply prEvent_congr_of_support
  intro z hz
  have hh : IsQueryBoundP (A.rawMain (κ • g₂)) (Weighted.replyPredicate Sum.isLeft) qh := by
    convert (hqueries (κ • g₂)).1 using 1
    funext q
    rcases q with ((n | i) | m) <;> simp [Weighted.replyPredicate, AGM.isHash]
  have hs : IsQueryBoundP (A.rawMain (κ • g₂)) (Weighted.replyPredicate Sum.isRight) qs := by
    convert (hqueries (κ • g₂)).2 using 1
    funext q
    rcases q with ((n | i) | m) <;> simp [Weighted.replyPredicate, AGM.isSign]
  have hb₁ := Weighted.fixedRun_count_le _ _ _ Sum.isLeft qh hh z hz
  have hb₂ := Weighted.fixedRun_count_le _ _ _ Sum.isRight qs hs z hz
  simp only [hb₁, hb₂, and_true]

end Proximity
