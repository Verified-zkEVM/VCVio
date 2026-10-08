/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.HitPotential
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Hit potential checks

A Boolean random oracle whose points are classed by value: the point `false` draws from the tape
of class `false`, and the point `true` from the tape of class `true`, which is left empty, so
every draw at `true` is a fresh uniform bit. A fresh draw at `true` hits the cached point equal
to its answer. The designated positions are positions of the tape of class `false`.

* On the empty state every designated position is pending, and the potential is
  `(n * ε) ^ P.card`.
* A program making at most `n` queries at `true` hits the point at position `0` of tape `false`
  with probability at most `n / 2`.
* Off the gating invariant the potential is `⊤`.
-/

public section

open OracleComp OracleSpec AnswerTape
open scoped ENNReal

namespace HitPotentialTest

/-- A Boolean random oracle. -/
abbrev pts : OracleSpec Bool := Bool →ₒ Bool

/-- Every tape class answers in `Bool`. -/
abbrev Ans : Bool → Type := fun _ => Bool

/-- The tape class of a query is the queried point, at either call site. -/
abbrev byVal : (pts + pts).Domain → Bool
  | .inl x => x
  | .inr x => x

/-- Each point answers in its class's answer type. -/
theorem byVal_range : ∀ t : (pts + pts).Domain, (pts + pts).Range t = Ans (byVal t)
  | .inl _ => rfl
  | .inr _ => rfl

/-- A fresh answer `u` at `x` hits the cached point `u`. -/
abbrev hitRel : (x : Bool) → pts.Range x → Bool → Prop := fun _ u y => y = u

/-- A uniform bit equals a given bit with probability one half. -/
theorem prEvent_hitRel_le (x y : Bool) :
    Pr{let u ← ($ᵗ pts.Range x : ProbComp _)}[hitRel x u y] ≤ 2⁻¹ := by
  refine (prEvent_mono _ _ _ fun u (h : y = u) => h.symm).trans_eq ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard, Nat.card_eq_fintype_card,
    Fintype.card_bool, Nat.cast_ofNat]

/-- The empty state leaves both designated positions pending. -/
example (L : (k : Bool) → List (Ans k)) (ε : ℝ≥0∞) :
    hitPot byVal L hitRel false {0, 1} ε 3 ((∅, L), (ClassPos.init, ∅)) = (3 * ε) ^ 2 := by
  rw [hitPot_init]
  norm_num

/-- A state whose hit set holds an uncached point is off the gating invariant, where the
potential is `⊤`. -/
example (L : (k : Bool) → List (Ans k)) (ε : ℝ≥0∞) (n : ℕ) :
    hitPot byVal L hitRel false {0} ε n ((∅, L), (ClassPos.init, {true})) = ⊤ := by
  refine hitPot_of_not_hitInv (fun h => ?_) ε n
  exact h.2 true rfl (QueryCache.empty_apply true)

/-- **The hit bound on a concrete instance.** With the tape of class `true` empty, a program
making at most `n` queries at `true` hits the point at position `0` of tape `false` with
probability at most `n / 2`. -/
example (L : (k : Bool) → List (Ans k)) (hL : L true = []) {α : Type}
    (oa : OracleComp (unifSpec + (pts + pts)) α) (n : ℕ)
    (hq : IsQueryBoundP oa (fun t => classOf byVal t = some true) n) :
    Pr{let z ← (simulateQ (classPosImplFwd Ans byVal byVal_range
        (freshHitAux (· = true) hitRel)) oa).run ((∅, L), (ClassPos.init, ∅))}[
        HitAll hitRel false {0} z.2] ≤ (n : ℝ≥0∞) * 2⁻¹ := by
  refine (prEvent_hitAll_le (· = true) hitRel byVal byVal_range L false {0} 2⁻¹
    (fun x hx => by subst hx; exact ⟨hL, hL⟩) (fun x _ y => prEvent_hitRel_le x y) _
    (fun x hx => by subst hx; exact ⟨rfl, rfl⟩) oa n hq).trans_eq ?_
  simp

end HitPotentialTest
