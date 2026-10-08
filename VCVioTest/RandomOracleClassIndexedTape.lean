/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position

/-!
# Forwarded class-indexed tape checks

A program draws a private coin and then queries the point `true` of a Boolean random oracle
through the left copy of the duplicated interface. The tape class is the call site: the left
copy draws from tape `false`, the right copy from tape `true`. The tape of class `false` holds
one answer and the tape of class `true` none.

The checks compose the forwarded identification, the per-class budgets, the restricted position
lemma and the bind-form transport: the lazy run caches `true ↦ true` with probability at most
that of the first entry of tape `false` being `true`. That needs both budgets, since the class
pinned to the cached point could a priori be either call site, and the empty tape `true` is
ruled out only by its zero budget.
-/

public section

open OracleComp OracleSpec AnswerTape
open scoped ENNReal

namespace ClassIndexedTapeTest

/-- A Boolean random oracle. -/
abbrev pts : OracleSpec Bool := Bool →ₒ Bool

/-- Every tape class answers in `Bool`. -/
abbrev Ans : Bool → Type := fun _ => Bool

/-- The tape class of a query is its call site: `false` for the left copy, `true` for the
right. -/
abbrev site : (pts + pts).Domain → Bool
  | .inl _ => false
  | .inr _ => true

/-- Each call site answers in its class's answer type. -/
theorem site_range : ∀ t : (pts + pts).Domain, (pts + pts).Range t = Ans (site t)
  | .inl _ => rfl
  | .inr _ => rfl

/-- The tape lengths: one answer for the left call site, none for the right. -/
abbrev lens : Bool → ℕ
  | false => 1
  | true => 0

/-- Draw a private coin, then query the point `true` through the left copy. -/
def prog : OracleComp (unifSpec + (pts + pts)) Bool := do
  let _ ← liftM ((unifSpec + (pts + pts)).query (Sum.inl 1))
  liftM ((unifSpec + (pts + pts)).query (Sum.inr (Sum.inl true)))

/-- The private query is invisible to the tapes: the forwarded identification applies. -/
example :
    letI : MeasurableSpace (Bool × pts.QueryCache) := ⊤
    𝒟[(simulateQ (dupRandomOracleFwd pts) prog).run ∅] =
      𝒟[(do let L ← tapeFamily Ans lens
            let z ← (simulateQ (tapeImplFwd Ans site site_range) prog).run (∅, L)
            return (z.1, z.2.1))] :=
  evalDist_run_dupRandomOracleFwd_eq_tapeFamily site site_range prog ∅ lens

/-- The program makes one query of class `false`. -/
theorem prog_bound_false : IsQueryBoundP prog (fun t => classOf site t = some false) 1 := by
  rw [prog, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [classOf]),
    fun _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => by simp [classOf]⟩

/-- The program makes no query of class `true`. -/
theorem prog_bound_true : IsQueryBoundP prog (fun t => classOf site t = some true) 0 := by
  rw [prog, isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [classOf]),
    fun _ => (isQueryBoundP_query_iff _ _ _).2 (by simp [classOf])⟩

/-- The lazy run caches `true ↦ true` no more often than the tape of class `false` starts with
`true`. -/
theorem prEvent_cache_le :
    Pr{let z ← (simulateQ (dupRandomOracleFwd pts) prog).run ∅}[z.2 true = some true] ≤
      Pr{let L ← tapeFamily Ans lens}[(L false)[0]? = some true] := by
  have key := prEvent_run_dupRandomOracleFwd_le_sum site site_range (Q := Unit)
    (fun _ _ _ _ q => q) () prog lens (fun z => z.2 true = some true) {()}
    (fun _ L => (L false)[0]? = some true) (fun _ _ => True) (fun _ => 1)
    (fun L hL z hz hP => by
      have hlen := length_of_mem_support_tapeFamily lens hL
      have hb : ∀ j ∈ (Set.univ : Set Bool), z.2.2.1.cnt j ≤ (L j).length := by
        rintro (_ | _) -
        · simpa [hlen] using cnt_le_of_isQueryBoundP site site_range _ () L prog false
            prog_bound_false hz
        · simpa [hlen] using cnt_le_of_isQueryBoundP site site_range _ () L prog true
            prog_bound_true hz
      obtain ⟨j, -, -, hj⟩ :=
        (exists_pos_of_mem_support_run_instrImpl site site_range _ () L prog hz Set.univ hb).1
          true true hP
      obtain ⟨n, -, hn, h, hval⟩ := hj trivial
      rw [hlen] at hn
      cases j with
      | false =>
          obtain rfl : n = 0 := by simpa using hn
          exact ⟨(), Finset.mem_singleton_self _, by simpa using hval, trivial⟩
      | true => exact absurd hn (Nat.not_lt_zero n))
    (fun _ _ _ _ => prEvent_le_one _ _)
  simpa using key

end ClassIndexedTapeTest
