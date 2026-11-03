/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import NativeCausalState
import all NativeCausalState
import VCVio.OracleComp.EvalDist.Sum

/-! # Future-cell causality for an existing native role program -/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security.Coverage.NativeCausality

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (tracked : TapeClass)

/-- An overwrite changes no other class's current tape. -/
theorem overwriteTapes_apply_ne (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell : Nat) (value : tapeClassRange core tracked) (j : TapeClass) (hj : j ≠ tracked) :
    overwriteTapes core tracked L cell value j = L j := by
  simp [overwriteTapes, Function.update_of_ne hj]

/-- An overwrite of an empty tracked tape is a no-op. -/
theorem overwrite_nil (s : RoleState core) (cell : Nat) (value : tapeClassRange core tracked)
    (h : s.1.2 tracked = []) : overwrite core tracked s cell value = s := by
  have tapes : overwriteTapes core tracked s.1.2 cell value = s.1.2 := by
    unfold overwriteTapes
    rw [h, List.set_nil, ←h, Function.update_eq_self]
  simp only [overwrite, tapes, Prod.eta]

/-- Consuming another class's head commutes with overwriting the tracked tape. -/
theorem overwriteTapes_update_ne (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell : Nat) (value : tapeClassRange core tracked) (j : TapeClass) (hj : j ≠ tracked)
    (tail : List (tapeClassRange core j)) :
    Function.update (overwriteTapes core tracked L cell value) j tail =
      overwriteTapes core tracked (Function.update L j tail) cell value := by
  unfold overwriteTapes
  rw [Function.update_of_ne (Ne.symm hj)]
  exact (Function.update_comm hj tail ((L tracked).set cell value) L).symm

/-- Consuming the forger head leaves precisely the overwritten remainder. -/
theorem overwriteTapes_update_self (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell cell' : Nat) (value : tapeClassRange core tracked)
    (tail : List (tapeClassRange core tracked)) :
    Function.update (overwriteTapes core tracked L cell value) tracked (tail.set cell' value) =
      overwriteTapes core tracked (Function.update L tracked tail) cell' value := by
  simp [overwriteTapes]

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- One existing tape step preserves future-cell causality of its native continuations. -/
theorem tapeStep_causal {α : Type} (j : TapeClass) (point : (jointSpec core).Domain)
    (hR : (jointSpec core).Range point = tapeClassRange core j)
    (next : (jointSpec core).Range point → OracleComp (roleSpec core) α)
    (ih : ∀ answer (s : RoleState core) (index cell : Nat) (value : tapeClassRange core tracked),
      index ≤ cell →
      Pr{let z ← (simulateQ (roleRunImpl core) (next answer)).run
          (overwrite core tracked s cell value)}[s.2.1.cnt tracked + index <
            z.2.2.1.cnt tracked] =
      Pr{let z ← (simulateQ (roleRunImpl core) (next answer)).run s}[s.2.1.cnt tracked +
        index < z.2.2.1.cnt tracked])
    (s : RoleState core) (index cell : Nat) (value : tapeClassRange core tracked)
    (horder : index ≤ cell) :
    Pr{let z ← (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) j point hR).run
        (overwrite core tracked s cell value).1
      (simulateQ (roleRunImpl core) (next w.1)).run
        (post core j point (overwrite core tracked s cell value) w.1 w.2))}[
      s.2.1.cnt tracked + index < z.2.2.1.cnt tracked] =
    Pr{let z ← (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) j point hR).run s.1
      (simulateQ (roleRunImpl core) (next w.1)).run (post core j point s w.1 w.2))}[
      s.2.1.cnt tracked + index < z.2.2.1.cnt tracked] := by
  classical
  dsimp only [overwrite]
  by_cases jf : j = tracked
  · subst j
    cases index with
    | zero =>
      trans (1 : ℝ≥0∞)
      · apply prEvent_eq_one_of_forall_mem_support
        intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        have grows := cnt_run_mono core tracked (next w.1)
          (post core tracked point (overwrite core tracked s cell value) w.1 w.2) z hz
        rw [post_cnt] at grows
        simp only [overwrite, ↓reduceIte] at grows
        omega
      · symm
        apply prEvent_eq_one_of_forall_mem_support
        intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        have grows := cnt_run_mono core tracked (next w.1)
          (post core tracked point s w.1 w.2) z hz
        rw [post_cnt] at grows
        simp only [↓reduceIte] at grows
        omega
    | succ index =>
      cases cell with
      | zero => omega
      | succ cell =>
        cases cached : s.1.1 point with
        | some answer =>
          rw [AnswerTape.tapeStep_run_some cached, AnswerTape.tapeStep_run_some cached]
          simp only [pure_bind]
          change Pr{let z ← ((simulateQ (roleRunImpl core) (next answer)).run
            (post core tracked point (overwrite core tracked s (cell+1) value) answer
              (s.1.1, overwriteTapes core tracked s.1.2 (cell+1) value)))}[_] = _
          rw [post_overwrite]
          simpa only [post_cnt, ↓reduceIte, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using ih answer (post core tracked point s answer s.1) index (cell+1)
              value (by omega)
        | none =>
          cases tape : s.1.2 tracked with
          | nil =>
            change Pr{let z ← (do
              let w ← (AnswerTape.tapeStep (tapeClassRange core) tracked point hR).run
                (overwrite core tracked s (cell+1) value).1
              (simulateQ (roleRunImpl core) (next w.1)).run
                (post core tracked point
                  (overwrite core tracked s (cell+1) value) w.1 w.2))}[_] = _
            rw [overwrite_nil core tracked s (cell+1) value tape]
          | cons head tail =>
            have changed : overwriteTapes core tracked s.1.2 (cell+1) value tracked =
                head :: tail.set cell value := by
              simp [overwriteTapes, tape]
            rw [AnswerTape.tapeStep_run_cons cached changed,
              AnswerTape.tapeStep_run_cons cached tape]
            simp only [pure_bind]
            change Pr{let z ← ((simulateQ (roleRunImpl core) (next (cast hR.symm head))).run
              (post core tracked point (overwrite core tracked s (cell+1) value)
                (cast hR.symm head)
                (s.1.1.cacheQuery point (cast hR.symm head),
                  Function.update (overwriteTapes core tracked s.1.2 (cell+1) value)
                    tracked (tail.set cell value))))}[_] = _
            rw [overwriteTapes_update_self, post_overwrite]
            simpa only [post_cnt, ↓reduceIte, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using ih (cast hR.symm head)
                (post core tracked point s (cast hR.symm head)
                  (s.1.1.cacheQuery point (cast hR.symm head),
                    Function.update s.1.2 tracked tail)) index cell value (by omega)
  · cases cached : s.1.1 point with
    | some answer =>
      rw [AnswerTape.tapeStep_run_some cached, AnswerTape.tapeStep_run_some cached]
      simp only [pure_bind]
      change Pr{let z ← ((simulateQ (roleRunImpl core) (next answer)).run
        (post core j point (overwrite core tracked s cell value) answer
          (s.1.1, overwriteTapes core tracked s.1.2 cell value)))}[_] = _
      rw [post_overwrite]
      simpa only [post_cnt, jf, ↓reduceIte, Nat.add_zero]
        using ih answer (post core j point s answer s.1) index cell value horder
    | none =>
      have changed : overwriteTapes core tracked s.1.2 cell value j = s.1.2 j :=
        overwriteTapes_apply_ne core tracked s.1.2 cell value j jf
      cases tape : s.1.2 j with
      | nil =>
        rw [AnswerTape.tapeStep_run_nil cached (changed.trans tape),
          AnswerTape.tapeStep_run_nil cached tape]
        simp only [bind_map_left]
        rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
        apply tsum_congr
        intro answer
        congr 1
        change Pr{let z ← ((simulateQ (roleRunImpl core) (next answer)).run
          (post core j point (overwrite core tracked s cell value) answer
            (s.1.1.cacheQuery point answer, overwriteTapes core tracked s.1.2 cell value)))}[_] = _
        rw [post_overwrite]
        simpa only [post_cnt, jf, ↓reduceIte, Nat.add_zero]
          using ih answer (post core j point s answer
            (s.1.1.cacheQuery point answer, s.1.2)) index cell value horder
      | cons head tail =>
        rw [AnswerTape.tapeStep_run_cons cached (changed.trans tape),
          AnswerTape.tapeStep_run_cons cached tape]
        simp only [pure_bind]
        change Pr{let z ← ((simulateQ (roleRunImpl core) (next (cast hR.symm head))).run
          (post core j point (overwrite core tracked s cell value) (cast hR.symm head)
            (s.1.1.cacheQuery point (cast hR.symm head),
              Function.update (overwriteTapes core tracked s.1.2 cell value) j tail)))}[_] = _
        rw [overwriteTapes_update_ne core tracked s.1.2 cell value j jf tail, post_overwrite]
        simpa only [post_cnt, jf, ↓reduceIte, Nat.add_zero]
          using ih (cast hR.symm head) (post core j point s (cast hR.symm head)
            (s.1.1.cacheQuery point (cast hR.symm head), Function.update s.1.2 j tail))
            index cell value horder

end SLHDSA.Security.Coverage.NativeCausality

namespace SLHDSA.Security.Coverage.NativeCausality

/-- A future cell of any tracked unread tape cannot affect reaching its relative query count. -/
theorem prEvent_cnt_overwrite
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (tracked : TapeClass) {α : Type} (program : OracleComp (roleSpec core) α)
    (s : RoleState core) (index cell : Nat) (value : tapeClassRange core tracked)
    (horder : index ≤ cell) :
    Pr{let z ← ((simulateQ (roleRunImpl core) program).run
      ((s.1.1, Function.update s.1.2 tracked ((s.1.2 tracked).set cell value)), s.2))}[
        s.2.1.cnt tracked + index < z.2.2.1.cnt tracked] =
    Pr{let z ← (simulateQ (roleRunImpl core) program).run s}[
      s.2.1.cnt tracked + index < z.2.2.1.cnt tracked] := by
  classical
  change Pr{let z ← ((simulateQ (roleRunImpl core) program).run
    (overwrite core tracked s cell value))}[_] = _
  induction program using OracleComp.inductionOn generalizing s index cell value with
  | pure result => simp [overwrite, simulateQ_pure]
  | query_bind queried next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with n | (point | point)
    · rw [run_uniform, run_uniform]
      simp only [bind_map_left]
      rw [prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]
      apply tsum_congr
      intro answer
      congr 1
      exact ih answer s index cell value horder
    · rw [run_inl, run_inl]
      simp only [bind_assoc, pure_bind]
      exact tapeStep_causal core tracked _ point (range_eq_tapeClassRange core (.inl point)) next
        (fun answer state i c v h => ih answer state i c v h) s index cell value horder
    · rw [run_inr, run_inr]
      simp only [bind_assoc, pure_bind]
      exact tapeStep_causal core tracked _ point (range_eq_tapeClassRange core (.inr point)) next
        (fun answer state i c v h => ih answer state i c v h) s index cell value horder

end SLHDSA.Security.Coverage.NativeCausality

#print axioms SLHDSA.Security.Coverage.NativeCausality.prEvent_cnt_overwrite

#print axioms SLHDSA.Security.Coverage.NativeCausality.overwriteTapes_apply_ne
#print axioms SLHDSA.Security.Coverage.NativeCausality.overwrite_nil
#print axioms SLHDSA.Security.Coverage.NativeCausality.overwriteTapes_update_ne
#print axioms SLHDSA.Security.Coverage.NativeCausality.overwriteTapes_update_self
#print axioms SLHDSA.Security.Coverage.NativeCausality.tapeStep_causal
#print axioms SLHDSA.Security.Coverage.NativeCausality.prEvent_cnt_overwrite
