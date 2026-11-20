/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageRun
import VCVio.OracleComp.EvalDist.Sum
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position

/-!
# Causality of consumed signer and forger tape positions

If the queried index is at or before the overwritten cell of the unread tape, overwriting
preserves its reach probability. This lets a caller price the entries consumed by a role
against an independently sampled tape.
-/

@[expose] public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA.Security

namespace SLHDSA.Security.Coverage.ClassCountCausality

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (which : TapeClass)

/-- Overwrite one cell of the selected class tape in a tape family. -/
def overwriteTapes (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell : Nat) (value : tapeClassRange core which) :
    (j : TapeClass) → List (tapeClassRange core j) :=
  Function.update L which ((L which).set cell value)

/-- Overwrite one cell of the currently unread selected class tape,
leaving every other state field. -/
def overwrite (s : RoleState core) (cell : Nat) (value : tapeClassRange core which) :
    RoleState core :=
  ((s.1.1, overwriteTapes core which s.1.2 cell value), s.2)

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- The one-step post-state of the existing class-indexed tape bookkeeping. -/
private def post (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (s' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j))) :
    RoleState core :=
  (s', (AnswerTape.classPosStep (tapeClassRange core) j point s.1 answer s' s.2.1,
    AnswerTape.freshHitStep (IsRandPoint core) (randRel core) s.1.1 point answer s.2.2))

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- A future-cell overwrite preserves the empty/nonempty distinction read by bookkeeping. -/
private theorem classPosStep_overwrite (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (s' s'' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j)))
    (cell : Nat) (value : tapeClassRange core which) :
    AnswerTape.classPosStep (tapeClassRange core) j point (overwrite core which s cell value).1
        answer s' s.2.1 =
      AnswerTape.classPosStep (tapeClassRange core) j point s.1 answer s'' s.2.1 := by
  classical
  unfold AnswerTape.classPosStep overwrite overwriteTapes
  by_cases same : j = which
  · subst j
    cases hc : s.1.1 point with
    | some cached => simp
    | none =>
      cases hl : s.1.2 which with
      | nil => simp
      | cons head tail => cases cell <;> simp
  · simp [Function.update_of_ne same]

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- Passive post-state bookkeeping commutes with an overwrite of unread tape cells. -/
private theorem post_overwrite (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (cache : (jointSpec core).QueryCache)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell cell' : Nat) (value : tapeClassRange core which) :
    post core j point (overwrite core which s cell value) answer
        (cache, overwriteTapes core which L cell' value) =
      overwrite core which (post core j point s answer (cache, L)) cell' value := by
  exact congrArg (fun p => ((cache, overwriteTapes core which L cell' value), p,
    AnswerTape.freshHitStep (IsRandPoint core) (randRel core) s.1.1 point answer s.2.2))
    (classPosStep_overwrite core which j point s answer _ (cache, L) cell value)

/-- A private uniform query changes none of the native state. -/
private theorem run_uniform (n : Nat) (s : RoleState core) :
    ((roleRunImpl core (.inl n)).run s) =
      (fun value => (value, s)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  rw [QueryImpl.extendState_apply]
  simp [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inl,
    AnswerTape.classPosAuxFwd, AnswerTape.freshHitAux]

/-- A forger-copy step uses its existing tape step and passive bookkeeping. -/
private theorem run_inl (point : (jointSpec core).Domain) (s : RoleState core) :
    ((roleRunImpl core (.inr (.inl point))).run s) = (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) (tapeClass core (.inl point)) point
        (range_eq_tapeClassRange core (.inl point))).run s.1
      pure (w.1, post core (tapeClass core (.inl point)) point s w.1 w.2)) := by
  rw [QueryImpl.extendState_apply]
  simp only [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inr,
    AnswerTape.tapeCachingImplClass_apply_inl]
  rfl

/-- A signer-copy step uses its existing tape step and passive bookkeeping. -/
private theorem run_inr (point : (jointSpec core).Domain) (s : RoleState core) :
    ((roleRunImpl core (.inr (.inr point))).run s) = (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) (tapeClass core (.inr point)) point
        (range_eq_tapeClassRange core (.inr point))).run s.1
      pure (w.1, post core (tapeClass core (.inr point)) point s w.1 w.2)) := by
  rw [QueryImpl.extendState_apply]
  simp only [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inr,
    AnswerTape.tapeCachingImplClass_apply_inr]
  rfl

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- Every tape query increments precisely its own class counter, including cache hits. -/
private theorem post_cnt (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (s' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j))) :
    (post core j point s answer s').2.1.cnt which =
      s.2.1.cnt which + if j = which then 1 else 0 := by
  classical
  cases j <;> cases which <;> unfold post AnswerTape.classPosStep <;> split <;> simp

/-- The selected class counter never decreases at a native query. -/
private theorem cnt_step_mono (t : (roleSpec core).Domain) (s : RoleState core)
    (y : (roleSpec core).Range t × RoleState core)
    (hy : y ∈ support ((roleRunImpl core t).run s)) :
    s.2.1.cnt which ≤ y.2.2.1.cnt which := by
  rcases t with n | (point | point)
  · rw [run_uniform, support_map] at hy
    obtain ⟨value, _, rfl⟩ := hy
    exact le_rfl
  all_goals
    first | rw [run_inl, mem_support_bind_iff] at hy | rw [run_inr, mem_support_bind_iff] at hy
    obtain ⟨w, _, hy⟩ := hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst y
    rw [post_cnt]
    exact Nat.le_add_right _ _

/-- A native program preserves every lower bound on its initial selected class counter. -/
private theorem cnt_run_mono {α : Type} (program : OracleComp (roleSpec core) α)
    (s : RoleState core) (z : α × RoleState core)
    (hz : z ∈ support ((simulateQ (roleRunImpl core) program).run s)) :
    s.2.1.cnt which ≤ z.2.2.1.cnt which := by
  exact simulateQ_run_preserves_inv_of_query (roleRunImpl core)
    (fun state => s.2.1.cnt which ≤ state.2.1.cnt which)
    (fun t state h y hy => h.trans (cnt_step_mono core which t state y hy)) program s le_rfl z hz

end SLHDSA.Security.Coverage.ClassCountCausality

namespace SLHDSA.Security.Coverage.ClassCountCausality

variable {vp : ValidatedParams} (core : CorePrimitives vp.params) (which : TapeClass)

/-- An overwrite changes no other class's current tape. -/
private theorem overwriteTapes_apply_ne (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell : Nat) (value : tapeClassRange core which) (j : TapeClass) (hj : j ≠ which) :
    overwriteTapes core which L cell value j = L j := by
  simp [overwriteTapes, Function.update_of_ne hj]

/-- An overwrite of an empty selected class tape is a no-op. -/
private theorem overwrite_nil (s : RoleState core) (cell : Nat) (value : tapeClassRange core which)
    (h : s.1.2 which = []) : overwrite core which s cell value = s := by
  have tapes : overwriteTapes core which s.1.2 cell value = s.1.2 := by
    unfold overwriteTapes
    rw [h, List.set_nil, ←h, Function.update_eq_self]
  simp only [overwrite, tapes, Prod.eta]

/-- Consuming another class's head commutes with overwriting the selected class tape. -/
private theorem overwriteTapes_update_ne (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell : Nat) (value : tapeClassRange core which) (j : TapeClass) (hj : j ≠ which)
    (tail : List (tapeClassRange core j)) :
    Function.update (overwriteTapes core which L cell value) j tail =
      overwriteTapes core which (Function.update L j tail) cell value := by
  unfold overwriteTapes
  rw [Function.update_of_ne (Ne.symm hj)]
  exact (Function.update_comm hj tail ((L which).set cell value) L).symm

/-- Consuming the selected class head leaves precisely the overwritten remainder. -/
private theorem overwriteTapes_update_self (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell cell' : Nat) (value : tapeClassRange core which)
    (tail : List (tapeClassRange core which)) :
    Function.update (overwriteTapes core which L cell value) which (tail.set cell' value) =
      overwriteTapes core which (Function.update L which tail) cell' value := by
  simp [overwriteTapes]

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- One existing tape step preserves future-cell causality of its native continuations. -/
private theorem tapeStep_causal {α : Type} (j : TapeClass) (point : (jointSpec core).Domain)
    (hR : (jointSpec core).Range point = tapeClassRange core j)
    (next : (jointSpec core).Range point → OracleComp (roleSpec core) α)
    (ih : ∀ answer (s : RoleState core) (index cell : Nat) (value : tapeClassRange core which),
      index ≤ cell →
      Pr{let z ← (simulateQ (roleRunImpl core) (next answer)).run
          (overwrite core which s cell value)}[s.2.1.cnt which + index <
            z.2.2.1.cnt which] =
      Pr{let z ← (simulateQ (roleRunImpl core) (next answer)).run s}[s.2.1.cnt which +
        index < z.2.2.1.cnt which])
    (s : RoleState core) (index cell : Nat) (value : tapeClassRange core which)
    (horder : index ≤ cell) :
    Pr{let z ← (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) j point hR).run
        (overwrite core which s cell value).1
      (simulateQ (roleRunImpl core) (next w.1)).run
        (post core j point (overwrite core which s cell value) w.1 w.2))}[
      s.2.1.cnt which + index < z.2.2.1.cnt which] =
    Pr{let z ← (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) j point hR).run s.1
      (simulateQ (roleRunImpl core) (next w.1)).run (post core j point s w.1 w.2))}[
      s.2.1.cnt which + index < z.2.2.1.cnt which] := by
  classical
  dsimp only [overwrite]
  by_cases jf : j = which
  · subst j
    cases index with
    | zero =>
      trans (1 : ℝ≥0∞)
      · apply prEvent_eq_one_of_forall_mem_support
        intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        have grows := cnt_run_mono core which (next w.1)
          (post core which point (overwrite core which s cell value) w.1 w.2) z hz
        rw [post_cnt] at grows
        simp only [overwrite, ↓reduceIte] at grows
        omega
      · symm
        apply prEvent_eq_one_of_forall_mem_support
        intro z hz
        rw [mem_support_bind_iff] at hz
        obtain ⟨w, _, hz⟩ := hz
        have grows := cnt_run_mono core which (next w.1)
          (post core which point s w.1 w.2) z hz
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
            (post core which point (overwrite core which s (cell+1) value) answer
              (s.1.1, overwriteTapes core which s.1.2 (cell+1) value)))}[_] = _
          rw [post_overwrite]
          simpa only [post_cnt, ↓reduceIte, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            using ih answer (post core which point s answer s.1) index (cell+1)
              value (by omega)
        | none =>
          cases tape : s.1.2 which with
          | nil =>
            change Pr{let z ← (do
              let w ← (AnswerTape.tapeStep (tapeClassRange core) which point hR).run
                (overwrite core which s (cell+1) value).1
              (simulateQ (roleRunImpl core) (next w.1)).run
                (post core which point
                  (overwrite core which s (cell+1) value) w.1 w.2))}[_] = _
            rw [overwrite_nil core which s (cell+1) value tape]
          | cons head tail =>
            have changed : overwriteTapes core which s.1.2 (cell+1) value which =
                head :: tail.set cell value := by
              simp [overwriteTapes, tape]
            rw [AnswerTape.tapeStep_run_cons cached changed,
              AnswerTape.tapeStep_run_cons cached tape]
            simp only [pure_bind]
            change Pr{let z ← ((simulateQ (roleRunImpl core) (next (cast hR.symm head))).run
              (post core which point (overwrite core which s (cell+1) value)
                (cast hR.symm head)
                (s.1.1.cacheQuery point (cast hR.symm head),
                  Function.update (overwriteTapes core which s.1.2 (cell+1) value)
                    which (tail.set cell value))))}[_] = _
            rw [overwriteTapes_update_self, post_overwrite]
            simpa only [post_cnt, ↓reduceIte, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using ih (cast hR.symm head)
                (post core which point s (cast hR.symm head)
                  (s.1.1.cacheQuery point (cast hR.symm head),
                    Function.update s.1.2 which tail)) index cell value (by omega)
  · cases cached : s.1.1 point with
    | some answer =>
      rw [AnswerTape.tapeStep_run_some cached, AnswerTape.tapeStep_run_some cached]
      simp only [pure_bind]
      change Pr{let z ← ((simulateQ (roleRunImpl core) (next answer)).run
        (post core j point (overwrite core which s cell value) answer
          (s.1.1, overwriteTapes core which s.1.2 cell value)))}[_] = _
      rw [post_overwrite]
      simpa only [post_cnt, jf, ↓reduceIte, Nat.add_zero]
        using ih answer (post core j point s answer s.1) index cell value horder
    | none =>
      have changed : overwriteTapes core which s.1.2 cell value j = s.1.2 j :=
        overwriteTapes_apply_ne core which s.1.2 cell value j jf
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
          (post core j point (overwrite core which s cell value) answer
            (s.1.1.cacheQuery point answer, overwriteTapes core which s.1.2 cell value)))}[_] = _
        rw [post_overwrite]
        simpa only [post_cnt, jf, ↓reduceIte, Nat.add_zero]
          using ih answer (post core j point s answer
            (s.1.1.cacheQuery point answer, s.1.2)) index cell value horder
      | cons head tail =>
        rw [AnswerTape.tapeStep_run_cons cached (changed.trans tape),
          AnswerTape.tapeStep_run_cons cached tape]
        simp only [pure_bind]
        change Pr{let z ← ((simulateQ (roleRunImpl core) (next (cast hR.symm head))).run
          (post core j point (overwrite core which s cell value) (cast hR.symm head)
            (s.1.1.cacheQuery point (cast hR.symm head),
              Function.update (overwriteTapes core which s.1.2 cell value) j tail)))}[_] = _
        rw [overwriteTapes_update_ne core which s.1.2 cell value j jf tail, post_overwrite]
        simpa only [post_cnt, jf, ↓reduceIte, Nat.add_zero]
          using ih (cast hR.symm head) (post core j point s (cast hR.symm head)
            (s.1.1.cacheQuery point (cast hR.symm head), Function.update s.1.2 j tail))
            index cell value horder

/-- A future cell of the unread selected class tape cannot influence reaching
the relative counter. -/
theorem prEvent_cnt_overwrite {α : Type} (program : OracleComp (roleSpec core) α)
    (s : RoleState core) (index cell : Nat) (value : tapeClassRange core which)
    (horder : index ≤ cell) :
    Pr{let z ← (simulateQ (roleRunImpl core) program).run (overwrite core which s cell value)}[
      s.2.1.cnt which + index < z.2.2.1.cnt which] =
    Pr{let z ← (simulateQ (roleRunImpl core) program).run s}[
      s.2.1.cnt which + index < z.2.2.1.cnt which] := by
  classical
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
      exact tapeStep_causal core which _ point (range_eq_tapeClassRange core (.inl point)) next
        (fun answer state i c v h => ih answer state i c v h) s index cell value horder
    · rw [run_inr, run_inr]
      simp only [bind_assoc, pure_bind]
      exact tapeStep_causal core which _ point (range_eq_tapeClassRange core (.inr point)) next
        (fun answer state i c v h => ih answer state i c v h) s index cell value horder

end SLHDSA.Security.Coverage.ClassCountCausality
