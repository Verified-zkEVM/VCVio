/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CoverageRun
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
import VCVio.OracleComp.EvalDist.Sum

/-! # Native class-counter observations and current tape updates -/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security.Coverage.NativeCausality

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- Overwrite one cell of the forger tape in a tape family. -/
def overwriteTapes (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell : Nat) (value : Bytes vp.params.m) : (j : TapeClass) → List (tapeClassRange core j) :=
  Function.update L TapeClass.forger ((L TapeClass.forger).set cell value)

/-- Overwrite one cell of the currently unread forger tape, leaving every other state field. -/
def overwrite (s : RoleState core) (cell : Nat) (value : Bytes vp.params.m) : RoleState core :=
  ((s.1.1, overwriteTapes core s.1.2 cell value), s.2)

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- The one-step post-state of the existing class-indexed tape bookkeeping. -/
def post (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (s' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j))) :
    RoleState core :=
  (s', (AnswerTape.classPosStep (tapeClassRange core) j point s.1 answer s' s.2.1,
    AnswerTape.freshHitStep (IsRandPoint core) (randRel core) s.1.1 point answer s.2.2))

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- A future-cell overwrite preserves the empty/nonempty distinction read by bookkeeping. -/
theorem classPosStep_overwrite (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (s' s'' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j)))
    (cell : Nat) (value : Bytes vp.params.m) :
    AnswerTape.classPosStep (tapeClassRange core) j point (overwrite core s cell value).1
        answer s' s.2.1 =
      AnswerTape.classPosStep (tapeClassRange core) j point s.1 answer s'' s.2.1 := by
  classical
  unfold AnswerTape.classPosStep overwrite overwriteTapes
  by_cases same : j = TapeClass.forger
  · subst j
    cases hc : s.1.1 point with
    | some cached => simp
    | none =>
      cases hl : s.1.2 TapeClass.forger with
      | nil => simp
      | cons head tail => cases cell <;> simp
  · simp [Function.update_of_ne same]

omit [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] in
/-- Passive post-state bookkeeping commutes with an overwrite of unread tape cells. -/
theorem post_overwrite (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (cache : (jointSpec core).QueryCache)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (cell cell' : Nat) (value : Bytes vp.params.m) :
    post core j point (overwrite core s cell value) answer
        (cache, overwriteTapes core L cell' value) =
      overwrite core (post core j point s answer (cache, L)) cell' value := by
  exact congrArg (fun p => ((cache, overwriteTapes core L cell' value), p,
    AnswerTape.freshHitStep (IsRandPoint core) (randRel core) s.1.1 point answer s.2.2))
    (classPosStep_overwrite core j point s answer _ (cache, L) cell value)

/-- A private uniform query changes none of the native state. -/
theorem run_uniform (n : Nat) (s : RoleState core) :
    ((roleRunImpl core (.inl n)).run s) =
      (fun value => (value, s)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  rw [QueryImpl.extendState_apply]
  simp [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inl,
    AnswerTape.classPosAuxFwd, AnswerTape.freshHitAux]

/-- A forger-copy step uses its existing tape step and passive bookkeeping. -/
theorem run_inl (point : (jointSpec core).Domain) (s : RoleState core) :
    ((roleRunImpl core (.inr (.inl point))).run s) = (do
      let w ← (AnswerTape.tapeStep (tapeClassRange core) (tapeClass core (.inl point)) point
        (range_eq_tapeClassRange core (.inl point))).run s.1
      pure (w.1, post core (tapeClass core (.inl point)) point s w.1 w.2)) := by
  rw [QueryImpl.extendState_apply]
  simp only [AnswerTape.tapeImplFwd, QueryImpl.add_apply_inr,
    AnswerTape.tapeCachingImplClass_apply_inl]
  rfl

/-- A signer-copy step uses its existing tape step and passive bookkeeping. -/
theorem run_inr (point : (jointSpec core).Domain) (s : RoleState core) :
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
theorem post_cnt (j : TapeClass) (point : (jointSpec core).Domain)
    (s : RoleState core) (answer : (jointSpec core).Range point)
    (s' : (jointSpec core).QueryCache × ((j : TapeClass) → List (tapeClassRange core j))) :
    (post core j point s answer s').2.1.cnt TapeClass.forger =
      s.2.1.cnt TapeClass.forger + if j = TapeClass.forger then 1 else 0 := by
  classical
  cases j <;> unfold post AnswerTape.classPosStep <;> split <;> simp

/-- The forger counter never decreases at a native query. -/
theorem cnt_step_mono (t : (roleSpec core).Domain) (s : RoleState core)
    (y : (roleSpec core).Range t × RoleState core)
    (hy : y ∈ support ((roleRunImpl core t).run s)) :
    s.2.1.cnt TapeClass.forger ≤ y.2.2.1.cnt TapeClass.forger := by
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

/-- A native program preserves every lower bound on its initial forger counter. -/
theorem cnt_run_mono {α : Type} (program : OracleComp (roleSpec core) α)
    (s : RoleState core) (z : α × RoleState core)
    (hz : z ∈ support ((simulateQ (roleRunImpl core) program).run s)) :
    s.2.1.cnt TapeClass.forger ≤ z.2.2.1.cnt TapeClass.forger := by
  exact simulateQ_run_preserves_inv_of_query (roleRunImpl core)
    (fun state => s.2.1.cnt TapeClass.forger ≤ state.2.1.cnt TapeClass.forger)
    (fun t state h y hy => h.trans (cnt_step_mono core t state y hy)) program s le_rfl z hz

/-- Once reached, a counter threshold remains reached with probability one. -/
theorem prEvent_reached_eq_one {α : Type} (program : OracleComp (roleSpec core) α)
    (s : RoleState core) (threshold : Nat) (h : threshold < s.2.1.cnt TapeClass.forger) :
    Pr{let z ← (simulateQ (roleRunImpl core) program).run s}[
      threshold < z.2.2.1.cnt TapeClass.forger] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _ fun z hz =>
    h.trans_le (cnt_run_mono core program s z hz)

end SLHDSA.Security.Coverage.NativeCausality

#print axioms SLHDSA.Security.Coverage.NativeCausality.prEvent_reached_eq_one

#print axioms SLHDSA.Security.Coverage.NativeCausality.classPosStep_overwrite
#print axioms SLHDSA.Security.Coverage.NativeCausality.post_overwrite
#print axioms SLHDSA.Security.Coverage.NativeCausality.run_uniform
#print axioms SLHDSA.Security.Coverage.NativeCausality.run_inl
#print axioms SLHDSA.Security.Coverage.NativeCausality.run_inr
#print axioms SLHDSA.Security.Coverage.NativeCausality.post_cnt
#print axioms SLHDSA.Security.Coverage.NativeCausality.cnt_step_mono
#print axioms SLHDSA.Security.Coverage.NativeCausality.cnt_run_mono
#print axioms SLHDSA.Security.Coverage.NativeCausality.prEvent_reached_eq_one
