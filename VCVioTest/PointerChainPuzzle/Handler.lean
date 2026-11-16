/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Handler
import all VCVio.Schemes.PointerChainPuzzle.Basic
import all VCVio.Schemes.PointerChainPuzzle.Path
import all VCVio.Schemes.PointerChainPuzzle.Ideal
import all VCVio.Schemes.PointerChainPuzzle.Handler

/-!
# The atomic ideal handler on small parameters

Checks of the ideal handler of the pointer-chain puzzle for two chains of one step (`n = 2`,
`m = 1`) over small finite types:

* atomicity: in a round holding the path inputs of `s_0` and of `y_{0,1}`, submitted with nothing
  reached, only `s_0` is reached; the point of `y_{0,1}` is not legitimate in that round, so it is
  answered by the lazy random oracle, and it becomes legitimate in the next round;
* a point repeated in a round receives one answer;
* the round counter after `k` rounds is `k` more than before.

The checks reduce the derived decidable equality of points and path values and the definitions
of the handler, so the scheme modules are imported with `import all`. The answer types are
sampled through `SampleableType.Fin`, so loading this module enumerates no type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle

namespace VCVioTest.PointerChainPuzzle.Handler

/-- States are `Fin 11`. -/
abbrev S := Fin 11

/-- Links are `Fin 5`. -/
abbrev L := Fin 5

/-- Salts and contexts are `Fin 3`. -/
abbrev Salt := Fin 3

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := ⟨ctx.val + 6, by omega⟩

/-- Labels of two chains of one step: state `y_{i,k}` has label `3 i + k + 1`, mask `μ_0` has
label `2`, accumulator `a_i` has label `7 + i`, the key `9` and the commitment `10`. -/
def labels : Labels 2 1 S L
  | .state i k => ⟨3 * i.val + k.val + 1, by omega⟩
  | .mask _ => 2
  | .acc i => ⟨7 + i.val, by omega⟩
  | .key => 9
  | .commit => 10

/-- A puzzle with salt `2`, first link `3` and masked link `4`, committing to the key label. -/
def puzzle : Puzzle 2 S L Salt := labelPuzzle 2 3 (fun _ => 4) labels

/-- The path value `y_{0,1}`, one chain step after `s_0 = y_{0,0}`. -/
def y01 : PathValue 2 1 := .state 0 1

/-- The path input of a path value. -/
def input (v : PathValue 2 1) : Point 2 S L Salt Salt :=
  pathInput 1 mkCtx initAcc puzzle labels v

/-- The round holding the path inputs of `s_0` and of `y_{0,1}`. -/
def round₀ : List (Point 2 S L Salt Salt) := [input .firstStart, input y01]

/-! ## Atomicity of a round -/

/-- `y_{0,1}` has `s_0` as its only predecessor, and its path input is a step on the label of
`s_0`. -/
example : y01.preds = {PathValue.firstStart} := by decide +kernel

example : input y01 = .step 2 0 (labels .firstStart) := rfl

/-- Against the empty reached set, the point of `s_0` is legitimate and the point of `y_{0,1}` is
not; the latter is a path input, so it is online-bad. -/
example : IsLegit 1 mkCtx initAcc puzzle labels ∅ (input .firstStart) .firstStart := by
  decide +kernel

example : (legitLabel 1 mkCtx initAcc puzzle labels ∅ (input .firstStart)).isSome = true := by
  decide +kernel

example : (legitLabel 1 mkCtx initAcc puzzle labels ∅ (input y01)).isNone = true := by
  decide +kernel

example : OnlineBadAt 1 mkCtx initAcc puzzle labels ∅ (input y01) := by decide +kernel

/-- The round `[s_0, y_{0,1}]` submitted with nothing reached reaches `s_0` only. -/
example : newlyReached 1 mkCtx initAcc puzzle labels ∅ round₀ = {PathValue.firstStart} := by
  decide +kernel

/-- Once `s_0` is reached, the same round reaches both path values. -/
example : newlyReached 1 mkCtx initAcc puzzle labels {PathValue.firstStart} round₀ =
    {PathValue.firstStart, y01} := by
  decide +kernel

example : (legitLabel 1 mkCtx initAcc puzzle labels {PathValue.firstStart} (input y01)).isSome =
    true := by
  decide +kernel

/-- In every run of the round `[s_0, y_{0,1}]` from the initial state, `s_0` is reached and
`y_{0,1}` is not, the counter is `1`, and online Bad is raised by the point of `y_{0,1}`. -/
theorem round₀_atomic (c : (oracleSpec 2 S L Salt Salt).QueryCache)
    {z : (oracleSpec 2 S L Salt Salt).batch.Range round₀ × IdealState 2 1 S L Salt Salt}
    (hz : z ∈ support ((idealImpl 1 mkCtx initAcc puzzle labels (.inr round₀)).run
      (IdealState.init c))) :
    z.2.reached = {PathValue.firstStart} ∧ z.2.round = 1 ∧
      z.2.OnlineBad 1 mkCtx initAcc puzzle labels := by
  obtain ⟨c', hc⟩ := exists_of_mem_support_idealImpl_inr hz
  rw [hc]
  refine ⟨?_, rfl, ?_⟩
  · rw [IdealState.afterRound_reached, IdealState.init_reached, Finset.empty_union]
    decide +kernel
  · refine IdealState.onlineBad_afterRound_of_mem (t := input y01)
      (List.mem_cons_of_mem _ List.mem_cons_self) ?_ c'
    rw [IdealState.init_reached]
    decide +kernel

/-! ## Repeated points -/

/-- A point repeated in a round receives one answer: the second occurrence is answered from the
cache, or by the same label. -/
theorem repeated_point_one_answer (t : Point 2 S L Salt Salt) (s : IdealState 2 1 S L Salt Salt)
    {z : (oracleSpec 2 S L Salt Salt).batch.Range [t, t] × IdealState 2 1 S L Salt Salt}
    (hz : z ∈ support ((idealImpl 1 mkCtx initAcc puzzle labels (.inr [t, t])).run s)) :
    z.1 ⟨0, Nat.zero_lt_succ _⟩ = z.1 ⟨1, Nat.one_lt_succ_succ _⟩ := by
  rw [idealImpl_inr_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp only [QueryImpl.batch_cons, QueryImpl.batch_nil, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨u₁, h₁, u₂, h₂, w', hw', rfl⟩ := hw
  rw [idealPoint_run_of_mem_support h₁, support_pure] at h₂
  obtain ⟨x, hx, _, rfl, rfl⟩ := h₂
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rfl

/-! ## The round counter -/

/-- `k` rounds, each submitting the points `ts`. -/
def rounds (ts : List (Point 2 S L Salt Salt)) :
    ℕ → OracleComp (unifSpec + (oracleSpec 2 S L Salt Salt).batch) Unit
  | 0 => pure ()
  | k + 1 => do
      let _ ← liftM ((unifSpec + (oracleSpec 2 S L Salt Salt).batch).query (.inr ts))
      rounds ts k

/-- After `k` rounds the counter is `k` more than before. -/
theorem round_rounds (ts : List (Point 2 S L Salt Salt)) (k : ℕ)
    (s : IdealState 2 1 S L Salt Salt) {z : Unit × IdealState 2 1 S L Salt Salt}
    (hz : z ∈ support ((simulateQ (idealImpl 1 mkCtx initAcc puzzle labels) (rounds ts k)).run s)) :
    z.2.round = s.round + k := by
  induction k generalizing s with
  | zero =>
      simp only [rounds, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      rfl
  | succ k ih =>
      have hz' : z ∈ support
          (((simulateQ (idealImpl 1 mkCtx initAcc puzzle labels)
                (OracleSpec.query (spec := unifSpec + (oracleSpec 2 S L Salt Salt).batch)
                    (Sum.inr ts) :
                  OracleComp (unifSpec + (oracleSpec 2 S L Salt Salt).batch)
                    ((unifSpec + (oracleSpec 2 S L Salt Salt).batch).Range (.inr ts)))).run s) >>=
            fun us => (simulateQ (idealImpl 1 mkCtx initAcc puzzle labels) (rounds ts k)).run
              us.2) := by
        simpa [rounds, simulateQ_bind, OracleComp.liftM_def] using hz
      obtain ⟨us, hus, hzc⟩ := (mem_support_bind_iff _ _ _).1 hz'
      replace hus : us ∈ support ((idealImpl 1 mkCtx initAcc puzzle labels (.inr ts)).run s) := by
        simpa [simulateQ_spec_query] using hus
      obtain ⟨c, hc⟩ := exists_of_mem_support_idealImpl_inr hus
      rw [ih us.2 hzc, hc, IdealState.afterRound_round]
      omega

/-- Three rounds of `[s_0, y_{0,1}]` from the initial state leave the counter at `3`. -/
example (c : (oracleSpec 2 S L Salt Salt).QueryCache) {z : Unit × IdealState 2 1 S L Salt Salt}
    (hz : z ∈ support ((simulateQ (idealImpl 1 mkCtx initAcc puzzle labels) (rounds round₀ 3)).run
      (IdealState.init c))) :
    z.2.round = 3 :=
  round_rounds round₀ 3 _ hz

end VCVioTest.PointerChainPuzzle.Handler
