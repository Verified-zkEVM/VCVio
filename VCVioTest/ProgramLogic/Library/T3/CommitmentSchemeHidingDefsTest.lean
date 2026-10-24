/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.CommitmentScheme.Hiding.CountBounds
public import VCVio.ProgramLogic.Library.T3.CommitmentScheme.HidingDefs

/-!
# Tests for the commitment hiding handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.CommitmentScheme.HidingDefs`:
repeated queries, the bad frame of an opaque adversary, and existing per-step and whole-run
lemmas of `Examples.CommitmentScheme.Hiding.CountBounds` re-proved in one to three lines.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.CommitmentHiding

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {M S C : Type} [DecidableEq M] [DecidableEq S]

/-- Two queries at the same point agree, and the second one is not counted. -/
example (s : S) (m : M) (n : ℕ) :
    ⦃ fun st => st.2 = n ⦄
      simulateQ (hidingImpl₁ s) (do
        let a ← ((CMOracle M S C).query (m, s) : OracleComp (CMOracle M S C) C)
        let b ← ((CMOracle M S C).query (m, s) : OracleComp (CMOracle M S C) C)
        return (a, b))
    ⦃ fun z st => z.1 = z.2 ∧ st.2 ≤ n + 1 ⦄ := by
  vcgen
  grind

/-- An opaque adversary under the simulator never clears the bad event. -/
example [Inhabited M] [Inhabited S] {α : Type} (s : S) (adv : OracleComp (CMOracle M S C) α) :
    ⦃ fun st => hidingBad st ∧ True ⦄ simulateQ (hidingImplSim s) adv
    ⦃ fun _ st => hidingBad st ⦄ := by
  vcgen
  grind [hidingBad, Prod.le_def]

/-- `count_mono_step_hidingImplCountAll`, re-proved. -/
example (s : S) (ms : M × S) (st : QueryCache (CMOracle M S C) × (S → ℕ))
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms).run st)) :
    st.2 s ≤ x.2.2 s :=
  (monotoneState_hidingImplCountAll.step ms st x hx).2 s

/-- `count_mono_of_mem_support_run_hidingImplCountAll`, re-proved. -/
example {α : Type} (oa : OracleComp (CMOracle M S C) α)
    (st₀ : QueryCache (CMOracle M S C) × (S → ℕ))
    (z : α × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) (s : S) :
    st₀.2 s ≤ z.2.2 s :=
  (QueryImpl.MonotoneState.rel_of_mem_support hz).2 s

/-- `cache_le_of_mem_support_run_hidingImplCountAll`, re-proved. -/
example {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {st₀ : QueryCache (CMOracle M S C) × (S → ℕ)}
    {z : α × (QueryCache (CMOracle M S C) × (S → ℕ))}
    (hz : z ∈ support ((simulateQ hidingImplCountAll oa).run st₀)) : st₀.1 ≤ z.2.1 :=
  (QueryImpl.MonotoneState.rel_of_mem_support hz).1

/-- `hidingImpl₁_counter_le_succ`, re-proved. -/
example (s : S) (ms : M × S) (st : QueryCache (CMOracle M S C) × ℕ)
    (x : C × (QueryCache (CMOracle M S C) × ℕ)) (hx : x ∈ support ((hidingImpl₁ s ms).run st)) :
    st.2 ≤ x.2.2 ∧ x.2.2 ≤ st.2 + 1 := by
  obtain ⟨u, st'⟩ := x
  rcases (mem_support_hidingImpl₁_run_iff s).1 hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> grind

/-- `hidingCountInv_step_hidingImplCountAll`, re-proved. -/
example (ms₀ : M × S) (st : QueryCache (CMOracle M S C) × (S → ℕ)) (hInv : HidingCountInv st)
    (x : C × (QueryCache (CMOracle M S C) × (S → ℕ)))
    (hx : x ∈ support ((hidingImplCountAll (M := M) (S := S) (C := C) ms₀).run st)) :
    HidingCountInv x.2 := by
  obtain ⟨u, st'⟩ := x
  rcases mem_support_hidingImplCountAll_run_iff.1 hx with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    grind [HidingCountInv, Function.update_apply]

/-- Dropping the counter of the real hiding run is the caching run (`hidingReal_eq_impl₁`'s
core, for any program and state). -/
example {α : Type} (s : S) (oa : OracleComp (CMOracle M S C) α) :
    (simulateQ (hidingImpl₁ s) oa).run' (∅, 0) = (simulateQ cachingOracle oa).run' ∅ := by
  simpa [StateT.run'_eq, Functor.map_map] using
    congrArg (Prod.fst <$> ·) (map_run_simulateQ_hidingImpl₁_eq_cachingOracle s oa (∅, 0))

end VCVioTest.ProgramLogic.Library.T3.CommitmentHiding
