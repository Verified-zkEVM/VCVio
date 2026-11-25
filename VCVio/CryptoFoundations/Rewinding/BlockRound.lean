/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.Rewinding.ThresholdRound

/-!
# One block step

`Rewinding.thresholdChildren` runs a child at a first challenge and then collects the remaining
successful children of one round from a pool. A *block* is a round whose challenge has coordinates
`ι`, with a threshold `k j` at every coordinate. `blockChildren` runs the child at a centre `c₀`
and, on success, collects `k j - 1` successful children from the pool `pools j` of every
coordinate `j`.
It returns the centre's result and, for every coordinate, the collected results in the order they
were drawn.

The child is a parameter, so the step serves both the one-round finder, whose child asks the
acceptance oracle, and a recursion over rounds, whose child is the finder of the later rounds. With
one coordinate, the step is the threshold step: `thresholdChildren_eq_blockChildren`.
-/

public section

open OracleComp OracleSpec

/-- A finite family of computations over an index type with one element is the computation at
that element. -/
theorem Fintype.mPi_unique {α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {ι : Type}
    [Fintype ι] [Unique ι] (g : ι → m α) :
    Fintype.mPi g = (fun a _ => a) <$> g default := by
  unfold Fintype.mPi
  generalize Fintype.equivFin ι = e
  have hn : Fintype.card ι = 1 := Fintype.card_unique
  revert e
  rw [hn]
  intro e
  simp only [Fin.mOfFn, map_bind, map_pure]
  rw [show e.symm 0 = default from Subsingleton.elim _ _, map_eq_bind_pure_comp]
  refine bind_congr fun a => ?_
  rw [pure_bind]
  congr 1
  funext i
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply, Equiv.symm_symm]
  rw [show e i = 0 from Subsingleton.elim _ _]
  rfl

namespace Rewinding

variable {C W : Type} {m : Type → Type} [Monad m]

/-- **One block step.** Run the child at the centre `c₀`. If it fails, the step fails. Otherwise,
for every coordinate `j`, collect `k j - 1` successful children without replacement from the pool
`pools j`, and return the centre's result with the collected results if every coordinate supplied
them. -/
@[expose] noncomputable def blockChildren {ι : Type} [Fintype ι]
    (sample : (n : ℕ) → m (Fin (n + 1))) (child : C → m (Option W)) (k : ι → ℕ) (c₀ : C)
    (pools : ι → List C) : m (Option (W × (ι → List W))) :=
  child c₀ >>= fun w =>
    match w with
    | none => pure none
    | some w₀ =>
        Fintype.mPi (fun j => collectChildren sample child (k j - 1) (pools j)) >>= fun ws =>
          pure (if ∀ j, (ws j).length = k j - 1 then some (w₀, ws) else none)

/-- **One coordinate is the threshold step.** A threshold attempt on a nonempty pool draws its
first child and then runs the block step with one coordinate, centred at that child, on the rest of
the pool. -/
theorem thresholdChildren_eq_blockChildren [LawfulMonad m] (sample : (n : ℕ) → m (Fin (n + 1)))
    (child : C → m (Option W)) (r : ℕ) (c : C) (cs : List C) :
    thresholdChildren sample child (r + 1) (c :: cs) = (do
      let i ← sample cs.length
      let z ← blockChildren (ι := Fin 1) sample child (fun _ => r + 1)
        ((c :: cs)[(i : ℕ)]'(by simpa using i.isLt)) (fun _ => (c :: cs).eraseIdx i)
      pure (z.map fun p => p.1 :: p.2 0)) := by
  simp only [thresholdChildren, blockChildren, bind_assoc]
  refine bind_congr fun i => ?_
  refine bind_congr fun w => ?_
  cases w with
  | none => simp
  | some w =>
      simp only [Fintype.mPi_unique, bind_map_left, bind_assoc, pure_bind, Nat.add_sub_cancel,
        Unique.forall_iff]
      refine bind_congr fun ws => ?_
      split_ifs <;> rfl

end Rewinding
