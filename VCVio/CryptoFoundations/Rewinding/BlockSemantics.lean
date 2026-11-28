/-
Copyright (c) 2026 aryaethn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import VCVio.CryptoFoundations.Rewinding.BlockRound
import VCVio.CryptoFoundations.Rewinding.ThresholdSemantics
import VCVio.EvalDist.IndepProduct

/-!
# Semantics of the block step

`Rewinding.blockChildren` commutes with monad morphisms (`Rewinding.map_blockChildren`), through the
same fact for `Fin.mOfFn` and `Fintype.mPi` (`MonadHom.mmap_mOfFn`, `MonadHom.mmap_mPi`). In an
oracle computation, a successful block step ran its child at the centre successfully and returned,
at every coordinate, an output of that coordinate's collector with `k j - 1` entries
(`Rewinding.mem_support_blockChildren`); the counter form is
`Rewinding.length_of_mem_support_blockChildren_run`. These are what a recursion over rounds needs
from one round.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

/-- The block step commutes with monad morphisms. -/
theorem map_blockChildren {m n : Type → Type} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (φ : m →ᵐ n) {ι : Type} [Fintype ι] {C W : Type}
    (sample : (j : ℕ) → m (Fin (j + 1))) (child : C → m (Option W)) (k : ι → ℕ) (c₀ : C)
    (pools : ι → List C) :
    φ (blockChildren sample child k c₀ pools) =
      blockChildren (fun j => φ (sample j)) (fun c => φ (child c)) k c₀ pools := by
  simp only [blockChildren, φ.mmap_bind]
  congr 1
  funext w
  cases w with
  | none => exact φ.mmap_pure _
  | some w₀ =>
      simp only [φ.mmap_bind, φ.mmap_pure, MonadHom.mmap_mPi]
      congr 2
      funext j
      exact map_collectChildren φ sample child _ _ _ rfl

/-- A successful block step in an oracle computation: the centre's child succeeded, and every
coordinate's results are an output of its collector with `k j - 1` entries. -/
theorem mem_support_blockChildren {ιs : Type} {spec : OracleSpec ιs} {ι : Type} [Fintype ι]
    {C W : Type} (sample : (j : ℕ) → OracleComp spec (Fin (j + 1)))
    (child : C → OracleComp spec (Option W)) (k : ι → ℕ) (c₀ : C) (pools : ι → List C)
    (w₀ : W) (ws : ι → List W)
    (h : some (w₀, ws) ∈ support (blockChildren sample child k c₀ pools)) :
    some w₀ ∈ support (child c₀) ∧
      ∀ j, ws j ∈ support (collectChildren sample child (k j - 1) (pools j)) ∧
        (ws j).length = k j - 1 := by
  simp only [blockChildren, mem_support_bind_iff] at h
  obtain ⟨v, hv, h⟩ := h
  cases v with
  | none => simp at h
  | some v₀ =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
      obtain ⟨u, hu, h⟩ := h
      split at h
      · rename_i hlen
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hv, fun j => ⟨mem_support_mPi _ _ hu j, hlen j⟩⟩
      · simp at h

/-- A successful block step returns exactly `k j - 1` results at every coordinate. -/
theorem length_of_mem_support_blockChildren_run {ι : Type} [Fintype ι] {C W : Type}
    (sample : (j : ℕ) → ProbComp (Fin (j + 1))) (child : C → StateT ℕ ProbComp (Option W))
    (k : ι → ℕ) (c₀ : C) (pools : ι → List C) (count : ℕ)
    (z : Option (W × (ι → List W)) × ℕ)
    (hz : z ∈ support ((blockChildren (fun j => StateT.lift (sample j)) child k c₀ pools).run
      count))
    (w : W × (ι → List W)) (hw : z.1 = some w) : ∀ j, (w.2 j).length = k j - 1 := by
  simp only [blockChildren, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨v, -, hz⟩ := hz
  cases hv : v.1 with
  | none =>
      simp only [hv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simp at hw
  | some w₀ =>
      simp only [hv, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      dsimp only at hw
      split at hw
      · rename_i h
        simp only [Option.some.injEq] at hw
        subst hw
        exact h
      · simp at hw

end Rewinding
