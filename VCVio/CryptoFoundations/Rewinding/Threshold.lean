/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Finder
public import VCVio.CryptoFoundations.Rewinding.ThresholdRound
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Recursive threshold challenge trees

The threshold finder processes rounds in the order of `Fin μ`. At each node it aborts if its
first child fails, and otherwise searches the remaining challenges without replacement for
enough successful children. Its oracle queries are complete challenge vectors.

The construction follows Attema, Cramer and Kohl, *A compressed Σ-protocol theory for lattices*
(CRYPTO 2021), Section 3.2.
-/

public section

open OracleComp OracleSpec

namespace Rewinding

namespace VecTree

/-- The challenge tree with no rounds has one empty challenge vector. -/
@[expose] def empty (C : Fin 0 → Type) (k : Fin 0 → ℕ) : VecTree C k where
  leaf _ r := Fin.elim0 r
  causal _ _ r := Fin.elim0 r

/-- Attach a family of tail trees to the challenges at the first round. -/
@[expose] def cons {n : ℕ} {C : Fin (n + 1) → Type} {k : Fin (n + 1) → ℕ}
    (children : Fin (k 0) → C 0 × VecTree (fun i : Fin n => C i.succ) (fun i : Fin n => k i.succ)) :
    VecTree C k where
  leaf p := Fin.cons (children (p 0)).1 ((children (p 0)).2.leaf (fun i => p i.succ))
  causal p p' r h := by
    have h₀ : p 0 = p' 0 := h 0 (Fin.zero_le r)
    cases r using Fin.cases with
    | zero => simp [h₀]
    | succ r =>
      simp only [Fin.cons_succ, h₀]
      apply VecTree.causal
      intro s hs
      exact h s.succ (Fin.succ_le_succ_iff.mpr hs)

/-- Distinct root challenges and structured children form a structured threshold tree. -/
theorem cons_isStructured {n : ℕ} {C : Fin (n + 1) → Type} {k : Fin (n + 1) → ℕ}
    (children : Fin (k 0) → C 0 × VecTree (fun i : Fin n => C i.succ) (fun i : Fin n => k i.succ))
    (hroot : Function.Injective fun j => (children j).1)
    (hchildren : ∀ j, (children j).2.IsStructured (fun _ ch => Function.Injective ch)) :
    (cons children).IsStructured (fun _ ch => Function.Injective ch) := by
  intro p r
  cases r using Fin.cases with
  | zero =>
    change Function.Injective (fun j => (children ((Function.update p 0 j) 0)).1)
    simpa only [Function.update_self] using hroot
  | succ r =>
    change Function.Injective (fun j =>
      (children ((Function.update p r.succ j) 0)).2.leaf
        (fun i => (Function.update p r.succ j) i.succ) r)
    simp only [Function.update_of_ne (Fin.succ_ne_zero r).symm]
    have ht := hchildren (p 0) (fun i => p i.succ) r
    change Function.Injective (fun j =>
      (children (p 0)).2.leaf (Function.update (fun i => p i.succ) r j) r) at ht
    simpa only [← Fin.tail_def, Fin.tail_update_succ] using ht

end VecTree

/-- Enumerate the operational support of a finite-range sampler, preserving repeated values. -/
@[expose] def samplerOutcomes {α : Type} (mx : ProbComp α) : List α :=
  OracleComp.construct (spec := unifSpec) (C := fun _ => List α) (fun a => [a])
    (fun _ _ rest => (List.ofFn rest).flatten) mx

/-- The sampler enumeration contains precisely the supported outcomes. -/
theorem mem_samplerOutcomes {α : Type} (mx : ProbComp α) (a : α) :
    a ∈ samplerOutcomes mx ↔ a ∈ support mx := by
  induction mx using OracleComp.inductionOn with
  | pure b => simp [samplerOutcomes]
  | query_bind n next ih =>
    simp only [samplerOutcomes, OracleComp.construct_query_bind, List.mem_flatten,
      List.mem_ofFn, exists_exists_eq_and]
    change (∃ i, a ∈ samplerOutcomes (next i)) ↔ _
    simp [ih]

/-- A duplicate-free executable challenge enumeration obtained from its uniform sampler. -/
@[expose] def challengePool (α : Type) [SampleableType α] [DecidableEq α] : List α :=
  (samplerOutcomes ($ᵗ α)).dedup

/-- Every challenge occurs in its sampler-derived enumeration. -/
theorem mem_challengePool {α : Type} [SampleableType α] [DecidableEq α] (a : α) :
    a ∈ challengePool α := by
  simp [challengePool, mem_samplerOutcomes]

/-- The sampler-derived challenge enumeration contains no duplicates. -/
theorem nodup_challengePool (α : Type) [SampleableType α] [DecidableEq α] :
    (challengePool α).Nodup := List.nodup_dedup _

/-- Assemble a root from a list containing exactly the requested number of children. -/
@[expose] def assembleChildren {n : ℕ} {C : Fin (n + 1) → Type}
    {k : Fin (n + 1) → ℕ}
    (children : List (C 0 × VecTree (fun i : Fin n => C i.succ) (fun i => k i.succ))) :
    Option (VecTree C k) :=
  if h : children.length = k 0 then
    some (VecTree.cons fun j => children[(j : ℕ)]'(by simpa only [h] using j.isLt))
  else none

/-- Recursive threshold extraction with a sampler, explicit challenge pools, and a Boolean
acceptance operation. It processes rounds in increasing `Fin` order and queries complete vectors.
-/
@[expose] def thresholdProgram {m : Type → Type} [Monad m]
    (sample : (j : ℕ) → m (Fin (j + 1))) :
    (n : ℕ) → (C : Fin n → Type) → (k : Fin n → ℕ) →
    ((i : Fin n) → List (C i)) → (((i : Fin n) → C i) → m Bool) →
    m (Option (VecTree C k))
  | 0, C, k, _, accept => do
      let b ← accept (fun i => Fin.elim0 i)
      pure (if b then some (VecTree.empty C k) else none)
  | n + 1, C, k, pools, accept => do
      let children ← thresholdChildren sample
        (fun c => do
          let t ← thresholdProgram sample n (fun i => C i.succ) (fun i => k i.succ)
            (fun i => pools i.succ) (fun q => accept (Fin.cons c q))
          pure (t.map (fun t => (c, t)))) (k 0) (pools 0)
      pure (children.bind assembleChildren)

/-- The black-box threshold finder with explicit finite challenge pools. -/
@[expose] def thresholdFinderWithPools (n : ℕ) (C : Fin n → Type) (k : Fin n → ℕ)
    (pools : (i : Fin n) → List (C i)) :
    OracleComp (unifSpec + accSpec C) (Option (VecTree C k)) :=
  thresholdProgram (m := OracleComp (unifSpec + accSpec C))
    (fun j => liftM (unifSpec.query j)) n C k pools (fun q => liftM ((accSpec C).query q))

/-- The computable ACK threshold finder on `Fin n`, using each challenge type's uniform
sampler to enumerate its finite support. The finder is independent of the acceptance function.
-/
@[expose] def thresholdFinder {n : ℕ} (C : Fin n → Type) [∀ i, SampleableType (C i)]
    [∀ i, DecidableEq (C i)] (k : Fin n → ℕ) :
    OracleComp (unifSpec + accSpec C) (Option (VecTree C k)) :=
  thresholdFinderWithPools n C k (fun i => challengePool (C i))

end Rewinding
