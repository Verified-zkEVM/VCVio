/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.ProgramLogic.Tactics.Relational
import VCVio.ProgramLogic.Tactics.PrVCGen

/-!
# Information-Theoretic Private Information Retrieval (PIR)

This file defines a simple 2-server PIR protocol and proves:
1. **Correctness**: the protocol always returns the correct database entry `a[i₀]`.
2. **Privacy**: the distribution of each query set is independent of the queried index.

## Protocol

The user wants to retrieve `a[i₀]` from a database `a : Fin N → W` without
revealing `i₀` to either server. The "word type" `W` must be an additive group
where `x + x = 0` for all `x` (i.e., addition is XOR / characteristic 2).

**Query generation** (via `foldlM` over `List.finRange N`):
- For each index `j`:
  - If `j = i₀`: flip a coin; add `j` to `s` (heads) or `s'` (tails).
  - If `j ≠ i₀`: flip a coin; add `j` to both `s` and `s'` (heads) or neither (tails).

**Response**: server 1 computes `⊕_{j ∈ s} a[j]`, server 2 computes `⊕_{j ∈ s'} a[j]`.
**Reconstruction**: the user XORs (adds) the two responses to recover `a[i₀]`.

**Privacy**: for any `j`, the probability of `j ∈ s` is exactly `1/2`,
regardless of `i₀`. So the distribution of `s` alone reveals nothing about `i₀`.

## References

Port of EasyCrypt's `PIR.ec`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

/-! ## Query generation -/

variable {N : ℕ}

/-- Imperative-style PIR query generation using `for` / `let mut` syntax. -/
def pirQuery' (i₀ : Fin N) : ProbComp (List (Fin N) × List (Fin N)) := do
  let mut s  : List (Fin N) := []
  let mut s' : List (Fin N) := []
  for j in List.finRange N do
    let b ← $ᵗ Bool
    if j = i₀ then
      if b then s := j :: s else s' := j :: s'
    else
      if b then
        s := j :: s
        s' := j :: s'
  return (s, s')

/-- PIR query generation: build two index sets `s, s'` whose "symmetric difference"
is `{i₀}`. Uses `foldlM` over `List.finRange N` with a random coin per index. -/
def pirQuery (i₀ : Fin N) : ProbComp (List (Fin N) × List (Fin N)) :=
  (List.finRange N).foldlM (fun (acc : List (Fin N) × List (Fin N)) (j : Fin N) => do
    let b ← $ᵗ Bool
    if j = i₀ then
      return if b then (j :: acc.1, acc.2) else (acc.1, j :: acc.2)
    else
      return if b then (j :: acc.1, j :: acc.2) else acc
  ) ([], [])

/-- The imperative-style `pirQuery'` (using `for`/`let mut`) and the functional-style
`pirQuery` (using `List.foldlM`) compute exactly the same oracle computation.

Uses Lean's `List.forIn_yield_eq_foldlM` bridge to convert the `for`/`let mut`
desugaring (which uses `forIn` with product state and `ForInStep.yield`) into the
direct `foldlM` formulation. The local `ite` lemmas normalize the elaborator's
branchwise `pure`/`yield` terms to the form expected by that bridge. -/
theorem pirQuery'_eq_pirQuery (i₀ : Fin N) : pirQuery' i₀ = pirQuery i₀ := by
  simp only [pirQuery', pirQuery, monad_norm, Prod.eta, bind_pure]
  have ite_pure {α : Type} (p : Prop) [Decidable p] (x y : α) :
      (if p then pure x else pure y : ProbComp α) = pure (if p then x else y) := by
    split <;> rfl
  have ite_yield {α : Type} (p : Prop) [Decidable p] (x y : α) :
      (if p then ForInStep.yield x else .yield y) = .yield (if p then x else y) := by
    split <;> rfl
  simp only [ite_pure, ite_yield]
  simpa only [map_eq_pure_bind] using
    (List.forIn_yield_eq_foldlM
      (l := List.finRange N)
      (f := fun _ _ => ($ᵗ Bool))
      (g := fun j acc b =>
        if j = i₀ then
          if b then (j :: acc.1, acc.2) else (acc.1, j :: acc.2)
        else if b then (j :: acc.1, j :: acc.2) else acc)
      (init := ([], [])))

/-! ## Response computation and main protocol -/

variable {W : Type} [AddCommGroup W]

/-- Compute the XOR (additive sum) of database entries at the given indices.
Uses `+` as the group operation; for correctness we will need `x + x = 0`. -/
def pirResponse (a : Fin N → W) (s : List (Fin N)) : W :=
  s.foldl (fun acc j => acc + a j) 0

/-- Full PIR protocol: generate queries, compute responses, XOR (add) them. -/
def pirMain (a : Fin N → W) (i₀ : Fin N) : ProbComp W := do
  let (s, s') ← pirQuery i₀
  return (pirResponse a s + pirResponse a s')

/-! ## Correctness -/

private lemma foldl_add_shift {β : Type*} (g : β → W) (c : W) (l : List β) :
    l.foldl (fun acc x => acc + g x) c = c + l.foldl (fun acc x => acc + g x) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons x t ih => simp only [List.foldl_cons]; rw [ih, ih (0 + g x), zero_add, add_assoc]

private lemma pirResponse_cons (a : Fin N → W) (j : Fin N) (s : List (Fin N)) :
    pirResponse a (j :: s) = a j + pirResponse a s := by
  simp only [pirResponse, List.foldl_cons, zero_add]; exact foldl_add_shift _ (a j) s

/-- Correctness: the PIR protocol always returns `a[i₀]`, assuming `W` has
characteristic 2 (i.e. `x + x = 0` for all `x`). This ensures that database
entries appearing in both query sets cancel out.

The proof uses a loop invariant: after processing index `j`, the XOR of entries
in `s` plus the XOR of entries in `s'` equals the sum of `a[k]` for all
`k ≤ j` in the symmetric difference of `s` and `s'`, which is `{i₀} ∩ {0..j}`. -/
theorem pir_correct (hchar : ∀ x : W, x + x = 0)
    (a : Fin N → W) (i₀ : Fin N) :
    Pr{let y ← pirMain a i₀}[y = a i₀] = 1 := by
  prvcgen [pirMain, pirQuery] invariants
  · fun pref _ acc => pirResponse a acc.1 + pirResponse a acc.2 = if i₀ ∈ pref then a i₀ else 0
  case vc1 => simp [pirResponse]
  case vc2 => rename_i h; simpa using h
  case vc3 =>
    rename_i pref cur suff hxs s s' hinv hcur
    subst hcur
    have hnot : cur ∉ pref := fun h =>
      (List.nodup_append.mp (hxs ▸ List.nodup_finRange N)).2.2 _ h _ List.mem_cons_self rfl
    cases b <;> simp only [hnot, ↓reduceIte, Bool.false_eq_true, pirResponse_cons,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_true] at hinv ⊢
    · rw [add_left_comm, hinv, add_zero]
    · rw [add_assoc, hinv, add_zero]
  case vc4 =>
    rename_i pref cur suff hxs s s' hinv hcur
    cases b
    · simpa [Ne.symm hcur] using hinv
    · simp only [pirResponse_cons, List.mem_append, List.mem_singleton, Ne.symm hcur, or_false,
        ↓reduceIte] at hinv ⊢
      rw [← hinv]
      calc _ = (a cur + a cur) + (pirResponse a s + pirResponse a s') := by abel
        _ = _ := by rw [hchar, zero_add]

/-- Privacy of the first server view: the distribution of the first query set `s`
is independent of which index is being queried. Intuitively, each index `j` appears in `s` with
probability 1/2 regardless of whether `j = i₀` or not:
- If `j = i₀`: `j ∈ s` iff coin is heads (prob 1/2)
- If `j ≠ i₀`: `j ∈ s` iff coin is heads (prob 1/2)

This is one half of the information-theoretic privacy guarantee; the second
server view is handled by `pir_private_snd`. -/
theorem pir_private (i₁ i₂ : Fin N) :
    Prod.fst <$> pirQuery i₁ =ᵈ Prod.fst <$> pirQuery i₂ := by
  simp only [pirQuery]
  by_equiv
  rvcstep -- handle map
  rvcstep -- handle foldlM
  · rfl -- initial states: ([], []).1 = ([], []).1
  · intro j acc₁ acc₂ hS
    simp only [ProgramLogic.Relational.EqRel] at hS
    rvcstep using (fun b : Bool => b)
    · simp only [ProgramLogic.Relational.relTriple_iff_relWP,
        ProgramLogic.Relational.relWP_iff_couplingPost]
      split <;> split <;> split <;>
        apply ProgramLogic.Relational.relTriple_pure_pure <;>
        simp [ProgramLogic.Relational.EqRel, hS]
    · exact Function.bijective_id

/-- Privacy of the second server view: the distribution of the second query set `s'`
is independent of which index is being queried. Intuitively, each index `j` appears in `s'` with
probability 1/2 regardless of whether `j = i₀` or not:
- If `j = i₀`: `j ∈ s'` iff coin is tails (prob 1/2)
- If `j ≠ i₀`: `j ∈ s'` iff coin is heads (prob 1/2)

This is the other half of the information-theoretic privacy guarantee (see `pir_private`).
The proof uses a coupling argument with four cases depending on whether `j` equals `i₁`, `i₂`,
both, or neither. When `j` equals exactly one of them, the coupling negates the coin (`b ↦ !b`),
exploiting the symmetry of the uniform distribution on `Bool`. -/
theorem pir_private_snd (i₁ i₂ : Fin N) :
    Prod.snd <$> pirQuery i₁ =ᵈ Prod.snd <$> pirQuery i₂ := by
  simp only [pirQuery]
  by_equiv
  rvcstep -- handle map
  rvcstep -- handle foldlM
  · rfl
  · intro j acc₁ acc₂ hS
    simp only [ProgramLogic.Relational.EqRel] at hS
    by_cases h₁ : j = i₁ <;> by_cases h₂ : j = i₂
    -- Case 1: j = i₁ ∧ j = i₂ — identical, identity coupling
    · subst h₁; subst h₂
      rvcstep using (fun b : Bool => b)
      · simp [ProgramLogic.Relational.EqRel, hS]
        split <;> rfl
      · exact Function.bijective_id
    -- Case 2: j = i₁ ∧ j ≠ i₂ — negation coupling
    · subst h₁
      rvcstep using (fun b : Bool => !b)
      · simp [h₂]
        split_ifs <;> simp [ProgramLogic.Relational.EqRel, hS] at * <;>
          cases ‹Bool› <;> simp at *
      · exact Bool.involutive_not.bijective
    -- Case 3: j ≠ i₁ ∧ j = i₂ — negation coupling
    · subst h₂
      rvcstep using (fun b : Bool => !b)
      · simp [h₁]
        split_ifs <;> simp [ProgramLogic.Relational.EqRel, hS] at * <;>
          cases ‹Bool› <;> simp at *
      · exact Bool.involutive_not.bijective
    -- Case 4: j ≠ i₁ ∧ j ≠ i₂ — identity coupling
    · rvcstep using (fun b : Bool => b)
      · simp [h₁, h₂]
        split_ifs <;> simp [ProgramLogic.Relational.EqRel, hS] at *
      · exact Function.bijective_id
