/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Sym
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Computable `FinEnum` constructions for `Bool`, `Sym`, `Equiv.Perm`, and embeddings

`FinEnum α` chooses an equivalence between `α` and `Fin (FinEnum.card α)`. The order
of `FinEnum.toList α` comes from that choice. The instance for `Bool` enumerates
`[true, false]`.

`Sym.finEnum`, `Equiv.Perm.finEnum`, and `Function.Embedding.finEnum` are named definitions.
For example, `letI : FinEnum (Equiv.Perm α) := Equiv.Perm.finEnum` lets a caller enumerate
permutations of a `FinEnum` type `α`. Installing the enumeration locally avoids adding a second
global way to synthesize the `Fintype` that Mathlib already supplies.

The multiset enumeration uses `List.sym`, with completeness given by `List.mem_sym`.
Permutations use `permsOfList`, and embeddings use the subtype of injective functions.
-/

@[expose] public section

universe u

/-- Completeness of `List.sym`: every `z : Sym α n` whose members all lie in `xs` is enumerated by
`xs.sym n`. This is the converse of `List.mem_of_mem_of_mem_sym`. -/
theorem List.mem_sym {α : Type u} :
    ∀ {n : ℕ} {xs : List α} {z : Sym α n}, (∀ a ∈ z, a ∈ xs) → z ∈ xs.sym n
  | 0, _, z, _ => by rw [Sym.eq_nil_of_card_zero z]; simp [List.sym]
  | n + 1, [], z, h => by
      obtain ⟨a, z', rfl⟩ := z.exists_eq_cons_of_succ
      exact absurd (h a (Sym.mem_cons_self a z')) (by simp)
  | n + 1, x :: xs, z, h => by
      classical
      rw [List.sym, List.mem_append]
      by_cases hx : x ∈ z
      · refine Or.inl (List.mem_map.mpr ⟨z.erase x hx, ?_, Sym.cons_erase hx⟩)
        exact List.mem_sym fun a ha =>
          h a (by rw [← Sym.cons_erase hx]; exact Sym.mem_cons.mpr (Or.inr ha))
      · refine Or.inr (List.mem_sym fun a ha => ?_)
        rcases List.mem_cons.mp (h a ha) with rfl | ha'
        · exact absurd ha hx
        · exact ha'

/-- `Bool` enumerated as `[true, false]`. -/
instance : FinEnum Bool := .ofList [true, false] (by decide)

/-- Computable enumeration of size-`n` multisets over a `FinEnum` type, drawn from `List.sym` of
the chosen enumeration. Every `z : Sym α n` qualifies since all its members lie in
`FinEnum.toList`. -/
@[reducible] def Sym.finEnum {α : Type u} [FinEnum α] (n : ℕ) : FinEnum (Sym α n) :=
  FinEnum.ofNodupList ((FinEnum.toList α).sym n)
    (fun _ => List.mem_sym fun a _ => FinEnum.mem_toList a)
    (List.Nodup.sym n FinEnum.nodup_toList)

/-- Computable enumeration of permutations of a `FinEnum` type via `permsOfList` applied to the
chosen enumeration. Completeness holds because every element a permutation can move lies in
`FinEnum.toList`. -/
@[reducible] def Equiv.Perm.finEnum {α : Type u} [FinEnum α] : FinEnum (Equiv.Perm α) :=
  FinEnum.ofNodupList (permsOfList (FinEnum.toList α))
    (fun _ => mem_permsOfList_of_mem fun x _ => FinEnum.mem_toList x)
    (nodup_permsOfList FinEnum.nodup_toList)

/-- Computable enumeration of embeddings `β ↪ α` between `FinEnum` types, transported from the
`FinEnum` on the subtype of injective functions `{f : β → α // Function.Injective f}`.
Enumerating the domain and comparing images using decidable equality on the codomain
decides injectivity. Mathlib's `Function.Embedding.fintype` is noncomputable. With this
enumeration, a sampler can compute the embedding at a given index. -/
@[reducible] def Function.Embedding.finEnum {β α : Type u} [FinEnum β] [FinEnum α] :
    FinEnum (β ↪ α) :=
  FinEnum.ofEquiv { f : β → α // Function.Injective f }
    (Equiv.subtypeInjectiveEquivEmbedding β α).symm
