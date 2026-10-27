/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Tuples

/-!
# Multi-extractors and admissibility

A multi-extractor for a family of `k` vector commitments (Chiesa, Di, Hu and Zheng,
ePrint 2025/2166, §7, p. 49) is a deterministic classical map that takes a commitment tuple
`((idx_i, cm_i))_{i ∈ [j]}` and a classical state `S` of an emulated oracle's private register, and
returns a decommitment tuple of the same length.

## Admissibility, and why Def 7.1 is repaired

Def 7.1 (p. 49) calls a multi-extractor admissible when

1. a tuple with a repeated index extracts to all `⊥`, and
2. extraction is prefix consistent: the extraction of a prefix is the prefix of the extraction.

Taken literally, the two properties force every position `i` with `i + 1 < k` of every tuple to
extract to `⊥`. Extend the length-`(i + 1)` prefix by repeating `idx_i`: property 1 makes that
extension all `⊥`, and property 2 carries the `⊥` back to the prefix and then to the original tuple
(`Quantum.MultiExtractor.AdmissibleLiteral.extract_eq_bot`). Hence every tuple shorter than `k`
extracts to all `⊥`, and so does every full tuple with a repeated index (property 1). On a full
tuple with distinct indices, every position but the last, `k - 1`, extracts to `⊥`; the last
position is left unconstrained, so the literal definition still admits multi-extractors that are
non-trivial there (for `k = 2`, one returning `(⊥, v)` on full distinct-index tuples). In
particular, for `k ≥ 2` the Merkle multi-extractor of §8.3, which extracts at every position of a
shorter tuple, does not satisfy it.

`Quantum.MultiExtractor.Admissible` requires prefix consistency only for tuples with distinct
indices. The literal definition is kept as `Quantum.MultiExtractor.AdmissibleLiteral` so that its
degeneracy is stated and checked.

The definitions are classical; the purified extractor `U_MultiExtract` (p. 49) is built on
top of them.

## Main definitions

* `Quantum.MultiExtractor k Cm Dm S`.
* `Quantum.MultiExtractor.Admissible`: Def 7.1, with prefix consistency on distinct-index tuples.
* `Quantum.MultiExtractor.AdmissibleLiteral`: Def 7.1 as written.

## Main results

* `Quantum.MultiExtractor.AdmissibleLiteral.extract_eq_bot`: the literal Def 7.1 forces `⊥` at
  every position `i` with `i + 1 < k`.
-/

public section

universe u v w

namespace Quantum

/-- A multi-extractor (ePrint 2025/2166, §7, p. 49): a deterministic classical map from a
commitment tuple and a basis state `s : S` of the oracle's private register to a decommitment tuple
of the same length. The length is preserved by the type. "Polynomial time" (p. 49) is not part
of the definition; `extract` is any function. -/
structure MultiExtractor (k : ℕ) (Cm : Type u) (Dm : Fin k → Type v) (S : Type w) where
  /-- `MultiExtract(tic, S)`. -/
  extract : (tic : TpIC k Cm) → S → TpDLen k Dm tic.1

namespace MultiExtractor

variable {k : ℕ} {Cm : Type u} {Dm : Fin k → Type v} {S : Type w}

/-- Admissibility (ePrint 2025/2166, Def 7.1, p. 49), with prefix consistency required only
for tuples with distinct indices; see the module docstring for why the literal definition is
repaired. `bot i` is the all-`⊥` decommitment of the scheme `VC_i`. -/
structure Admissible (ME : MultiExtractor k Cm Dm S) (bot : ∀ i, Dm i) : Prop where
  /-- Property 1 (p. 49): a tuple with a repeated index extracts to all `⊥`. -/
  eq_bot_of_not_injective : ∀ (tic : TpIC k Cm) (s : S), ¬ Function.Injective tic.idx →
    ∀ i, ME.extract tic s i = bot _
  /-- Property 2 (p. 49), for tuples with distinct indices: the extraction of a prefix is
  the prefix of the extraction. -/
  prefix_eq : ∀ (tic : TpIC k Cm) (s : S), Function.Injective tic.idx →
    ∀ (j' : TupleLen k) (h : j'.len ≤ tic.1.len) (i : Fin j'.len),
      ME.extract (tic.prefix j' h) s i = ME.extract tic s (Fin.castLE h i)

/-- Def 7.1 (p. 49) as written, with prefix consistency for every tuple. It is degenerate
(`Quantum.MultiExtractor.AdmissibleLiteral.extract_eq_bot`). -/
structure AdmissibleLiteral (ME : MultiExtractor k Cm Dm S) (bot : ∀ i, Dm i) : Prop where
  /-- Property 1 (p. 49): a tuple with a repeated index extracts to all `⊥`. -/
  eq_bot_of_not_injective : ∀ (tic : TpIC k Cm) (s : S), ¬ Function.Injective tic.idx →
    ∀ i, ME.extract tic s i = bot _
  /-- Property 2 (p. 49), for every tuple. -/
  prefix_eq : ∀ (tic : TpIC k Cm) (s : S) (j' : TupleLen k) (h : j'.len ≤ tic.1.len)
    (i : Fin j'.len), ME.extract (tic.prefix j' h) s i = ME.extract tic s (Fin.castLE h i)

/-- The literal definition implies the repaired one. -/
theorem AdmissibleLiteral.admissible {ME : MultiExtractor k Cm Dm S} {bot : ∀ i, Dm i}
    (h : ME.AdmissibleLiteral bot) : ME.Admissible bot :=
  ⟨h.eq_bot_of_not_injective, fun tic s _ ↦ h.prefix_eq tic s⟩

/-- **The literal Def 7.1 is degenerate.** Under it, every position `i` with `i + 1 < k` of every
tuple extracts to `⊥`:

* the prefix of length `i + 1`, extended by repeating its last entry, has a repeated index, so
  property 1 makes its extraction all `⊥`;
* property 2 carries this `⊥` to the prefix of length `i + 1`, and then to the original tuple.

So every position of a tuple shorter than `k`, and every position but the last of a full tuple,
extracts to `⊥`. The last position of a full tuple with distinct indices is not constrained. -/
theorem AdmissibleLiteral.extract_eq_bot {ME : MultiExtractor k Cm Dm S} {bot : ∀ i, Dm i}
    (h : ME.AdmissibleLiteral bot) (tic : TpIC k Cm) (s : S) (i : Fin tic.1.len)
    (hi : i.val + 1 < k) : ME.extract tic s i = bot _ := by
  have hlen := tic.1.len_le
  -- The prefix of length `i + 1`.
  let j₁ : TupleLen k := TupleLen.ofNat (i.val + 1) (Nat.succ_pos _) (by omega)
  have h₁ : j₁.len ≤ tic.1.len := by simp only [j₁, TupleLen.len_ofNat]; omega
  -- The prefix of length `i + 1`, extended by repeating entry `i`.
  let j₂ : TupleLen k := TupleLen.ofNat (i.val + 2) (Nat.succ_pos _) (by omega)
  let tic₂ : TpIC k Cm := ⟨j₂, fun t ↦ tic.2 ⟨min t.val i.val, by omega⟩⟩
  have h₂ : j₁.len ≤ tic₂.1.len := by simp [j₁, tic₂, j₂]
  have hnot : ¬ Function.Injective tic₂.idx := by
    intro hinj
    have := @hinj ⟨i.val, by simp [tic₂, j₂]⟩ ⟨i.val + 1, by simp [tic₂, j₂]⟩
      (by simp [TpIC.idx, tic₂])
    simp [Fin.ext_iff] at this
  have hF : (fun t : Fin j₁.len ↦ tic₂.2 (Fin.castLE h₂ t)) =
      fun t ↦ tic.2 (Fin.castLE h₁ t) := by
    funext t
    have : t.val < i.val + 1 := by simpa [j₁] using t.isLt
    refine congrArg tic.2 (Fin.ext ?_)
    simp only [Fin.val_castLE]
    omega
  let i₁ : Fin j₁.len := ⟨i.val, by simp [j₁]⟩
  have e₁ := h.prefix_eq tic s j₁ h₁ i₁
  have e₂ : ME.extract ⟨j₁, fun t ↦ tic₂.2 (Fin.castLE h₂ t)⟩ s i₁ =
      ME.extract tic₂ s (Fin.castLE h₂ i₁) :=
    h.prefix_eq tic₂ s j₁ h₂ i₁
  have e₃ := h.eq_bot_of_not_injective tic₂ s hnot (Fin.castLE h₂ i₁)
  rw [hF] at e₂
  have hi₁ : Fin.castLE h₁ i₁ = i := Fin.ext rfl
  rw [← hi₁, ← e₁]
  exact e₂.trans e₃

end MultiExtractor

end Quantum
