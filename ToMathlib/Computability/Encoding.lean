/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Computability.Encoding
public import Mathlib.Data.FinEnum

/-!
# Additional Encoding Combinators

This file extends `Mathlib.Computability.Encoding` with combinators needed to feed
structured values to Turing machines:

- `Computability.finEncodingOfFinEnum`: a `FinEncoding` of any `FinEnum` type (unary
  over a `Unit` alphabet), making the common finite cases — `Unit`, `Bool`, `Fin n`,
  products, sums, sigmas — encodable for free.
- `Computability.finEncodingOption`: a `FinEncoding` of `Option β` from one of `β`.
- `Computability.finEncodingSigma`: a `FinEncoding` of a dependent pair `(t : ι) × F t`
  from an encoding of the index and per-index encodings over a shared fiber alphabet.
- `Computability.FinEncoding.boolify`: relabel any finite-alphabet encoding into
  `List Bool` via fixed-width one-hot symbol codes, so that encodings over different
  alphabets can serve as inputs and outputs of machines over a single alphabet.
- `Computability.finEncodingBitVec`: the fixed-width binary encoding of `BitVec w`,
  linear in `w` where the unary `finEncodingOfFinEnum` would be exponential, together
  with length lemmas for it and for pair and option encodings.

These mirror the design of `Computability.finEncodingPair`.
-/

@[expose] public section

universe u v

namespace List

/-- A `flatMap` by an injective fixed-width block code is injective. -/
theorem flatMap_injective {α : Type u} {β : Type v} {f : α → List β} {w : ℕ} (hw : 0 < w)
    (hlen : ∀ a, (f a).length = w) (hinj : Function.Injective f) :
    Function.Injective fun l : List α => l.flatMap f := by
  intro l₁ l₂ h
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t =>
      simp only [flatMap_nil, flatMap_cons] at h
      have := congrArg length h
      simp [hlen b] at this
      omega
  | cons a t ih =>
    cases l₂ with
    | nil =>
      simp only [flatMap_cons, flatMap_nil] at h
      have := congrArg length h
      simp [hlen a] at this
      omega
    | cons b t' =>
      simp only [flatMap_cons] at h
      obtain ⟨hfab, htail⟩ := append_inj h ((hlen a).trans (hlen b).symm)
      rw [hinj hfab, ih htail]

end List

namespace Computability

/-! ## Encodings of Enumerable Finite Types -/

/-- A `FinEncoding` of any `FinEnum` type: unary encoding over the `Unit` alphabet,
with string length the enumeration index. Gives encodings of the common finite types
(`Unit`, `Bool`, `Fin n`, products, sums, sigmas of such) for free. -/
def finEncodingOfFinEnum (α : Type u) [FinEnum α] : FinEncoding α where
  Γ := Unit
  encode x := List.replicate (FinEnum.equiv x : ℕ) ()
  decode l :=
    if h : l.length < FinEnum.card α then some (FinEnum.equiv.symm ⟨l.length, h⟩) else none
  decode_encode x := by simp
  ΓFin := inferInstance

/-! ## Option and Sigma Encodings -/

/-- A `FinEncoding` of `Option β`: `none` is the empty string, `some b` is a marker
symbol followed by the relabeled encoding of `b`. -/
def finEncodingOption {β : Type u} (eb : FinEncoding β) : FinEncoding (Option β) where
  Γ := Unit ⊕ eb.Γ
  encode
    | none => []
    | some b => .inl () :: (eb.encode b).map .inr
  decode
    | [] => some none
    | .inl _ :: l => (eb.decode (l.filterMap Sum.getRight?)).map some
    | .inr _ :: _ => none
  decode_encode x := by cases x <;> simp
  ΓFin := inferInstance

/-- Sigma analogue of `finEncodingPair`: encode the index with `.inl` symbols and the
fiber value with `.inr` symbols. The fiber encodings share a single alphabet `Γ`
(per-index alphabets could not form one machine alphabet); they are given as raw
encode/decode functions with a round-trip proof rather than per-index
`FinEncoding`s for the same reason. -/
def finEncodingSigma {ι : Type u} (ei : FinEncoding ι) {F : ι → Type v} {Γ : Type}
    [Fintype Γ] (enc : (t : ι) → F t → List Γ) (dec : (t : ι) → List Γ → Option (F t))
    (henc : ∀ t x, dec t (enc t x) = some x) : FinEncoding ((t : ι) × F t) where
  Γ := ei.Γ ⊕ Γ
  encode x := (ei.encode x.1).map .inl ++ (enc x.1 x.2).map .inr
  decode l := (ei.decode (l.filterMap Sum.getLeft?)).bind
    fun t => (dec t (l.filterMap Sum.getRight?)).map (⟨t, ·⟩)
  decode_encode x := by
    obtain ⟨t, y⟩ := x
    simp [henc]
  ΓFin := inferInstance

/-! ## Relabeling into a Boolean Alphabet -/

namespace FinEncoding

variable {α : Type u} (e : FinEncoding α)

/-- The fixed-width one-hot code of a single alphabet symbol: a `Bool` string of length
`Fintype.card e.Γ + 1` that is `true` exactly at the symbol's index. The `+ 1` keeps the
width positive even for an empty alphabet. -/
noncomputable def symbolCode (g : e.Γ) : List Bool :=
  (List.range (Fintype.card e.Γ + 1)).map fun i => decide (i = (Fintype.equivFin e.Γ g : ℕ))

@[simp] theorem length_symbolCode (g : e.Γ) :
    (e.symbolCode g).length = Fintype.card e.Γ + 1 := by
  simp [symbolCode]

theorem symbolCode_injective : Function.Injective e.symbolCode := by
  intro g₁ g₂ h
  have hlt : ((Fintype.equivFin e.Γ) g₁ : ℕ) ∈ List.range (Fintype.card e.Γ + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_lt (Fintype.equivFin e.Γ g₁).isLt)
  have := (List.map_inj_left.mp h) _ hlt
  simp only [decide_eq_decide, true_iff] at this
  exact (Fintype.equivFin e.Γ).injective (Fin.val_injective (this ▸ rfl))

/-- Relabel a finite-alphabet encoding into `List Bool` by replacing each symbol with
its fixed-width one-hot code. Machines over the single alphabet `Bool` can then
consume and produce values of any `FinEncoding`-encodable type. -/
noncomputable def boolify : α → List Bool :=
  fun x => (e.encode x).flatMap e.symbolCode

theorem boolify_injective : Function.Injective e.boolify :=
  (List.flatMap_injective (Nat.succ_pos _) e.length_symbolCode e.symbolCode_injective).comp
    e.toEncoding.encode_injective

@[simp] theorem length_boolify (x : α) :
    (e.boolify x).length = (Fintype.card e.Γ + 1) * (e.encode x).length := by
  simp only [boolify, List.length_flatMap]
  simp [Nat.mul_comm]

end FinEncoding

/-- The boolified unary `FinEnum` encoding has length at most `2 * card`: the unary
string has length the enumeration index (below `card`), and the one-hot symbol width
over the `Unit` alphabet is `2`. This is the pointwise bound feeding
`Computability.EncPolyTime.time_ofFintype_eval_le` at `FinEnum` encodings. -/
theorem length_boolify_finEncodingOfFinEnum {γ : Type u} [FinEnum γ] [Fintype γ] (x : γ) :
    ((finEncodingOfFinEnum γ).boolify x).length ≤ 2 * Fintype.card γ := by
  have hx : (FinEnum.equiv x : ℕ) < Fintype.card γ :=
    FinEnum.card_eq_fintypeCard (α := γ) ▸ (FinEnum.equiv x).isLt
  rw [FinEncoding.length_boolify]
  simp only [finEncodingOfFinEnum, List.length_replicate, Fintype.card_unique]
  omega

/-! ## Binary Bitvector Encoding -/

/-- Fixed-width binary encoding of `BitVec w` over the `Bool` alphabet: the string of the
`w` bits, least significant first. The encoded length is `w`, linear where the unary
`finEncodingOfFinEnum` encoding would have length up to `2 ^ w`; machine states containing
bitvectors need this encoding for polynomial size bounds. -/
def finEncodingBitVec (w : ℕ) : FinEncoding (BitVec w) where
  Γ := Bool
  encode m := (List.range w).map m.getLsbD
  decode l := if h : l.length = w then some (BitVec.cast h (BitVec.ofBoolListLE l)) else none
  decode_encode m := by
    have hlen : ((List.range w).map m.getLsbD).length = w := by simp
    rw [dif_pos hlen]
    refine congrArg some (BitVec.eq_of_getLsbD_eq_iff.mpr fun i hi => ?_)
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
    simp [List.getD_eq_getElem?_getD, hi]
  ΓFin := inferInstance

@[simp] theorem length_encode_finEncodingBitVec {w : ℕ} (m : BitVec w) :
    ((finEncodingBitVec w).encode m).length = w := by
  simp [finEncodingBitVec]

/-- The boolified binary bitvector encoding has length exactly `3 * w`: `w` symbols of
one-hot width `card Bool + 1`. The pointwise bound feeding
`Computability.EncPolyTime.time_ofFintype_eval_le` at bitvector-shaped machine states. -/
theorem length_boolify_finEncodingBitVec {w : ℕ} (m : BitVec w) :
    ((finEncodingBitVec w).boolify m).length = 3 * w := by
  rw [FinEncoding.length_boolify, length_encode_finEncodingBitVec]
  change (Fintype.card Bool + 1) * w = 3 * w
  rw [Fintype.card_bool]

/-! ## Encoding Lengths of Pairs and Options -/

theorem length_encode_finEncodingPair {α : Type u} {β : Type v} (ea : FinEncoding α)
    (eb : FinEncoding β) (x : α × β) :
    ((finEncodingPair ea eb).encode x).length =
      (ea.encode x.1).length + (eb.encode x.2).length := by
  simp [finEncodingPair]

@[simp] theorem length_encode_finEncodingOption_none {β : Type u} (eb : FinEncoding β) :
    ((finEncodingOption eb).encode (none : Option β)).length = 0 := rfl

theorem length_encode_finEncodingOption_some {β : Type u} (eb : FinEncoding β) (b : β) :
    ((finEncodingOption eb).encode (some b)).length = (eb.encode b).length + 1 := by
  simp [finEncodingOption]

/-- The boolified pair encoding has length `(card Γ₁ + card Γ₂ + 1)` times the sum of the two
component encode-lengths: the one-hot symbol width over the combined alphabet `Γ₁ ⊕ Γ₂` times
the concatenated encoding length. The pointwise bound for paired machine states (e.g. a counter
paired with an accumulator). -/
theorem length_boolify_finEncodingPair {α : Type u} {β : Type v} (ea : FinEncoding α)
    (eb : FinEncoding β) (x : α × β) :
    ((finEncodingPair ea eb).boolify x).length
      = (Fintype.card ea.Γ + Fintype.card eb.Γ + 1)
          * ((ea.encode x.1).length + (eb.encode x.2).length) := by
  have hc : Fintype.card (finEncodingPair ea eb).Γ = Fintype.card ea.Γ + Fintype.card eb.Γ :=
    Fintype.card_sum
  rw [FinEncoding.length_boolify, length_encode_finEncodingPair, hc]

/-- The boolified option encoding has length `(card Γ + 2)` times the option encode-length: the
`Unit ⊕ Γ` alphabet has one more symbol than `Γ`, so the one-hot width is `card Γ + 2`. The
pointwise bound for optional machine outputs. -/
theorem length_boolify_finEncodingOption {β : Type v} (eb : FinEncoding β) (x : Option β) :
    ((finEncodingOption eb).boolify x).length
      = (Fintype.card eb.Γ + 2) * ((finEncodingOption eb).encode x).length := by
  have hc : Fintype.card (finEncodingOption eb).Γ = Fintype.card eb.Γ + 1 :=
    (Fintype.card_sum (α := Unit) (β := eb.Γ)).trans (by rw [Fintype.card_unit, Nat.add_comm])
  rw [FinEncoding.length_boolify, hc]

end Computability
