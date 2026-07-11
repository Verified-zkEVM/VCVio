/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Computability.BitEncoding

/-!
# Base-Machine Combinators for Uniform Witness Families

**The machine frontier** of the polynomial-time adversary model: the raw-encoding base
combinators on `Computability.EncPolyTimeFam` that await a single-tape base-machine
library (streaming copy, shift, dispatch, and fixed-width bookkeeping machines in
Cslib's `Turing.SingleTapeTM` model). Every combinator is stated at the canonical raw
`List Bool` encodings of `ToMathlib.Computability.BitEncoding` — the encodings the
adversary layer (`MachineAdversary`) actually consumes — and each `sorry` is one
missing machine construction with routine tape bookkeeping, declared as a frontier
ticket so downstream composition can be written against the final interface. The
intended consumers are the Turing-machine halves of adversary sequential composition —
the `σ₁ ⊕ σ₂`-state `seqComp` machine and the fixed-prefix carry of a
`MachineAdversary` — feeding `OracleComp.IsPolyTime.bind`, whose semantic half
(`OracleMachine.Implements.seqComp`) is already proven.

The six frontier primitives:

* `EncPolyTimeFam.sumElim` (S1): tag dispatch over `StrEncFam.sum`.
* `EncPolyTimeFam.keep` (S2): compute-and-retain, result block first.
* `EncPolyTimeFam.takeFix` (S3): first projection of a fixed-left pair.
* `EncPolyTimeFam.dropFix` (S4): run after dropping a fixed-width prefix.
* `EncPolyTimeFam.underPrefix` (S5): run under a preserved fixed-width prefix.
* `EncPolyTimeFam.optionUnder` (S6): commute a fixed block into an option payload.

From these, the injection witnesses `EncPolyTimeFam.inlWit` / `EncPolyTimeFam.inrWit`
into the tag-bit sum encoding are *derived*: a `keep` of the constant tag block
`BitEncFam.tag` plus a pure `recode`, so they add no machine content of their own. The
constant tag witness `EncPolyTimeFam.tagWit` is fully proven from the constant machine
(`EncPolyTimeFam.const`); no seventh frontier primitive is needed.

## Sorry census

Exactly six sorries, one per frontier primitive (S1–S6). They supersede the two
`boolify`-typed sorries formerly declared in `ToMathlib.Computability.PolyTimeTM` (the
sum-dispatch transducer and its time bound), which were typed at one-hot
`FinEncoding.boolify` encodings unconsumable from the raw-encoding adversary layer.
Everything else in this file is proven.
-/

@[expose] public section

universe u

namespace Computability

/-! ## The single-bit tag block -/

namespace BitEncFam

/-- The single-bit tag block: a `PUnit` boundary of width `1` whose encoding is the
fixed bit `[b]` — the tag prefix of `StrEncFam.sum` (`false` for `inl`, `true` for
`inr`), as `BitEncFam.pad` is the all-zero payload block of `BitEncFam.option`. -/
noncomputable def tag (b : Bool) : BitEncFam (fun _ => PUnit.{u + 1}) where
  wid _ := 1
  widBound := .C 1
  wid_le _ := by simp
  enc _ _ := [b]
  len_eq _ _ := rfl
  enc_injective _ x y _ := by cases x; cases y; rfl

@[simp] theorem tag_enc (b : Bool) (n : ℕ) (x : PUnit) : (tag b).enc n x = [b] := rfl

end BitEncFam

namespace EncPolyTimeFam

variable {σ₁ σ₂ σ σ' τ : ℕ → Type u}

/-! ## The frontier: six declared base-machine tickets -/

/-- (S1) Tag dispatch: a single witness family over the tag-bit sum encoding
`StrEncFam.sum`, computing `Sum.elim f₁ f₂` from witnesses for the two branches.
Machine sketch: read the tag bit; on `false` erase it and run the left machine, on
`true` erase it and run the right machine — a branch on one input cell. Declared
base-machine frontier ticket. -/
noncomputable def sumElim {et : (n : ℕ) → τ n → List Bool}
    {f₁ : (n : ℕ) → σ₁ n → τ n} {f₂ : (n : ℕ) → σ₂ n → τ n}
    (s₁ : StrEncFam σ₁) (s₂ : StrEncFam σ₂)
    (h₁ : EncPolyTimeFam s₁.enc et f₁) (h₂ : EncPolyTimeFam s₂.enc et f₂) :
    EncPolyTimeFam (s₁.sum s₂).enc et (fun n => Sum.elim (f₁ n) (f₂ n)) := sorry

/-- (S2) Compute-and-retain: result block first, original input after. Machine sketch:
copy the input to the right, run the machine for `f` on the copy in place, and the
fixed result width makes the layout `e.enc (f x) ++ s.enc x`. Declared base-machine
frontier ticket. -/
noncomputable def keep {γ : ℕ → Type u} {f : (n : ℕ) → σ n → γ n}
    (s : StrEncFam σ) (e : BitEncFam γ) (h : EncPolyTimeFam s.enc e.enc f) :
    EncPolyTimeFam s.enc (e.pairFix s).enc (fun n x => (f n x, x)) := sorry

/-- (S3) First projection of a fixed-left pair: truncate to the fixed prefix width.
Machine sketch: keep the first `e.wid n` cells and erase the rest moving right — a
position counter of `e.wid n` (polynomially many) machine states. Declared
base-machine frontier ticket. -/
noncomputable def takeFix {γ : ℕ → Type u} (e : BitEncFam γ) (s : StrEncFam σ) :
    EncPolyTimeFam (e.pairFix s).enc e.enc (fun _ p => p.1) := sorry

/-- (S4) Run after dropping a fixed-width prefix: compute `f` on the second component
of a fixed-left pair. Machine sketch: erase the first `e.wid n` cells (a position
counter), then run the machine for `f` on the remaining tape. Derivable from `sumElim`
by width-fold bit peeling, but kept primitive: the uniform time/size bookkeeping of
the iterated derivation is worse than a direct machine. Declared base-machine frontier
ticket. -/
noncomputable def dropFix {γ : ℕ → Type u} {et : (n : ℕ) → τ n → List Bool}
    {f : (n : ℕ) → σ n → τ n} (e : BitEncFam γ) (s : StrEncFam σ)
    (h : EncPolyTimeFam s.enc et f) :
    EncPolyTimeFam (e.pairFix s).enc et (fun n p => f n p.2) := sorry

/-- (S5) Run under a preserved fixed-width prefix: transform the variable-width tail
while carrying the fixed block unchanged — the carry primitive for a machine
adversary's init/update steps under composition. Machine sketch: skip over the first
`e.wid n` cells (a position counter), run the machine for `f` on the tail, and leave
the prefix intact on the tape. Declared base-machine frontier ticket. -/
noncomputable def underPrefix {γ : ℕ → Type u} {f : (n : ℕ) → σ n → σ' n}
    (e : BitEncFam γ) (s : StrEncFam σ) (s' : StrEncFam σ')
    (h : EncPolyTimeFam s.enc s'.enc f) :
    EncPolyTimeFam (e.pairFix s).enc (e.pairFix s').enc (fun n p => (p.1, f n p.2)) := sorry

/-- (S6) Commute a fixed block into an option payload: from `γ × Option β` encoded as
`block ++ (tag :: payload)` to `Option (γ × β)` encoded as `tag :: (block ++ payload)`.
Machine sketch: move the tag bit at position `e.wid n` to the front and, on a `false`
tag, zero out the block — a fixed-width rotation plus a conditional clear. Declared
base-machine frontier ticket. -/
noncomputable def optionUnder {γ β : ℕ → Type u} (e : BitEncFam γ) (f : BitEncFam β) :
    EncPolyTimeFam (e.pair f.option).enc ((e.pair f).option).enc
      (fun n (p : γ n × Option (β n)) => p.2.map (p.1, ·)) := sorry

/-! ## Derived injection witnesses

The tag-bit sum injections cost no machine content beyond the frontier's `keep`: the
tag block is a constant, so the proven constant machine (`EncPolyTimeFam.const`)
produces it, `keep` retains the payload after it, and a pure `recode` rebrackets
`[b] ++ s.enc n x` as `(s₁.sum s₂).enc n (Sum.inl x)` / `… (Sum.inr y)`. -/

/-- The constant tag-block witness: every input maps to the unique value of the
width-`1` tag boundary `BitEncFam.tag b`. Fully proven — the constant machine
(`EncPolyTimeFam.const`) erases its input and writes `[b]`; not a frontier ticket. -/
noncomputable def tagWit (s : StrEncFam σ) (b : Bool) :
    EncPolyTimeFam s.enc (BitEncFam.tag b).enc (fun _ _ => PUnit.unit) :=
  .const s.enc (fun _ => PUnit.unit) (.C 1) fun _ => by simp

/-- Left injection into the tag-bit sum encoding: prepend a `false` tag. Derived, not
a frontier primitive: `keep` of the constant `false` tag block (`tagWit`), then a pure
`recode` along `[false] ++ s₁.enc n x = (s₁.sum s₂).enc n (Sum.inl x)` — the only
machine content is the frontier's (`keep`) plus the proven constant machine. -/
noncomputable def inlWit (s₁ : StrEncFam σ₁) (s₂ : StrEncFam σ₂) :
    EncPolyTimeFam s₁.enc (s₁.sum s₂).enc (fun _ => Sum.inl) :=
  (keep s₁ (.tag false) (tagWit s₁ false)).recode (fun _ x => x) (fun _ => Sum.inl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Right injection into the tag-bit sum encoding: prepend a `true` tag. Derived, not
a frontier primitive: `keep` of the constant `true` tag block (`tagWit`), then a pure
`recode` along `[true] ++ s₂.enc n y = (s₁.sum s₂).enc n (Sum.inr y)` — the only
machine content is the frontier's (`keep`) plus the proven constant machine. -/
noncomputable def inrWit (s₁ : StrEncFam σ₁) (s₂ : StrEncFam σ₂) :
    EncPolyTimeFam s₂.enc (s₁.sum s₂).enc (fun _ => Sum.inr) :=
  (keep s₂ (.tag true) (tagWit s₂ true)).recode (fun _ x => x) (fun _ => Sum.inr)
    (fun _ _ => rfl) (fun _ _ => rfl)

end EncPolyTimeFam

end Computability
