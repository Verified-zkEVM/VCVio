/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Computability.PolyTimeTM
public import Mathlib.Data.Nat.Log

/-!
# Canonical Fixed-Width Bit Encodings and Uniform Machine Families

The canonical boundary representation for the polynomial-time adversary model, and the
reusable unit of machine-computability it consumes.

## Why fixed canonical encodings

"Computable in polynomial time relative to *some* encoding" is vacuous: an encoding
`enc x := std x ++ block (f x)` caches any function `f` inside the representation, and
every machine witness degenerates to a projection. Polynomial time is only well-defined
relative to a *fixed canonical* representation (syntactic frameworks fix one implicitly
through the programming language's value representation; a machine-grounded framework
must fix it explicitly). This file provides that representation:

* `Computability.StrEncFam` — a security-parameter-indexed family of injective raw
  `List Bool` encodings with a polynomial length bound. This is the *variable-width*
  notion, the representation freedom left to a machine's internal state.
* `Computability.BitEncFam` — the *fixed-width* refinement: at each parameter every
  value encodes to exactly `wid n` bits, with `wid` polynomially bounded. This is the
  canonical *boundary* representation for inputs, outputs, and oracle interfaces. The
  polynomial width bound is the formal content of the Katz–Lindell `1^n` convention:
  all game values at parameter `n` have `poly(n)`-length representations, so
  "polynomial in `n`" and "polynomial in the input length" agree.
* Constructors: `BitEncFam.const` (fixed-width binary index encoding of a finite type),
  `BitEncFam.bitVec`/`bitVecX` (raw bits), `BitEncFam.pair` (append — widths are fixed,
  so no tags or alphabets are needed), `BitEncFam.option` (tag bit plus padded payload),
  and `StrEncFam.pairVar` (variable-width left ++ fixed-width right, injective because
  the split point is determined from the right — the shape of a machine's
  state/answer update input).
* `Computability.EncPolyTimeFam` — a family of `EncPolyTime` witnesses with uniform
  polynomial time and description-size bounds: the reusable unit "this function family
  is computed by polynomial machines relative to these encodings". Base machines
  produce these; the closure combinators (`comp`, `id`, `const`, `ofFintype`) compose
  them; a polynomial-time adversary carries four of them.

Everything here is raw `α → List Bool`: no `FinEncoding` alphabets and no one-hot
`boolify` relabeling on the canonical side (the legacy `Computability.FinEncoding`
layer remains available for machine-internal state representations).
-/

@[expose] public section

universe u

open Turing.SingleTapeTM

namespace Computability

/-! ## Fixed-width binary strings for natural numbers -/

/-- The `w` low bits of `m`, least significant first. -/
def natToBits (w m : ℕ) : List Bool := (List.range w).map m.testBit

@[simp] theorem length_natToBits (w m : ℕ) : (natToBits w m).length = w := by
  simp [natToBits]

/-- Distinct numbers below `2 ^ w` have distinct `w`-bit strings. -/
theorem natToBits_inj {w m₁ m₂ : ℕ} (h₁ : m₁ < 2 ^ w) (h₂ : m₂ < 2 ^ w)
    (h : natToBits w m₁ = natToBits w m₂) : m₁ = m₂ := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rcases lt_or_ge i w with hi | hi
  · have := List.map_inj_left.mp (by simpa [natToBits] using h) i (List.mem_range.mpr hi)
    exact this
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h₁ (Nat.pow_le_pow_right (by omega) hi)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by omega) hi))]

/-! ## Variable-width bounded string encodings -/

/-- A security-parameter-indexed family of injective raw bit-string encodings with a
polynomial length bound: the representation freedom left to a machine's internal
state. Injectivity is the only semantic demand; the length bound is what keeps
resource accounting polynomial. -/
structure StrEncFam (α : ℕ → Type u) : Type u where
  /-- The raw bit-string encoding at each parameter. -/
  enc : (n : ℕ) → α n → List Bool
  /-- The encoding is injective at each parameter. -/
  enc_injective : ∀ n, Function.Injective (enc n)
  /-- Polynomial bound on encoded lengths (over *all* values, not only reachable ones). -/
  bound : Polynomial ℕ
  /-- All encodings respect the length bound. -/
  len_le : ∀ n x, (enc n x).length ≤ bound.eval n

/-! ## Fixed-width canonical boundary encodings -/

/-- A security-parameter-indexed family of **fixed-width** raw bit-string encodings:
the canonical boundary representation. At parameter `n` every value encodes to exactly
`wid n` bits, and `wid` is polynomially bounded — the formal content of the
Katz–Lindell `1^n` convention. Fixed widths make pairing literal append and let the
split point of any concatenation be recovered positionally, with no alphabets, tags,
or self-delimiting machinery. -/
structure BitEncFam (α : ℕ → Type u) : Type u where
  /-- The exact encoded width at each parameter. -/
  wid : ℕ → ℕ
  /-- Polynomial bound on the widths — the `1^n` convention. -/
  widBound : Polynomial ℕ
  /-- The widths respect the bound. -/
  wid_le : ∀ n, wid n ≤ widBound.eval n
  /-- The raw bit-string encoding at each parameter. -/
  enc : (n : ℕ) → α n → List Bool
  /-- Every encoding has exactly the fixed width. -/
  len_eq : ∀ n x, (enc n x).length = wid n
  /-- The encoding is injective at each parameter. -/
  enc_injective : ∀ n, Function.Injective (enc n)

namespace BitEncFam

variable {α β : ℕ → Type u}

/-- Forget the fixed width, keeping the polynomial length bound. -/
def toStrEncFam (e : BitEncFam α) : StrEncFam α where
  enc := e.enc
  enc_injective := e.enc_injective
  bound := e.widBound
  len_le n x := (e.len_eq n x).le.trans (e.wid_le n)

@[simp] theorem toStrEncFam_enc (e : BitEncFam α) : e.toStrEncFam.enc = e.enc := rfl

@[simp] theorem toStrEncFam_bound (e : BitEncFam α) : e.toStrEncFam.bound = e.widBound := rfl

/-- The canonical encoding of a constant finite type: the fixed-width binary encoding
of the enumeration index, width `⌈log₂ card γ⌉`. `Unit` gets width `0`, `Bool` width
`1`, `Fin k` width `⌈log₂ k⌉`. -/
noncomputable def const (γ : Type u) [Fintype γ] : BitEncFam (fun _ => γ) where
  wid _ := Nat.clog 2 (Fintype.card γ)
  widBound := .C (Nat.clog 2 (Fintype.card γ))
  wid_le _ := by simp
  enc _ x := natToBits (Nat.clog 2 (Fintype.card γ)) (Fintype.equivFin γ x)
  len_eq _ _ := length_natToBits _ _
  enc_injective n x y h := by
    have hlt : ∀ z : γ, ((Fintype.equivFin γ) z : ℕ) < 2 ^ Nat.clog 2 (Fintype.card γ) :=
      fun z => lt_of_lt_of_le (Fintype.equivFin γ z).isLt (Nat.le_pow_clog one_lt_two _)
    exact (Fintype.equivFin γ).injective (Fin.val_injective (natToBits_inj (hlt x) (hlt y) h))

/-- The canonical `Unit` boundary: width `0`. -/
noncomputable abbrev unit : BitEncFam (fun _ => PUnit.{u + 1}) := const PUnit

/-- The canonical `Bool` boundary: width `1`. -/
noncomputable abbrev bool : BitEncFam (fun _ => Bool) := const Bool

/-- The canonical encoding of a `Fin (k n + 1)` family (e.g. a round counter): the
binary index in exactly `k n` bits, using `i ≤ k n < 2 ^ (k n)`. -/
noncomputable def fin (k : ℕ → ℕ) (p : Polynomial ℕ) (hk : ∀ n, k n ≤ p.eval n) :
    BitEncFam (fun n => Fin (k n + 1)) where
  wid := k
  widBound := p
  wid_le := hk
  enc n i := natToBits (k n) i
  len_eq n i := length_natToBits _ _
  enc_injective n i j h := by
    have hlt : ∀ m : Fin (k n + 1), (m : ℕ) < 2 ^ k n :=
      fun m => lt_of_lt_of_le m.isLt (Nat.succ_le_of_lt Nat.lt_two_pow_self)
    exact Fin.val_injective (natToBits_inj (hlt i) (hlt j) h)

/-- The canonical encoding of a bitvector family: the raw bits, least significant
first, width exactly `w n` — linear, where a unary enumeration would be exponential. -/
noncomputable def bitVec (w : ℕ → ℕ) (p : Polynomial ℕ) (hw : ∀ n, w n ≤ p.eval n) :
    BitEncFam (fun n => BitVec (w n)) where
  wid := w
  widBound := p
  wid_le := hw
  enc n v := (List.range (w n)).map v.getLsbD
  len_eq n v := by simp
  enc_injective n v₁ v₂ h := by
    refine BitVec.eq_of_getLsbD_eq_iff.mpr fun i hi => ?_
    exact List.map_inj_left.mp h i (List.mem_range.mpr hi)

/-- The canonical `BitVec n` boundary. -/
noncomputable def bitVecX : BitEncFam (fun n => BitVec n) :=
  bitVec id .X fun n => (Polynomial.eval_X (x := n)).ge

/-- Pair two fixed-width boundaries by literal append: the widths are fixed, so the
split point is positional and no separator is needed. Widths add. -/
noncomputable def pair (e₁ : BitEncFam α) (e₂ : BitEncFam β) : BitEncFam (fun n => α n × β n) where
  wid n := e₁.wid n + e₂.wid n
  widBound := e₁.widBound + e₂.widBound
  wid_le n := by
    have := e₁.wid_le n; have := e₂.wid_le n
    simp only [Polynomial.eval_add]; omega
  enc n p := e₁.enc n p.1 ++ e₂.enc n p.2
  len_eq n p := by rw [List.length_append, e₁.len_eq, e₂.len_eq]
  enc_injective n p q h := by
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [e₁.len_eq, e₁.len_eq])
    exact Prod.ext (e₁.enc_injective n h₁) (e₂.enc_injective n h₂)

/-- The canonical optional boundary: one tag bit, then the payload (zero-padded for
`none`), width `1 + wid`. This is the shape of a machine's optional readout. -/
noncomputable def option (e : BitEncFam α) : BitEncFam (fun n => Option (α n)) where
  wid n := e.wid n + 1
  widBound := e.widBound + .C 1
  wid_le n := by have := e.wid_le n; simp only [Polynomial.eval_add, Polynomial.eval_C]; omega
  enc n
    | Option.none => false :: List.replicate (e.wid n) false
    | Option.some x => true :: e.enc n x
  len_eq n x := by cases x <;> simp [e.len_eq]
  enc_injective n x y h := by
    cases x <;> cases y <;> simp only [List.cons.injEq] at h
    · rfl
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact congrArg _ (e.enc_injective n h.2)

end BitEncFam

/-! ## Variable-left, fixed-right pairing -/

namespace StrEncFam

variable {σ β : ℕ → Type u}

/-- Pair a variable-width encoding with a fixed-width one by append: injective because
the fixed-width right component determines the split point from the right. This is the
input shape of a machine's state/answer update. -/
noncomputable def pairVar (s : StrEncFam σ) (e : BitEncFam β) : StrEncFam (fun n => σ n × β n) where
  enc n p := s.enc n p.1 ++ e.enc n p.2
  enc_injective n p q h := by
    obtain ⟨h₁, h₂⟩ := List.append_inj' h (by rw [e.len_eq, e.len_eq])
    exact Prod.ext (s.enc_injective n h₁) (e.enc_injective n h₂)
  bound := s.bound + e.widBound
  len_le n p := by
    rw [List.length_append, e.len_eq]
    have := s.len_le n p.1; have := e.wid_le n
    simp only [Polynomial.eval_add]; omega

@[simp] theorem pairVar_enc (s : StrEncFam σ) (e : BitEncFam β) (n : ℕ) (p : σ n × β n) :
    (s.pairVar e).enc n p = s.enc n p.1 ++ e.enc n p.2 := rfl

/-- Tag-bit sum of raw string encodings: `false ::` the left payload, `true ::` the
right payload. The state shape of a two-phase (`⊕`-state) machine. -/
noncomputable def sum {τ : ℕ → Type u} (s₁ : StrEncFam σ) (s₂ : StrEncFam τ) :
    StrEncFam (fun n => σ n ⊕ τ n) where
  enc n := Sum.elim (fun x => false :: s₁.enc n x) (fun y => true :: s₂.enc n y)
  enc_injective n x y h := by
    cases x <;> cases y <;> simp only [Sum.elim_inl, Sum.elim_inr, List.cons.injEq] at h
    · exact congrArg Sum.inl (s₁.enc_injective n h.2)
    · exact absurd h.1 (by simp)
    · exact absurd h.1 (by simp)
    · exact congrArg Sum.inr (s₂.enc_injective n h.2)
  bound := s₁.bound + s₂.bound + .C 1
  len_le n x := by
    cases x with
    | inl x =>
      have := s₁.len_le n x
      simp only [Sum.elim_inl, List.length_cons, Polynomial.eval_add, Polynomial.eval_C]
      omega
    | inr y =>
      have := s₂.len_le n y
      simp only [Sum.elim_inr, List.length_cons, Polynomial.eval_add, Polynomial.eval_C]
      omega

@[simp] theorem sum_enc_inl {τ : ℕ → Type u} (s₁ : StrEncFam σ) (s₂ : StrEncFam τ)
    (n : ℕ) (x : σ n) : (s₁.sum s₂).enc n (Sum.inl x) = false :: s₁.enc n x := rfl

@[simp] theorem sum_enc_inr {τ : ℕ → Type u} (s₁ : StrEncFam σ) (s₂ : StrEncFam τ)
    (n : ℕ) (y : τ n) : (s₁.sum s₂).enc n (Sum.inr y) = true :: s₂.enc n y := rfl

end StrEncFam

namespace BitEncFam

variable {γ : ℕ → Type u} {σ : ℕ → Type u}

/-- Pair a fixed-width encoding on the left with a variable-width one on the right by
append — the mirror of `StrEncFam.pairVar`. Injective because the fixed-width left
component determines the split point from the left. This is the state shape of a
machine carrying a fixed-width value alongside a running machine's state. -/
noncomputable def pairFix (e : BitEncFam γ) (s : StrEncFam σ) :
    StrEncFam (fun n => γ n × σ n) where
  enc n p := e.enc n p.1 ++ s.enc n p.2
  enc_injective n p q h := by
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [e.len_eq, e.len_eq])
    exact Prod.ext (e.enc_injective n h₁) (s.enc_injective n h₂)
  bound := e.widBound + s.bound
  len_le n p := by
    rw [List.length_append, e.len_eq]
    have := s.len_le n p.2; have := e.wid_le n
    simp only [Polynomial.eval_add]; omega

@[simp] theorem pairFix_enc (e : BitEncFam γ) (s : StrEncFam σ) (n : ℕ) (p : γ n × σ n) :
    (e.pairFix s).enc n p = e.enc n p.1 ++ s.enc n p.2 := rfl

/-- The all-zero padding block of a prescribed fixed width: a `PUnit` boundary whose
encoding is `wid n` zero bits — the `none`-payload shape of `BitEncFam.option`. -/
noncomputable def pad (w : ℕ → ℕ) (p : Polynomial ℕ) (hw : ∀ n, w n ≤ p.eval n) :
    BitEncFam (fun _ => PUnit.{u + 1}) where
  wid := w
  widBound := p
  wid_le := hw
  enc n _ := List.replicate (w n) false
  len_eq n _ := List.length_replicate
  enc_injective _ x y _ := by cases x; cases y; rfl

@[simp] theorem pad_enc (w : ℕ → ℕ) (p : Polynomial ℕ) (hw : ∀ n, w n ≤ p.eval n)
    (n : ℕ) (x : PUnit) : (pad w p hw).enc n x = List.replicate (w n) false := rfl

end BitEncFam

/-! ## Uniform polynomial-time machine families -/

/-- A family of encoded polynomial-time machine witnesses with **uniform** polynomial
bounds: one machine per security parameter computing `f n` relative to the given
string encodings, a single polynomial bounding all running times (in `n` plus the
input length), and a single polynomial bounding all description sizes (the advice
bound — without it, per-parameter table machines smuggle unbounded advice). This is
the reusable unit of the polynomial-time adversary model: base machines produce these,
combinators compose them, and an adversary's four step functions each carry one. -/
structure EncPolyTimeFam {α β : ℕ → Type u}
    (ea : (n : ℕ) → α n → List Bool) (eb : (n : ℕ) → β n → List Bool)
    (f : (n : ℕ) → α n → β n) : Type (u + 1) where
  /-- The machine witness at each parameter. -/
  wit : (n : ℕ) → EncPolyTime (ea n) (eb n) (f n)
  /-- Uniform polynomial bound on running times, in `n` plus the input length. -/
  time : Polynomial ℕ
  /-- Every witness runs within the uniform time bound. -/
  time_le : ∀ n k, ((wit n).time).eval k ≤ time.eval (n + k)
  /-- Uniform polynomial bound on description sizes — the advice bound. -/
  size : Polynomial ℕ
  /-- Every witness's machine description is within the advice bound. -/
  size_le : ∀ n, (wit n).size ≤ size.eval n

namespace EncPolyTimeFam

variable {α β γ : ℕ → Type u}
  {ea : (n : ℕ) → α n → List Bool} {eb : (n : ℕ) → β n → List Bool}
  {ec : (n : ℕ) → γ n → List Bool}

/-- Transport a witness family along string-equal encodings on both sides: the machines,
time polynomial, and advice bound are untouched (`EncPolyTime.recode` per parameter).
The workhorse for pure re-bracketings of encoded data — `cons`/append associativity and
pair/sum reshuffles cost no machine content. -/
def recode {α' β' : ℕ → Type u} {ea' : (n : ℕ) → α' n → List Bool}
    {eb' : (n : ℕ) → β' n → List Bool} {f : (n : ℕ) → α n → β n}
    (h : EncPolyTimeFam ea eb f) (φ : (n : ℕ) → α' n → α n) (g : (n : ℕ) → α' n → β' n)
    (hin : ∀ n x, ea' n x = ea n (φ n x))
    (hout : ∀ n x, eb' n (g n x) = eb n (f n (φ n x))) :
    EncPolyTimeFam ea' eb' g where
  wit n := (h.wit n).recode (φ n) (g n) (hin n) (hout n)
  time := h.time
  time_le := h.time_le
  size := h.size
  size_le := h.size_le

/-- The identity family: one state, unit time. -/
noncomputable def id (ea : (n : ℕ) → α n → List Bool) :
    EncPolyTimeFam ea ea (fun _ => _root_.id) where
  wit n := .id (ea n)
  time := .C 1
  time_le n k := by
    simp only [EncPolyTime.time, EncPolyTime.id, PolyTimeComputable.id, Polynomial.eval_one,
      Polynomial.eval_C]
    exact le_rfl
  size := .C 1
  size_le n := by simp

/-- Transport a family along pointwise-equal functions. -/
def copy {f : (n : ℕ) → α n → β n} (h : EncPolyTimeFam ea eb f)
    (f' : (n : ℕ) → α n → β n) (hf : ∀ n x, f n x = f' n x) :
    EncPolyTimeFam ea eb f' where
  wit n := (h.wit n).copy (f' n) (hf n)
  time := h.time
  time_le n k := by simpa [EncPolyTime.copy, EncPolyTime.time] using h.time_le n k
  size := h.size
  size_le n := by simpa using h.size_le n

/-- Composition of uniform families: witnesses compose by `EncPolyTime.comp`; the
uniform time bound composes through the output-length envelope, and description
sizes add. -/
noncomputable def comp {f : (n : ℕ) → α n → β n} {g : (n : ℕ) → β n → γ n}
    (h : EncPolyTimeFam ea eb f) (h' : EncPolyTimeFam eb ec g) :
    EncPolyTimeFam ea ec (fun n => g n ∘ f n) where
  wit n := (h.wit n).comp (h'.wit n)
  time := h.time + h'.time.comp (.C 1 + .X + h.time)
  time_le n k := by
    rw [EncPolyTime.comp_time_eval]
    have h1 : ((h.wit n).time).eval k ≤ h.time.eval (n + k) := h.time_le n k
    have h2 : ((h'.wit n).time).eval (1 + k + ((h.wit n).time).eval k) ≤
        h'.time.eval (n + (1 + k + ((h.wit n).time).eval k)) := h'.time_le n _
    have h3 : h'.time.eval (n + (1 + k + ((h.wit n).time).eval k)) ≤
        h'.time.eval (1 + (n + k) + h.time.eval (n + k)) :=
      Polynomial.eval_le_eval (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X,
      Polynomial.eval_C]
    omega
  size := h.size + h'.size
  size_le n := by
    rw [EncPolyTime.size_comp]
    have := h.size_le n; have := h'.size_le n
    simp only [Polynomial.eval_add]; omega

/-- The constant family, from a length bound on the encoded constants: the machine
erases its input and writes the constant. -/
noncomputable def const (ea : (n : ℕ) → α n → List Bool) {eb : (n : ℕ) → β n → List Bool}
    (c : (n : ℕ) → β n) (B : Polynomial ℕ) (hB : ∀ n, (eb n (c n)).length ≤ B.eval n) :
    EncPolyTimeFam ea eb (fun n _ => c n) where
  wit n := .const (ea n) (eb n) (c n)
  time := .X + B + .C 2
  time_le n k := by
    have hlen := hB n
    have hmono : B.eval n ≤ B.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    show ((constPolyTimeComputable (eb n (c n))).poly).eval k ≤ _
    simp only [constPolyTimeComputable, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega
  size := B + .C 2
  size_le n := by
    refine (EncPolyTime.size_const_le _ _ _).trans ?_
    have := hB n
    simp only [Polynomial.eval_add, Polynomial.eval_C]; omega

/-- The finite-table family, for input families of polynomially bounded cardinality
and encoding length: any function family is computable by lookup tables, within the
advice bound exactly when the domain stays polynomially small. -/
noncomputable def ofFintype [∀ n, Fintype (α n)] {ea : (n : ℕ) → α n → List Bool}
    (hea : ∀ n, Function.Injective (ea n)) {eb : (n : ℕ) → β n → List Bool}
    (f : (n : ℕ) → α n → β n)
    (cardIn : Polynomial ℕ) (hcard : ∀ n, Fintype.card (α n) ≤ cardIn.eval n)
    (lenIn : Polynomial ℕ) (hlenIn : ∀ n x, (ea n x).length ≤ lenIn.eval n)
    (lenOut : Polynomial ℕ) (hlenOut : ∀ n x, (eb n (f n x)).length ≤ lenOut.eval n) :
    EncPolyTimeFam ea eb f where
  wit n := .ofFintype (ea n) (hea n) (eb n) (f n)
  time := .X + lenOut + .C 1
  time_le n k := by
    refine (EncPolyTime.time_ofFintype_eval_le (hea n) (hlenOut n) k).trans ?_
    have : lenOut.eval n ≤ lenOut.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
  size := cardIn * (lenIn + .C 1 + lenOut) + .C 1
  size_le n := by
    refine (EncPolyTime.size_ofFintype_le_of_bounds (hea n) (hcard n) (hlenIn n)
      (hlenOut n)).trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact le_rfl

end EncPolyTimeFam

end Computability
