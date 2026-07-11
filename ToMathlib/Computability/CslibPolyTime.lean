/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import ToMathlib.Computability.Encoding

/-!
# Encoded Polynomial-Time Computability

Cslib's `Turing.SingleTapeTM.PolyTimeComputable` certifies polynomial-time computability
of raw string functions `List Symbol → List Symbol`. This file adds the encoding layer:
`Computability.EncPolyTime ea eb f` witnesses that a function `f : α → β` between
arbitrary types is polynomial-time computable relative to `Bool`-string encodings
`ea : α → List Bool` and `eb : β → List Bool`, by bundling a machine-computed total
string function that intertwines the encodings. Encodings typically arise from a
`Computability.FinEncoding` via `FinEncoding.boolify`.

Identity and composition (`EncPolyTime.id`, `EncPolyTime.comp`) lift directly from
Cslib's proven `PolyTimeComputable.id` and `PolyTimeComputable.comp`; the monotone
time-bound side condition of the latter is discharged by `PolyTimeComputable.normalize`,
which replaces a machine's time bound with its own polynomial.

Besides the running time `EncPolyTime.time`, every witness has a **description size**
`EncPolyTime.size`: the state count of its machine. Cslib's `PolyTimeComputable` bounds
only the running time, which suffices for a *single* function but not for a *family* of
witnesses indexed by a security parameter: a finite-table machine looks up any function
in linear time using one state per valid input, so without a size bound a family of
witnesses smuggles unbounded advice and the induced "polynomial-time" class contains
every function on polynomially-encodable domains. Families must therefore bound
`size` polynomially as well (see `PolyTimeAdversary.descBound`), giving the standard
non-uniform P/poly model.
-/

@[expose] public section

universe u v w u_1 u_2

/-- Evaluation of a natural-number polynomial is monotone in the argument. -/
theorem Polynomial.eval_le_eval {p : Polynomial ℕ} {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  rw [p.eval_eq_sum_range, p.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

namespace Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Replace the time bound of a polynomial-time machine by the evaluation of its own
polynomial. The resulting bound is monotone, as required by `PolyTimeComputable.comp`
for the second machine. -/
def PolyTimeComputable.normalize {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : PolyTimeComputable f where
  tm := h.tm
  timeBound n := h.poly.eval n
  outputsFunInTime a := (h.outputsFunInTime a).of_le (h.bounds _)
  poly := h.poly
  bounds _ := le_rfl

theorem PolyTimeComputable.monotone_normalize_timeBound {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : Monotone h.normalize.timeBound :=
  fun _ _ hmn => Polynomial.eval_le_eval hmn

/-- The description size of a machine witness: its number of states. Over a fixed tape
alphabet the transition table has one row per state, so this measures the machine's
description — the "advice" of a non-uniform family. Time bounds alone do not control
it: a table machine looks up any function on a finite domain in linear time using one
state per valid input. -/
def PolyTimeComputable.size {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : ℕ := Fintype.card h.tm.State

@[simp] theorem PolyTimeComputable.size_normalize {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) : h.normalize.size = h.size := rfl

end Turing.SingleTapeTM

namespace Computability

open Turing.SingleTapeTM

variable {α : Type u} {β : Type v} {γ : Type w}

/-- A witness that `f : α → β` is polynomial-time computable relative to `Bool`-string
encodings of its domain and codomain: a total string function, computed by a single-tape
machine in polynomial time, that maps the encoding of `a` to the encoding of `f a`.

The string function is total: its behavior on strings outside the range of `ea` is
unconstrained. -/
structure EncPolyTime (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  /-- The total string function the machine computes. -/
  toFun : List Bool → List Bool
  /-- The machine computing `toFun`, with its polynomial time bound. -/
  polyTime : PolyTimeComputable toFun
  /-- The string function intertwines the encodings. -/
  map_encode : ∀ a, toFun (ea a) = eb (f a)

namespace EncPolyTime

variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}

/-- The polynomial time bound of the underlying machine. -/
def time {f : α → β} (h : EncPolyTime ea eb f) : Polynomial ℕ := h.polyTime.poly

/-- The description size (machine state count) of the underlying machine. Families of
witnesses indexed by a security parameter must bound this polynomially — the advice
bound of the non-uniform P/poly model; see the module docstring. -/
def size {f : α → β} (h : EncPolyTime ea eb f) : ℕ := h.polyTime.size

/-- The identity function is polynomial-time computable relative to any encoding. -/
noncomputable def id (ea : α → List Bool) : EncPolyTime ea ea _root_.id where
  toFun := _root_.id
  polyTime := PolyTimeComputable.id
  map_encode _ := rfl

/-- The identity witness has a single machine state. -/
@[simp] theorem size_id (ea : α → List Bool) : (EncPolyTime.id ea).size = 1 :=
  Fintype.card_punit

/-- Transport a witness along a pointwise-equal function. -/
def copy {f : α → β} (h : EncPolyTime ea eb f) (f' : α → β) (hf : ∀ a, f a = f' a) :
    EncPolyTime ea eb f' where
  toFun := h.toFun
  polyTime := h.polyTime
  map_encode a := (h.map_encode a).trans (congrArg eb (hf a))

/-- Transporting along a pointwise-equal function preserves the machine, hence the size. -/
@[simp] theorem size_copy {f : α → β} (h : EncPolyTime ea eb f) (f' : α → β)
    (hf : ∀ a, f a = f' a) : (h.copy f' hf).size = h.size := rfl

/-- Transport a witness along string-equal encodings on both sides: if `ea'` encodes
each `a'` exactly as `ea` encodes `φ a'`, and `eb'` encodes each `g a'` exactly as `eb`
encodes `f (φ a')`, the same machine witnesses `g` relative to `ea'`/`eb'`. The machine,
time, and size are untouched — this discharges pure re-bracketings and re-taggings of
encoded data (`cons`/append associativity, pair/sum reshuffles) with no machine content. -/
def recode {α' : Type u_1} {β' : Type u_2} {ea' : α' → List Bool} {eb' : β' → List Bool}
    {f : α → β} (h : EncPolyTime ea eb f) (φ : α' → α) (g : α' → β')
    (hin : ∀ a', ea' a' = ea (φ a')) (hout : ∀ a', eb' (g a') = eb (f (φ a'))) :
    EncPolyTime ea' eb' g where
  toFun := h.toFun
  polyTime := h.polyTime
  map_encode a' := by rw [hin, h.map_encode, ← hout]

/-- Recoding preserves the machine's time polynomial. -/
@[simp] theorem time_recode {α' : Type u_1} {β' : Type u_2} {ea' : α' → List Bool}
    {eb' : β' → List Bool} {f : α → β} (h : EncPolyTime ea eb f) (φ : α' → α) (g : α' → β')
    (hin : ∀ a', ea' a' = ea (φ a')) (hout : ∀ a', eb' (g a') = eb (f (φ a'))) :
    (h.recode φ g hin hout).time = h.time := rfl

/-- Recoding preserves the machine, hence the description size. -/
@[simp] theorem size_recode {α' : Type u_1} {β' : Type u_2} {ea' : α' → List Bool}
    {eb' : β' → List Bool} {f : α → β} (h : EncPolyTime ea eb f) (φ : α' → α) (g : α' → β')
    (hin : ∀ a', ea' a' = ea (φ a')) (hout : ∀ a', eb' (g a') = eb (f (φ a'))) :
    (h.recode φ g hin hout).size = h.size := rfl

/-- Composition of encoded polynomial-time witnesses, from Cslib's
`PolyTimeComputable.comp`. -/
noncomputable def comp {f : α → β} {f' : β → γ}
    (h : EncPolyTime ea eb f) (h' : EncPolyTime eb ec f') :
    EncPolyTime ea ec (f' ∘ f) where
  toFun := h'.toFun ∘ h.toFun
  polyTime := h.polyTime.comp h'.polyTime.normalize h'.polyTime.monotone_normalize_timeBound
  map_encode a := by
    simp only [Function.comp_apply, h.map_encode, h'.map_encode]

/-- The polynomial time bound of a composition, unfolded: the first machine's polynomial plus
the second's evaluated at the first's output-length envelope `1 + X + h.time`. -/
theorem comp_time {f : α → β} {f' : β → γ}
    (h : EncPolyTime ea eb f) (h' : EncPolyTime eb ec f') :
    (h.comp h').time = h.time + h'.time.comp (1 + Polynomial.X + h.time) := rfl

/-- Evaluation of the composed time bound: `h`'s cost at input length `k`, plus `h'`'s cost at the
length `h`'s output can reach (`1 + k + h.time.eval k`). -/
theorem comp_time_eval {f : α → β} {f' : β → γ}
    (h : EncPolyTime ea eb f) (h' : EncPolyTime eb ec f') (k : ℕ) :
    (h.comp h').time.eval k = h.time.eval k + h'.time.eval (1 + k + h.time.eval k) := by
  rw [comp_time]; simp [Polynomial.eval_comp]

/-- The composed machine is Cslib's phase-sum `compComputer`, so description sizes add. -/
theorem size_comp {f : α → β} {f' : β → γ}
    (h : EncPolyTime ea eb f) (h' : EncPolyTime eb ec f') :
    (h.comp h').size = h.size + h'.size :=
  Fintype.card_sum

/-- The output encoding of a polynomial-time computable function is at most polynomially
longer than the input encoding, by `output_length_le_input_length_add_time`. -/
theorem length_le {f : α → β} (h : EncPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ max 1 (ea a).length + h.time.eval (ea a).length := by
  rw [← h.map_encode a]
  refine le_trans (output_length_le_input_length_add_time h.polyTime.tm _ _ _
    (h.polyTime.outputsFunInTime (ea a))) ?_
  exact Nat.add_le_add_left (h.polyTime.bounds _) _

end EncPolyTime

end Computability
