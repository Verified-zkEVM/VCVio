/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.Prelude.Core
public import VCVio.OracleComp.Support
public import VCVio.EvalDist.Defs.Support.Failure
public import ToMathlib.Control.OptionT
public import Batteries.Control.OptionT

/-!
# Executable uniform oracle programs

`ProbComp` programs draw finite-range uniform inputs. The sampling operations and container
notation in this module are executable; their possible outputs use native attachment semantics.
-/

public section


open OracleComp ENNReal

universe u v w

/-- Simplified notation for computations with no oracles besides random inputs.
This specific case can be used with `#eval` to run a random program, see `OracleComp.runIO`.
NOTE: Need to decide if this should be more opaque than `abbrev`, seems like no as of now.. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec

namespace ProbComp

/-- Independently sample `k` values from `samp`, returning them as a `Fin k → α`. -/
@[expose]
def sampleIID {α : Type} (k : ℕ) (samp : ProbComp α) : ProbComp (Fin k → α) :=
  Fin.mOfFn k fun _ => samp

section uniformFin

/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
@[expose]
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  unifSpec.query n

notation "$[0.." n "]" => uniformFin n

@[grind =]
lemma uniformFin_def (n : ℕ) : $[0..n] = unifSpec.query n := rfl

@[simp]
lemma support_uniformFin (n : ℕ) :
    support (do $[0..n]) = Set.univ := by simp [uniformFin_def]

/-- Nicer induction rule for `ProbComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← $[0..n]; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected theorem inductionOn {α} {C : ProbComp α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (n : ℕ) → (mx : Fin (n + 1) → ProbComp α) → (∀ m, C (mx m)) → C ($[0..n] >>= mx))
    (oa : ProbComp α) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa

end uniformFin

section uniformRange

/-- Select uniformly from a non-empty range. The notation attempts to derive `h` automatically. -/
@[expose]
def uniformRange (n m : ℕ) (h : n < m) :
    ProbComp (Fin (m + 1)) :=
  (fun ⟨x, hx⟩ => ⟨x + n, by omega⟩) <$> $[0..(m - n)]

/-- Tactic to attempt to prove `uniformRange` decreasing bound, similar to array indexing. -/
syntax (name := uniformRangeTactic) "uniform_range_tactic" : tactic
macro_rules | `(tactic| uniform_range_tactic) => `(tactic | trivial)
macro_rules | `(tactic| uniform_range_tactic) => `(tactic | get_elem_tactic)

/-- Select uniformly from `[n, m]`, proving the bound with `uniform_range_tactic`. -/
notation "$[" n "⋯" m "]" => uniformRange n m (by uniform_range_tactic)

example {m n : ℕ} (h : m < n) : ProbComp ℕ := do
  let x ← $[314⋯31415]; let y ← $[0⋯10] -- Prove by trivial reduction
  let z ← $[m⋯n] -- Use value from hypothesis
  return x + 2 * y

@[simp, grind =]
lemma uniformRange_eq_uniformFin (n : ℕ) (hn : 0 < n) : $[0⋯n] = $[0..n] := rfl

@[simp, grind =]
lemma support_uniformRange (n m : ℕ) (h : n < m) :
    support (uniformRange n m h) =
      Set.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  ext k
  rw [uniformRange, MonadAttach.support_map, support_uniformFin,
    Set.mem_Icc, Fin.ofNat_Icc_iff h]
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; dsimp; omega
  · intro hk
    exact ⟨⟨k - n, by omega⟩, Fin.ext (by simp; omega)⟩


end uniformRange

section uniformSelect

/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`.
`β` is marked as an `outParam` so that Lean will first pick the output type before synthesizing.
NOTE: This current implementation doesn't impose any "correctness" conditions,
it purely exists to provide the notation, could revisit that in the future. -/
class HasUniformSelect (cont : Type u) (β : outParam Type) where
  uniformSelect : cont → OptionT ProbComp β

/-- Version of `HasUniformSelect` that doesn't allow for failure.
Useful for things like `Vector` that can be shown nonempty at the type level. -/
class HasUniformSelect! (cont : Type u) (β : outParam Type) where
  uniformSelect! : cont → ProbComp β

export HasUniformSelect (uniformSelect)
export HasUniformSelect! (uniformSelect!)

prefix : 75 "$" => uniformSelect
prefix : 75 "$!" => uniformSelect!

variable {cont : Type u} {β : Type}

/-- Given a non-failing uniform selection operation we also have a potentially failing one,
using `OptionT.lift` -/
instance hasUniformSelect_of_hasUniformSelect!
    [h : HasUniformSelect! cont β] : HasUniformSelect cont β where
  uniformSelect cont := OptionT.lift ($! cont)

/-- Compatibility of the `$! xs` operation with `$ xs` given the inferred instance.
TODO: I think we probably want to `simp` in the other direction when possible? -/
@[simp, grind =] lemma liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : (liftM ($! xs) : OptionT ProbComp β) = $ xs := by
  simp [OptionT.liftM_def]; rfl

lemma uniformSelect_eq_liftM_uniformSelect! [HasUniformSelect! cont β]
    (xs : cont) : ($ xs : OptionT ProbComp β) = liftM ($! xs) := by grind

end uniformSelect

section uniformSelectList

/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just fail rather than choose a default value.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case of empty lists. -/
instance hasUniformSelectList (α : Type) :
    HasUniformSelect (List α) α where
  uniformSelect
    | [] => failure
    | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length]

variable {α : Type} (xs : List α)

lemma uniformSelectList_def : $ xs = match xs with
  | [] => failure
  | x :: xs => ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp, grind =]
lemma uniformSelectList_nil : $ ([] : List α) = failure := rfl

@[grind =]
lemma uniformSelectList_cons (x : α) (xs : List α) :
    $ (x :: xs) = ((x :: xs)[·]) <$> $[0..xs.length] := rfl

@[simp, grind =]
lemma support_uniformSelectList (xs : List α) :
    support ($ xs) = {x | x ∈ xs} := match xs with
  | [] => by simp
  | x :: xs => by simp [uniformSelectList_cons, Set.ext_iff, Fin.exists_iff,
      - List.mem_cons, List.mem_iff_getElem]

end uniformSelectList

section uniformSelectVector

/-- Select a random element from a vector by indexing into it with a uniform value. -/
instance hasUniformSelectVector (α : Type) (n : ℕ) :
    HasUniformSelect! (Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))

lemma uniformSelectVector_def : $! xs = (xs[·]) <$> $[0..n] := rfl

@[simp, grind =]
lemma support_uniformSelectVector : support ($! xs) = {x | x ∈ xs.toList} := by
  ext x
  simp [uniformSelectVector_def, Vector.mem_iff_getElem, Fin.exists_iff]

end uniformSelectVector

section uniformSelectListVector

instance hasUniformSelectListVector (α : Type) (n : ℕ) :
    HasUniformSelect! (List.Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> $[0..n]

variable {α : Type} {n : ℕ} (xs : List.Vector α (n + 1))

lemma uniformSelectListVector_def : $! xs = (xs[·]) <$> $[0..n] := rfl

end uniformSelectListVector

section uniformSelectFinset

/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) :
    HasUniformSelect (Finset α) α where
  uniformSelect s := $ s.toList

variable {α : Type} (s : Finset α)

lemma uniformSelectFinset_def : $ s = $ s.toList := rfl

@[simp, grind =]
lemma support_uniformSelectFinset :
    support ($ s) = if s.Nonempty then ↑s else ∅ := by
  aesop (add norm uniformSelectFinset_def)

end uniformSelectFinset

section uniformSelectArray

instance hasUniformSelectArray (α : Type _) : HasUniformSelect (Array α) α where
  uniformSelect xs := if h : xs.size = 0 then failure else do
    let u ← $[0..xs.size-1]
    return xs[u] -- Note the in-index bound here relies on `h`.

variable {α : Type} (xs : Array α)

lemma uniformSelectArray_def :
    ($ xs : OptionT ProbComp α) =
      if h : xs.size = 0 then failure else do
        let u ← $[0..xs.size-1]
        return xs[u] := rfl

@[simp, grind =]
lemma uniformSelectArray_empty : ($ (#[] : Array α) : OptionT ProbComp α) = failure := rfl

@[simp, grind =]
lemma support_uniformSelectArray : support ($ xs) = {x | x ∈ xs} := by
  ext x
  rcases Nat.eq_zero_or_pos xs.size with h | h
  · simp [Array.size_eq_zero_iff.mp h]
  · rw [uniformSelectArray_def, dite_eq_right h.ne']
    simp [Array.mem_iff_getElem, Fin.exists_iff, eq_comm, Nat.sub_add_cancel h]

end uniformSelectArray

section uniformSelectMultiset

/-- Choose a random element from a multiset, by converting to a list and choosing from that.
This is noncomputable as the underlying list is only canonical up to permutation; for any
fixed `Multiset.toList` representative each element is sampled with weight equal to its
multiplicity. -/
noncomputable instance hasUniformSelectMultiset (α : Type) :
    HasUniformSelect (Multiset α) α where
  uniformSelect s := $ s.toList

variable {α : Type} (s : Multiset α)

lemma uniformSelectMultiset_def : ($ s : OptionT ProbComp α) = $ s.toList := rfl

@[simp, grind =]
lemma support_uniformSelectMultiset :
    support ($ s) = {x | x ∈ s} := by
  ext x; simp [uniformSelectMultiset_def, Multiset.mem_toList]

end uniformSelectMultiset

end ProbComp

section coinSpec
-- NOTE: This treats `coin` as essentially part of `ProbComp`, but it is more general.
-- In particular we can have a seperate theory of bounded uniform selection using only coins.

@[simp, grind =]
lemma support_coin : support coin = {true, false} := by aesop

end coinSpec
