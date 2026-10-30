/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Hashing.Encoding

/-!
# Ordered preimage resolvers

Finite candidate search fixes the preimage choice on every partial table, including tables with
collisions. Inserting a fresh input with a different response preserves that choice.
-/

public section

namespace MerkleTreeExtractor

universe u v
variable {X : Type u} {Y : Type v}

/-! ## Least preimages -/

/-- The least element of a finite set, if it is nonempty. -/
@[expose]
def leastOf {α : Type*} [LinearOrder α] (s : Finset α) : Option α :=
  s.min

/-- The least element of a set with only one element is that element. -/
theorem leastOf_eq_some {α : Type*} [LinearOrder α] {s : Finset α} {a : α} (ha : a ∈ s)
    (huniq : ∀ b ∈ s, b = a) : leastOf s = some a := by
  have hs : s = {a} := Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, huniq⟩
  change s.min = (a : WithTop α)
  rw [hs, Finset.min_singleton]

/-- The least `a` with `D (f a) = some u`, if there is one. -/
@[expose]
def leastPre {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq Y] (f : α → X)
    (D : X → Option Y) (u : Y) : Option α :=
  leastOf (Finset.univ.filter fun a ↦ D (f a) = some u)

section leastPre

variable {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq Y] {f : α → X} {D : X → Option Y}
  {u : Y} {a : α}

/-- The least preimage is a preimage. -/
theorem leastPre_spec (h : leastPre f D u = some a) : D (f a) = some u := by
  simpa using Finset.mem_of_min h

/-- A unique preimage is the least preimage. -/
theorem leastPre_eq_some (h : D (f a) = some u) (huniq : ∀ b, D (f b) = some u → b = a) :
    leastPre f D u = some a :=
  leastOf_eq_some (by simpa using h) fun b hb ↦ huniq b (by simpa using hb)

/-- Adding the entry `x ↦ y` at an empty position does not change the preimages of `u ≠ y`. -/
theorem leastPre_update [DecidableEq X] {x : X} {y : Y} (hx : D x = none) (hu : u ≠ y) :
    leastPre f (Function.update D x (some y)) u = leastPre f D u := by
  unfold leastPre
  congr 1
  refine Finset.filter_congr fun b _ ↦ ?_
  by_cases hb : f b = x
  · rw [hb, Function.update_self, hx]
    simp [Ne.symm hu]
  · rw [Function.update_of_ne hb]

end leastPre


/-- Candidate search equals least decoded supported-input selection, on every partial table. -/
theorem leastPre_eq_leastDecoded {α : Type*} [Fintype α] [LinearOrder α] [DecidableEq Y]
    (encode : α → X) (decoder : MerkleTreeHashing.RoleDecoder encode)
    (D : X → Option Y) (u : Y) :
    leastPre encode D u = by
      classical
      exact leastOf (Finset.univ.filter fun p =>
        ∃ x, D x = some u ∧ decoder.decode x = some p) := by
  classical
  unfold leastPre
  congr 1
  apply Finset.filter_congr
  intro p _
  constructor
  · intro hp
    exact ⟨encode p, hp, decoder.decode_encode p⟩
  · rintro ⟨x, hx, hp⟩
    rwa [decoder.encode_decode x p hp]

/-- Select the least ordered pair whose encoded input has the required answer. -/
@[expose]
def resolvePair {A B : Type*} [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    [DecidableEq Y] (encode : A × B → X) (D : X → Option Y) (u : Y) : Option (A × B) :=
  (leastPre (fun p : Lex (A × B) => encode (ofLex p)) D u).map ofLex

/-- A selected pair hashes to the requested response in the partial table. -/
theorem resolvePair_spec {A B : Type*} [Fintype A] [LinearOrder A]
    [Fintype B] [LinearOrder B] [DecidableEq Y] {encode : A × B → X}
    {D : X → Option Y} {u : Y} {p : A × B} (h : resolvePair encode D u = some p) :
    D (encode p) = some u := by
  obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp h
  exact leastPre_spec (α := Lex (A × B)) hp'

/-- A uniquely determined pair is selected. -/
theorem resolvePair_eq_some {A B : Type*} [Fintype A] [LinearOrder A]
    [Fintype B] [LinearOrder B] [DecidableEq Y] {encode : A × B → X}
    {D : X → Option Y} {u : Y} {p : A × B} (h : D (encode p) = some u)
    (huniq : ∀ q, D (encode q) = some u → q = p) : resolvePair encode D u = some p := by
  have hp : leastPre (fun q : Lex (A × B) => encode (ofLex q)) D u = some (toLex p) :=
    leastPre_eq_some h fun q hq => congrArg toLex (huniq _ hq)
  simp [resolvePair, hp]

/-- An injective encoding and unique table responses determine the recovered pair. -/
theorem resolvePair_eq_of_injective {A B : Type*} [Fintype A] [LinearOrder A]
    [Fintype B] [LinearOrder B] [DecidableEq Y] {encode : A × B → X}
    (hinj : Function.Injective encode) {D : X → Option Y}
    (hD : ∀ ⦃x₀ x₁ : X⦄ ⦃y : Y⦄, D x₀ = some y → D x₁ = some y → x₀ = x₁)
    {u : Y} {p : A × B} (h : D (encode p) = some u) : resolvePair encode D u = some p :=
  resolvePair_eq_some h fun _ hp => hinj (hD hp h)

/-- Fresh insertion at another response preserves the least pair, even in a collisionful table. -/
theorem resolvePair_update {A B : Type*} [Fintype A] [LinearOrder A]
    [Fintype B] [LinearOrder B] [DecidableEq Y] [DecidableEq X] (encode : A × B → X)
    {D : X → Option Y} {x : X} {y u : Y} (hx : D x = none) (hu : u ≠ y) :
    resolvePair encode (Function.update D x (some y)) u = resolvePair encode D u := by
  simp only [resolvePair, leastPre_update hx hu]

end MerkleTreeExtractor
