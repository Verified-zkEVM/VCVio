/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import VCVio.CryptoFoundations.MerkleTree.Addressed.Uniqueness

/-!
# Merkle Opening Uniqueness

Two openings at the same leaf index that recompute the same putative root must agree on both the
leaf value and the authentication path, provided the hash is injective on the node-hash inputs
the two openings induce. This is the deterministic analog of extractability: the Merkle root
uniquely determines the committed value at each position.

The hypothesis is local to a query transcript. `openingHashQueries` lists the ordered child pairs
hashed while recomputing the root of one opening, and `HashInjectiveOnQueries h log` asks for
injectivity of `h` only among the pairs of a finite `log`. A compressing hash is never globally
injective, but it can be injective on a query transcript, which is the form consumed by a
random-oracle or collision-resistance argument: a failure of uniqueness is a collision between two
queried pairs (`getPutativeRootWithHash_eq_or_collision_mem_openingHashQueries`).

The unaddressed tree is the addressed tree of `VCVio.CryptoFoundations.MerkleTree.Addressed` at
the constant address `Unit` (`openingQueries_unit`), so the queried-domain results here are
corollaries of `AddressedMerkleTree.opening_unique_of_queryInjectiveOn` and
`AddressedMerkleTree.findCollisionAddressed_mem_openingQueries`. The statements under global
`Function.Injective2 h` are the special case where the log is the union of both transcripts.

Combined with `getPutativeRootWithHash_binding` from `Binding.lean`, this
gives a complete picture of Merkle commitment security:
- **Binding** (no CR needed): same index, distinct values → hash collision.
- **Uniqueness** (hash injective on the queried pairs): same index, same root → identical
  opening.

The distinct-index case is not a binding violation — two different leaf
positions producing the same root is normal Merkle tree operation.

## Main Results

- `openingHashQueries`, `OpeningHashCovered`, `HashInjectiveOnQueries` — the node-hash inputs of
  one opening, their coverage by a log, and injectivity of the hash on a log
- `findCollision_mem_openingHashQueries` — the collision returned by `findCollision` consists of
  one queried pair from each opening
- `getPutativeRootWithHash_eq_or_collision_mem_openingHashQueries` — two openings with the same
  root either agree or exhibit a collision between their queried pairs
- `getPutativeRootWithHash_unique_of_queryInjectiveOn` — opening uniqueness under injectivity on
  a covering query log
- `getPutativeRootWithHash_unique` — opening uniqueness under a globally injective hash
- `getPutativeRootWithHash_roots_ne_of_ne` — contrapositive: distinct values
  at the same index produce distinct roots

## References

- Justin Thaler. *Proofs, Arguments, and Zero-Knowledge.* §7.3.2.2
  (Merkle-tree string commitment binding property)
- Vitalik Buterin. `Binding.lean` (PR #384) — same-index collision extraction
-/

@[expose] public section

namespace InductiveMerkleTree

open BinaryTree AddressedMerkleTree

variable {α : Type _}

/-! ## Queried node-hash inputs -/

/-- The hash `h` is injective on the supplied finite query transcript: two logged child pairs
with the same hash value are equal. Unlike `Function.Injective2 h`, this permits collisions
outside the logged pairs. -/
def HashInjectiveOnQueries (h : α → α → α) (log : List (α × α)) : Prop :=
  ∀ p₁ ∈ log, ∀ p₂ ∈ log, h p₁.1 p₁.2 = h p₂.1 p₂.2 → p₁ = p₂

/-- A globally injective hash is injective on every query transcript. -/
theorem HashInjectiveOnQueries.of_injective2 {h : α → α → α} (hinj : Function.Injective2 h)
    (log : List (α × α)) : HashInjectiveOnQueries h log :=
  fun _ _ _ _ heq => Prod.ext (hinj heq).1 (hinj heq).2

/-- Injectivity on a query transcript passes to every sub-transcript. -/
theorem HashInjectiveOnQueries.mono {h : α → α → α} {log log' : List (α × α)}
    (hinj : HashInjectiveOnQueries h log) (hsub : ∀ p ∈ log', p ∈ log) :
    HashInjectiveOnQueries h log' :=
  fun p₁ hp₁ p₂ hp₂ => hinj p₁ (hsub p₁ hp₁) p₂ (hsub p₂ hp₂)

/-- The ordered child pairs hashed while recomputing the putative root of one opening, listed
from the root toward the leaf. -/
def openingHashQueries (h : α → α → α) : {s : Skeleton} →
    (idx : SkeletonLeafIndex s) → α → List.Vector α idx.depth → List (α × α)
  | _, .ofLeaf, _, _ => []
  | _, .ofLeft idx, leaf, proof =>
      (getPutativeRootWithHash idx leaf proof.tail h, proof.head) ::
        openingHashQueries h idx leaf proof.tail
  | _, .ofRight idx, leaf, proof =>
      (proof.head, getPutativeRootWithHash idx leaf proof.tail h) ::
        openingHashQueries h idx leaf proof.tail

/-- Every node-hash input induced by an opening occurs in `log`. -/
def OpeningHashCovered (h : α → α → α) (log : List (α × α)) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leaf : α) (proof : List.Vector α idx.depth) : Prop :=
  ∀ p ∈ openingHashQueries h idx leaf proof, p ∈ log

/-- At the constant address `Unit`, the addressed opening transcript is the unaddressed one
with every child pair tagged by the unit address. -/
theorem openingQueries_unit (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (leaf : α) (proof : List.Vector α idx.depth) :
    openingQueries (fun _ => ()) (fun (_ : Unit) => h) idx leaf proof =
      (openingHashQueries h idx leaf proof).map (fun p => ⟨(), p⟩) := by
  induction idx with
  | ofLeaf => rfl
  | ofLeft idx ih =>
      simp [openingQueries, openingHashQueries, getPutativeRootAddressed_const, ih]
  | ofRight idx ih =>
      simp [openingQueries, openingHashQueries, getPutativeRootAddressed_const, ih]

/-- Membership in a unit-tagged transcript is membership of the underlying child pair. -/
private theorem unit_mem_map_iff (p : α × α) (log : List (α × α)) :
    (⟨(), p⟩ : NodeQuery Unit α) ∈ log.map (fun p => ⟨(), p⟩) ↔ p ∈ log :=
  List.mem_map_of_injective (fun _ _ hpq => congrArg NodeQuery.input hpq)

/-- The collision returned by `findCollision` consists of one queried pair from each compared
opening: the first pair lies in the first opening's transcript and the second pair in the
second's. -/
theorem findCollision_mem_openingHashQueries [DecidableEq α] (h : α → α → α) {s : Skeleton}
    (idx : SkeletonLeafIndex s) (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (w : α × α × α × α) (hw : findCollision h idx proof₁ proof₂ x y = some w) :
    (w.1, w.2.1) ∈ openingHashQueries h idx x proof₁ ∧
      (w.2.2.1, w.2.2.2) ∈ openingHashQueries h idx y proof₂ := by
  rw [← findCollisionAddressed_const] at hw
  obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hw
  obtain ⟨h₁, h₂⟩ := findCollisionAddressed_mem_openingQueries (Address := Unit) (fun _ => ())
    (fun _ => h) idx proof₁ proof₂ x y w' hw'
  rw [openingQueries_unit, unit_mem_map_iff] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- **Transcript-local collision.** Two openings at the same index that recompute the same root
either agree, or some pair queried by the first opening and some pair queried by the second are
distinct inputs with the same hash value. -/
theorem getPutativeRootWithHash_eq_or_collision_mem_openingHashQueries
    (h : α → α → α) {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (heq : getPutativeRootWithHash idx x proof₁ h = getPutativeRootWithHash idx y proof₂ h) :
    (x = y ∧ proof₁ = proof₂) ∨
      ∃ p₁ ∈ openingHashQueries h idx x proof₁, ∃ p₂ ∈ openingHashQueries h idx y proof₂,
        p₁ ≠ p₂ ∧ h p₁.1 p₁.2 = h p₂.1 p₂.2 := by
  classical
  by_cases hagree : x = y ∧ proof₁ = proof₂
  · exact Or.inl hagree
  refine Or.inr ?_
  have hopening : (x, proof₁) ≠ (y, proof₂) := fun hpair =>
    hagree ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  have hsome := findCollisionAddressed_isSome_of_opening_ne (fun _ => h) idx proof₁ proof₂ x y
    (by simpa only [getPutativeRootAddressed_const] using heq) hopening
  rw [← Option.isSome_map (f := fun w => w.2), findCollisionAddressed_const] at hsome
  obtain ⟨⟨l₁, r₁, l₂, r₂⟩, hw⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hmem₁, hmem₂⟩ := findCollision_mem_openingHashQueries h idx proof₁ proof₂ x y _ hw
  obtain ⟨hne, hcol⟩ := findCollision_sound h idx proof₁ proof₂ x y l₁ r₁ l₂ r₂ hw
  exact ⟨_, hmem₁, _, hmem₂, hne, hcol⟩

/-! ## Uniqueness -/

/-- **Queried-domain Merkle opening uniqueness.** If two openings at the same leaf index are
covered by one transcript on which `h` is injective, equality of their putative roots forces
equality of both the leaf value and the authentication path.

This is `AddressedMerkleTree.opening_unique_of_queryInjectiveOn` at the constant address
`Unit`. -/
theorem getPutativeRootWithHash_unique_of_queryInjectiveOn
    (h : α → α → α) (log : List (α × α)) (hinj : HashInjectiveOnQueries h log)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth) (x y : α)
    (hcovered₁ : OpeningHashCovered h log idx x proof₁)
    (hcovered₂ : OpeningHashCovered h log idx y proof₂)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    x = y ∧ proof₁ = proof₂ := by
  have hcovered : ∀ {leaf : α} {proof : List.Vector α idx.depth},
      OpeningHashCovered h log idx leaf proof →
        OpeningCovered (fun _ => ()) (fun _ => h) (log.map fun p => ⟨(), p⟩) idx leaf proof := by
    intro leaf proof hcov q hq
    rw [openingQueries_unit] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (unit_mem_map_iff p log).mpr (hcov p hp)
  refine opening_unique_of_queryInjectiveOn (Address := Unit) (fun _ => ()) (fun _ => h)
    (log.map fun p => ⟨(), p⟩) ?_ idx proof₁ proof₂ x y (hcovered hcovered₁)
    (hcovered hcovered₂) (by simpa only [getPutativeRootAddressed_const] using heq)
  rintro _ hq₁ _ hq₂ heval
  obtain ⟨p₁, hp₁, rfl⟩ := List.mem_map.mp hq₁
  obtain ⟨p₂, hp₂, rfl⟩ := List.mem_map.mp hq₂
  rw [hinj p₁ hp₁ p₂ hp₂ heval]

/-- **Merkle opening uniqueness under a globally injective hash.** When `h` is injective, two
openings at the same leaf index that produce the same root must agree on both the leaf value and
the entire authentication path.

This is the special case of `getPutativeRootWithHash_unique_of_queryInjectiveOn` whose log is
the union of the two openings' transcripts. -/
theorem getPutativeRootWithHash_unique
    (h : α → α → α) (hinj : Function.Injective2 h)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α)
    (heq : getPutativeRootWithHash idx x proof₁ h
         = getPutativeRootWithHash idx y proof₂ h) :
    x = y ∧ proof₁ = proof₂ :=
  getPutativeRootWithHash_unique_of_queryInjectiveOn h
    (openingHashQueries h idx x proof₁ ++ openingHashQueries h idx y proof₂)
    (HashInjectiveOnQueries.of_injective2 hinj _) idx proof₁ proof₂ x y
    (fun _ hp => List.mem_append_left _ hp) (fun _ hp => List.mem_append_right _ hp) heq

/-- Contrapositive of uniqueness: with an injective hash, distinct leaf values
    at the same index always produce distinct roots, regardless of the
    authentication paths used. -/
theorem getPutativeRootWithHash_roots_ne_of_ne
    (h : α → α → α) (hinj : Function.Injective2 h)
    {s : Skeleton} (idx : SkeletonLeafIndex s)
    (proof₁ proof₂ : List.Vector α idx.depth)
    (x y : α) (hne : x ≠ y) :
    getPutativeRootWithHash idx x proof₁ h
      ≠ getPutativeRootWithHash idx y proof₂ h :=
  fun heq => hne (getPutativeRootWithHash_unique h hinj idx proof₁ proof₂ x y heq).1

end InductiveMerkleTree
