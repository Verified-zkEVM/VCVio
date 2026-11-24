/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded
-- Only the infinite-support negative control unfolds the existing fallback implementation.
import all VCVio.OracleComp.QueryTracking.RandomOracle.Encoded

/-!
# Endpoints of finite full-cache completion

A cached full word may have a different first coordinate from the typed response.
Completion keeps that response and the cached word's second coordinate.
Aliased typed inputs and infinite typed support show why stronger conclusions need more premises.
All controls use small value spaces and leave the raw input carrier unbounded.
-/

public section

open OracleComp OracleSpec

namespace FillEndpointTest

/-- A bounded value space containing all displayed low and high coordinates. -/
abbrev Low := Fin 1024

/-- Identity routing with the first coordinate as the typed observation. -/
private noncomputable def identityEncoding :
    RandomOracleEncoding (Nat →ₒ Low) Nat (Low × Low) :=
  .ofSplit (Tail := fun _ => Low) id some (fun h => (Option.some.inj h).symm)
    (fun _ => rfl) (fun _ => Equiv.refl _)

private theorem identity_no_clash (c : (Nat →ₒ Low).QueryCache) :
    ¬identityEncoding.Clash c := by
  rintro ⟨a, b, hne, _, _, he⟩
  exact hne he

/-- A warm auxiliary first coordinate is overwritten, while its exact second coordinate remains. -/
example : ∃ completed ∈ support (identityEncoding.fill
    ((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17,
      (∅ : (Nat →ₒ Low × Low).QueryCache).cacheQuery 7 (999, 23))),
    completed 7 = some (17, 23) ∧ completed 7 ≠ some (999, 23) := by
  obtain ⟨completed, hb⟩ := OracleComp.support_nonempty (identityEncoding.fill
    ((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17,
      (∅ : (Nat →ₒ Low × Low).QueryCache).cacheQuery 7 (999, 23)))
  refine ⟨completed, hb, ?_⟩
  have hf : {q | (((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17) q).isSome}.Finite := by
    simp [QueryCache.isSome_cacheQuery_apply_iff]
  have h := (identityEncoding.mem_support_fill_coordinates hf (identity_no_clash _) hb).2.1
    7 17 (999, 23) (by simp) (by simp [identityEncoding, RandomOracleEncoding.ofSplit])
  change completed 7 = some (17, 23) at h
  refine ⟨h, ?_⟩
  rw [h]
  decide

/-- Filling a previously uncached raw word still retains the stored typed response. -/
example (completed : (Nat →ₒ Low × Low).QueryCache)
    (hb : completed ∈ support (identityEncoding.fill
      ((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17, ∅))) :
    (completed 7).map Prod.fst = some 17 := by
  have hf : {q | (((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17) q).isSome}.Finite := by
    simp [QueryCache.isSome_cacheQuery_apply_iff]
  exact (identityEncoding.mem_support_fill_coordinates hf (identity_no_clash _) hb).1
    7 17 (by simp)

/-- Auxiliary entries outside the cached typed domain remain in the full domain. -/
example (completed : (Nat →ₒ Low × Low).QueryCache)
    (hb : completed ∈ support (identityEncoding.fill
      ((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17,
        (∅ : (Nat →ₒ Low × Low).QueryCache).cacheQuery 8 (999, 23)))) :
    (completed 7).isSome ∧ (completed 8).isSome ∧ completed 9 = none := by
  have hf : {q | (((∅ : (Nat →ₒ Low).QueryCache).cacheQuery 7 17) q).isSome}.Finite := by
    simp [QueryCache.isSome_cacheQuery_apply_iff]
  have h := (identityEncoding.mem_support_fill_coordinates hf (identity_no_clash _) hb).2.2
  have domain (n : Nat) : (completed n).isSome ↔ n = 8 ∨ n = 7 := by
    simpa [RandomOracleEncoding.Covered, identityEncoding, RandomOracleEncoding.ofSplit,
      QueryCache.isSome_cacheQuery_apply_iff] using h n
  refine ⟨(domain 7).2 (by simp), (domain 8).2 (by simp), ?_⟩
  exact Option.not_isSome_iff_eq_none.1 ((domain 9).not.2 (by simp))

/-- Two typed inputs share one raw input; both read its first coordinate. -/
private noncomputable def aliasedEncoding :
    RandomOracleEncoding (Bool →ₒ Bool) Unit (Bool × Bool) :=
  .ofSplit (Tail := fun _ => Bool) (fun _ => ()) (fun _ => some false)
    (fun _ => rfl) (fun _ => rfl) (fun _ => Equiv.refl _)

/-- A single occupied typed point does not clash, despite the noninjective encoding. -/
private theorem aliased_no_clash :
    ¬aliasedEncoding.Clash ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery false true) := by
  rintro ⟨a, b, hne, ha, hb, _⟩
  simp [QueryCache.isSome_cacheQuery_apply_iff] at ha hb
  exact hne (ha.trans hb.symm)

/-- Filling one aliased point can create a projected value at an absent typed point. -/
example (completed : (Unit →ₒ Bool × Bool).QueryCache)
    (hb : completed ∈ support (aliasedEncoding.fill
      ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery false true, ∅))) :
    QueryCache.ofFn (fun q => (completed (aliasedEncoding.encode q)).map
      (aliasedEncoding.trunc q)) ≠
        (∅ : (Bool →ₒ Bool).QueryCache).cacheQuery false true := by
  have hf : {q | (((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery false true) q).isSome}.Finite :=
    Set.toFinite _
  have h := (aliasedEncoding.mem_support_fill_coordinates hf aliased_no_clash hb).1
    false true (by simp)
  change (completed ()).map Prod.fst = some true at h
  intro he
  have hx := congrArg (fun c : (Bool →ₒ Bool).QueryCache => c true) he
  change (completed ()).map Prod.fst = none at hx
  rw [h] at hx
  contradiction

/-- Infinite typed support selects the existing empty fallback, so finite support is essential. -/
example :
    let c : (Nat →ₒ Low).QueryCache := QueryCache.ofFn fun _ => some 17
    identityEncoding.fill (c, ∅) = pure ∅ ∧ c 0 = some 17 := by
  dsimp only
  have hf : ¬(Set.univ : Set Nat).Finite := Set.infinite_univ
  simp [RandomOracleEncoding.fill, identity_no_clash, hf]

end FillEndpointTest
