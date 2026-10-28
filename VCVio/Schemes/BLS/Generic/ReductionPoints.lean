/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionExecution
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Real values of the generic BLS point programs

Scalar multiplication and masked challenge computations allocate valid outer handles while
preserving every existing challenge entry.
-/

public section

open OracleComp OracleSpec GroupModel

namespace BLS.Generic

variable {F R T : Type} {G : Bool → Type}

attribute [local implicit_reducible] spec PFam

/-- Multiplying a valid challenge handle realizes the corresponding real scalar multiple. -/
theorem realizesPoint_smul [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (root : Tbl (PFam (G false) (G true) T)) (h : Handle) (hh : h < (root .g₁).length)
    (c : R → F) :
    RealizesPoint e root
      (fun r => (genSpec F pairingSig).query (.inl (.smul .g₁ (c r) h)))
      (fun r => c r • lookup root .g₁ h) := by
  intro r tbl hp
  have hl := lookup_eq_of_prefix (tbl := root) (tbl' := tbl) .g₁ (hp .g₁) h hh
  refine ⟨(tbl .g₁).length, append tbl .g₁ (c r • lookup root .g₁ h), ?_, ?_, ?_, ?_⟩
  · simp [runGen, run, impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, hl]
  · exact fun s => prefix_append tbl .g₁ s _
  · simp [append]
  · simp [lookup, append]

/-- Scaling a computed point preserves realization and allocates a fresh valid handle. -/
theorem RealizesPoint.smul [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    {e : G false →ₗ[F] G true →ₗ[F] T}
    {root : Tbl (PFam (G false) (G true) T)}
    {program : R → OracleComp (genSpec F pairingSig) Handle} {value : R → G false}
    (hp : RealizesPoint e root program value) (c : R → F) :
    RealizesPoint e root (fun r => do
      let h ← program r
      (genSpec F pairingSig).query (.inl (.smul .g₁ (c r) h))) (fun r => c r • value r) := by
  intro r tbl hroot
  obtain ⟨h, tbl', hr, hext, _, hv⟩ := hp r tbl hroot
  refine ⟨(tbl' .g₁).length, append tbl' .g₁ (c r • value r), ?_, ?_, ?_, ?_⟩
  · rw [runGen_bind, hr, pure_bind]
    simp [runGen, run, impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, hv]
    rfl
  · exact fun s => (hext s).trans (prefix_append tbl' .g₁ s _)
  · simp [append]
  · simp [lookup, append]

/-- Adding two point programs preserves both values even when the second extends the table. -/
theorem RealizesPoint.add [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    {e : G false →ₗ[F] G true →ₗ[F] T}
    {root : Tbl (PFam (G false) (G true) T)}
    {p₁ p₂ : R → OracleComp (genSpec F pairingSig) Handle} {v₁ v₂ : R → G false}
    (h₁ : RealizesPoint e root p₁ v₁) (h₂ : RealizesPoint e root p₂ v₂) :
    RealizesPoint e root (fun r => do
      let a ← p₁ r
      let b ← p₂ r
      (genSpec F pairingSig).query (.inl (.add .g₁ a b))) (fun r => v₁ r + v₂ r) := by
  intro r tbl hroot
  obtain ⟨a, t₁, ha, hext₁, hvalid₁, hv₁⟩ := h₁ r tbl hroot
  obtain ⟨b, t₂, hb, hext₂, _, hv₂⟩ := h₂ r t₁ (fun s => (hroot s).trans (hext₁ s))
  have hv₁' : lookup t₂ .g₁ a = v₁ r :=
    (lookup_eq_of_prefix (tbl := t₁) (tbl' := t₂) .g₁ (hext₂ .g₁) a hvalid₁).trans hv₁
  refine ⟨(t₂ .g₁).length, append t₂ .g₁ (v₁ r + v₂ r), ?_, ?_, ?_, ?_⟩
  · rw [runGen_bind, ha, pure_bind, runGen_bind, hb, pure_bind]
    simp [runGen, run, impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, hv₁', hv₂]
    rfl
  · exact fun s => ((hext₁ s).trans (hext₂ s)).trans (prefix_append t₂ .g₁ s _)
  · simp [append]
  · simp [lookup, append]

/-- The generic mask program realizes the affine combination of the two challenge entries. -/
theorem realizesPoint_maskedPoint [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (root : Tbl (PFam (G false) (G true) T)) (hroot : 1 < (root .g₁).length) :
    RealizesPoint e root maskedPoint
      (fun r : F × F => r.1 • lookup root .g₁ 1 + r.2 • lookup root .g₁ 0) :=
  (realizesPoint_smul e root 1 hroot Prod.fst).add
    (realizesPoint_smul e root 0 (Nat.lt_trans Nat.zero_lt_one hroot) Prod.snd)

end BLS.Generic
