/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.VectorCommitment
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi

/-!
# Tuples of commitments and decommitments

Multi-extraction for a family of `k` vector commitments works on tuples
(Chiesa, Di, Hu and Zheng, ePrint 2025/2166, §7, p. 49):

* `TpIC k Cm`: tuples `((idx_i, cm_i))_{i ∈ [j]}` of length `j ∈ [k]`, where `idx_i ∈ [k]` names
  an oracle and position `i` belongs to the scheme `VC_i`;
* `TpD k Dm`: tuples `(dm_i)_{i ∈ [j]}` with `dm_i : Dm i`;
* `TpICD k Cm Dm`: pairs of a `TpIC` and a `TpD` of the same length.

The definitions are classical. Lengths range over `TupleLen k`, the nonzero elements of
`Fin (k + 1)`, so that every type here is finite as soon as its components are. The
commitment type `Cm` and the decommitment family `Dm` live in independent universes.

## Main definitions

* `Quantum.TupleLen k`, `Quantum.TpIC k Cm`, `Quantum.TpDLen k Dm j`, `Quantum.TpD k Dm`,
  `Quantum.TpICD k Cm Dm`, and `Quantum.DmOf`, the decommitment type `(m_i, td_i)` of a family of
  vector commitments.
* `Quantum.TpIC.idx`, `Quantum.TpIC.prefix` and `Quantum.TpIC.full`.
-/

public section

universe u v

namespace Quantum

/-! ## Lengths -/

/-- Tuple lengths `j ∈ [k]` (p. 49), as the nonzero elements of `Fin (k + 1)`. -/
abbrev TupleLen (k : ℕ) := {j : Fin (k + 1) // j ≠ 0}

namespace TupleLen

variable {k : ℕ}

/-- The length as a natural number. -/
@[expose]
def len (j : TupleLen k) : ℕ := j.1

/-- The length of `⟨j, h⟩` is `j`. -/
@[simp]
theorem len_mk (j : Fin (k + 1)) (h : j ≠ 0) : len ⟨j, h⟩ = j :=
  rfl

/-- A tuple length is at most `k`. -/
theorem len_le (j : TupleLen k) : j.len ≤ k :=
  Nat.lt_succ_iff.mp j.1.isLt

/-- A tuple length is positive. -/
theorem len_pos (j : TupleLen k) : 0 < j.len :=
  Nat.pos_of_ne_zero fun h ↦ j.2 (Fin.ext h)

/-- The tuple length with the given value `n ∈ [1, k]`. -/
@[expose]
def ofNat (n : ℕ) (h₀ : 0 < n) (hk : n ≤ k) : TupleLen k :=
  ⟨⟨n, Nat.lt_succ_of_le hk⟩, fun h ↦ by simp [Fin.ext_iff] at h; omega⟩

/-- The length of `ofNat n` is `n`. -/
@[simp]
theorem len_ofNat (n : ℕ) (h₀ : 0 < n) (hk : n ≤ k) : (ofNat n h₀ hk).len = n :=
  rfl

/-- The full length `k`, for `k ≥ 1`. -/
@[expose]
def full (hk : 1 ≤ k) : TupleLen k :=
  ofNat k hk le_rfl

/-- The full length is `k`. -/
@[simp]
theorem len_full (hk : 1 ≤ k) : (full hk).len = k :=
  rfl

end TupleLen

/-! ## Tuples -/

/-- `TpIC` (p. 49): tuples `((idx_i, cm_i))_{i ∈ [j]}`. Position `i` belongs to the scheme
`VC_i`, and `idx_i` names its oracle. -/
@[expose]
def TpIC (k : ℕ) (Cm : Type u) : Type u :=
  Σ j : TupleLen k, Fin j.len → Fin k × Cm

/-- Decommitment tuples of length `j` (p. 49): position `i` holds `dm_i : Dm i` of the scheme
`VC_i`. -/
abbrev TpDLen (k : ℕ) (Dm : Fin k → Type v) (j : TupleLen k) : Type v :=
  ∀ i : Fin j.len, Dm (Fin.castLE j.len_le i)

/-- `TpD` (p. 49): decommitment tuples of every length. -/
@[expose]
def TpD (k : ℕ) (Dm : Fin k → Type v) : Type v :=
  Σ j : TupleLen k, TpDLen k Dm j

/-- `TpICD` (p. 49): a commitment tuple with a decommitment tuple of the same length. Equal
lengths are enforced by the type. -/
@[expose]
def TpICD (k : ℕ) (Cm : Type u) (Dm : Fin k → Type v) : Type (max u v) :=
  Σ tic : TpIC k Cm, TpDLen k Dm tic.1

/-- The decommitment type of the scheme `VC_i` in a family of vector commitments:
`dm_i = (m_i, td_i)` with `m_i ∈ (Σ ∪ {⊥})^{ℓ_i}` (p. 49). -/
abbrev DmOf {k : ℕ} (ℓ : Fin k → ℕ) (Msg : Type u) (Td : Fin k → Type v) (i : Fin k) :
    Type (max u v) :=
  PartialVec (ℓ i) Msg × Td i

section instances

variable {k : ℕ} {Cm : Type u} {Dm : Fin k → Type v}

/-- Commitment tuples over a finite type form a finite type. -/
instance [Fintype Cm] : Fintype (TpIC k Cm) :=
  inferInstanceAs (Fintype (Σ j : TupleLen k, Fin j.len → Fin k × Cm))

/-- Commitment tuples have decidable equality. -/
instance [DecidableEq Cm] : DecidableEq (TpIC k Cm) :=
  inferInstanceAs (DecidableEq (Σ j : TupleLen k, Fin j.len → Fin k × Cm))

/-- Decommitment tuples over finite types form a finite type. -/
instance [∀ i, Fintype (Dm i)] : Fintype (TpD k Dm) :=
  inferInstanceAs (Fintype (Σ j : TupleLen k, TpDLen k Dm j))

/-- Decommitment tuples have decidable equality. -/
instance [∀ i, DecidableEq (Dm i)] : DecidableEq (TpD k Dm) :=
  inferInstanceAs (DecidableEq (Σ j : TupleLen k, TpDLen k Dm j))

/-- Pairs of tuples over finite types form a finite type. -/
instance [Fintype Cm] [∀ i, Fintype (Dm i)] : Fintype (TpICD k Cm Dm) :=
  inferInstanceAs (Fintype (Σ tic : TpIC k Cm, TpDLen k Dm tic.1))

/-- Pairs of tuples have decidable equality. -/
instance [DecidableEq Cm] [∀ i, DecidableEq (Dm i)] : DecidableEq (TpICD k Cm Dm) :=
  inferInstanceAs (DecidableEq (Σ tic : TpIC k Cm, TpDLen k Dm tic.1))

end instances

namespace TpIC

variable {k : ℕ} {Cm : Type u}

/-- The oracle indices `(idx_i)_{i ∈ [j]}` of a tuple. -/
@[expose]
def idx (tic : TpIC k Cm) : Fin tic.1.len → Fin k :=
  fun i ↦ (tic.2 i).1

/-- The commitments `(cm_i)_{i ∈ [j]}` of a tuple. -/
@[expose]
def cm (tic : TpIC k Cm) : Fin tic.1.len → Cm :=
  fun i ↦ (tic.2 i).2

/-- The prefix `((idx_i, cm_i))_{i ∈ [j']}` of a tuple, for `j' ≤ j` (Def 7.1 property 2,
p. 49). -/
@[expose]
def «prefix» (tic : TpIC k Cm) (j' : TupleLen k) (h : j'.len ≤ tic.1.len) : TpIC k Cm :=
  ⟨j', fun i ↦ tic.2 (Fin.castLE h i)⟩

/-- The length of a prefix is the requested length. -/
@[simp]
theorem prefix_fst (tic : TpIC k Cm) (j' : TupleLen k) (h : j'.len ≤ tic.1.len) :
    (tic.prefix j' h).1 = j' :=
  rfl

/-- The indices of a prefix are a prefix of the indices. -/
@[simp]
theorem idx_prefix (tic : TpIC k Cm) (j' : TupleLen k) (h : j'.len ≤ tic.1.len)
    (i : Fin j'.len) : (tic.prefix j' h).idx i = tic.idx (Fin.castLE h i) :=
  rfl

/-- A prefix of a tuple with distinct indices has distinct indices. -/
theorem idx_prefix_injective {tic : TpIC k Cm} (hinj : Function.Injective tic.idx)
    (j' : TupleLen k) (h : j'.len ≤ tic.1.len) : Function.Injective (tic.prefix j' h).idx :=
  fun _ _ hab ↦ Fin.castLE_injective h (hinj hab)

/-- The full-length tuple `((idx_i, cm_i))_{i ∈ [k]}` that an adversary outputs in the
extraction games of Def 7.3 (p. 51). -/
@[expose]
def full (hk : 1 ≤ k) (idx : Fin k → Fin k) (cm : Fin k → Cm) : TpIC k Cm :=
  ⟨TupleLen.full hk, fun i ↦ (idx i, cm i)⟩

/-- The indices of a full tuple. -/
@[simp]
theorem idx_full (hk : 1 ≤ k) (idx : Fin k → Fin k) (cm : Fin k → Cm) (i : Fin k) :
    (full hk idx cm).idx i = idx i :=
  rfl

/-- The commitments of a full tuple. -/
@[simp]
theorem cm_full (hk : 1 ≤ k) (idx : Fin k → Fin k) (cm : Fin k → Cm) (i : Fin k) :
    (full hk idx cm).cm i = cm i :=
  rfl

end TpIC

end Quantum
