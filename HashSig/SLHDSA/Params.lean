/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import Mathlib.Data.Nat.Log
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# SLH-DSA Parameters

Fixed constants and all twelve approved parameter sets for SLH-DSA (FIPS 205). The development
stays generic over the variable parameters while keeping the historical
**SLH-DSA-SHA2-128-24** SP 800-230 reduced set in a separate, explicitly non-FIPS namespace.

The Winternitz and FORS lengths are derived from the primary parameters exactly as in FIPS 205
§5 (Eqs 5.1–5.3) and §9 (the message-digest length `m`); see `Params.len1`, `Params.len2`,
`Params.len`, and `Params.m`.

## References

- NIST FIPS 205 (SLH-DSA), Sections 4, 5, 9, 10, 11 (Table 2 parameter sets)
- NIST SP 800-230 ipd (the reduced 2²⁴-usage parameter set)
-/

@[expose] public section


namespace SLHDSA

/-- Byte values used by the SLH-DSA encodings and address layout. -/
abbrev Byte := UInt8

/-- Fixed-length byte vectors used by the FIPS 205 interfaces. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- The variable parameters that distinguish SLH-DSA instantiations (FIPS 205, Table 2). -/
structure Params where
  /-- Security parameter: hash output length in bytes (also the node size). -/
  n : ℕ
  /-- Total hypertree height. -/
  h : ℕ
  /-- Number of hypertree layers. -/
  d : ℕ
  /-- Per-XMSS-tree height `h' = h / d`. -/
  hp : ℕ
  /-- FORS tree height (each FORS tree has `2^a` leaves). -/
  a : ℕ
  /-- Number of FORS trees. -/
  k : ℕ
  /-- Bits per WOTS+ chain (`w = 2^lgw`). -/
  lgw : ℕ
deriving Repr, DecidableEq

namespace Params

/-- The Winternitz parameter `w = 2^lgw` (FIPS 205 Eq 5.1). -/
def w (p : Params) : ℕ := 2 ^ p.lgw

/-- WOTS+ message length `len1 = ⌈8n / lgw⌉` (FIPS 205 Eq 5.2). -/
def len1 (p : Params) : ℕ := (8 * p.n + p.lgw - 1) / p.lgw

/-- WOTS+ checksum length `len2 = ⌊log_w(len1·(w−1))⌋ + 1` (FIPS 205 Eq 5.3, computed via
`Nat.log` rather than the iterative `gen_len2` of Algorithm 1). -/
def len2 (p : Params) : ℕ := Nat.log p.w (p.len1 * (p.w - 1)) + 1

/-- Total number of WOTS+ chains `len = len1 + len2`. -/
def len (p : Params) : ℕ := p.len1 + p.len2

/-- Number of leaves in one FORS tree, `t = 2^a`. -/
def t (p : Params) : ℕ := 2 ^ p.a

/-- Bytes of the message digest fed to FORS, `⌈k·a / 8⌉`. -/
def digestBytes (p : Params) : ℕ := (p.k * p.a + 7) / 8

/-- Bytes selecting the lowest-layer XMSS tree, `⌈(h − h') / 8⌉`. -/
def treeIdxBytes (p : Params) : ℕ := (p.h - p.hp + 7) / 8

/-- Bytes selecting the WOTS+/FORS leaf within its tree, `⌈h / (8d)⌉`. -/
def leafIdxBytes (p : Params) : ℕ := (p.h + 8 * p.d - 1) / (8 * p.d)

/-- Length of the message digest produced by `H_msg`,
`m = ⌈k·a/8⌉ + ⌈(h−h')/8⌉ + ⌈h/(8d)⌉` (FIPS 205 §9). -/
def m (p : Params) : ℕ := p.digestBytes + p.treeIdxBytes + p.leafIdxBytes

/-- Signature size in bytes, `(1 + k(1+a) + h + d·len)·n` (FIPS 205 Fig 17). -/
def signatureBytes (p : Params) : ℕ := (1 + p.k * (1 + p.a) + p.h + p.d * p.len) * p.n

/-- Public-key size in bytes, `2n` (`PK.seed ‖ PK.root`). -/
def publicKeyBytes (p : Params) : ℕ := 2 * p.n

/-- Secret-key size in bytes, `4n` (`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`). -/
def secretKeyBytes (p : Params) : ℕ := 4 * p.n

end Params

/-- The two FIPS 205 hash-function families. -/
inductive HashFamily where
  | sha2 | shake
deriving Repr, DecidableEq

/-- One authoritative FIPS 205 Table 2 row, including the independently checked wire sizes. -/
structure ParameterProfile where
  name : String
  family : HashFamily
  params : Params
  category : ℕ
  expectedM : ℕ
  digestBytes : ℕ
  treeIdxBytes : ℕ
  leafIdxBytes : ℕ
  publicKeyBytes : ℕ
  secretKeyBytes : ℕ
  signatureBytes : ℕ
deriving Repr, DecidableEq

/-- The complete closed family of FIPS 205 approved parameter-set identifiers. -/
inductive ParameterSet where
  | SLHDSA_SHA2_128s | SLHDSA_SHAKE_128s
  | SLHDSA_SHA2_128f | SLHDSA_SHAKE_128f
  | SLHDSA_SHA2_192s | SLHDSA_SHAKE_192s
  | SLHDSA_SHA2_192f | SLHDSA_SHAKE_192f
  | SLHDSA_SHA2_256s | SLHDSA_SHAKE_256s
  | SLHDSA_SHA2_256f | SLHDSA_SHAKE_256f
deriving Repr, DecidableEq, Fintype

namespace ParameterSet

/-- Interpret an approved name as its exact FIPS 205 Table 2 row. -/
def profile : ParameterSet → ParameterProfile
  | .SLHDSA_SHA2_128s =>
      ⟨"SLH-DSA-SHA2-128s", .sha2, ⟨16, 63, 7, 9, 12, 14, 4⟩,
        1, 30, 21, 7, 2, 32, 64, 7856⟩
  | .SLHDSA_SHAKE_128s =>
      ⟨"SLH-DSA-SHAKE-128s", .shake, ⟨16, 63, 7, 9, 12, 14, 4⟩,
        1, 30, 21, 7, 2, 32, 64, 7856⟩
  | .SLHDSA_SHA2_128f =>
      ⟨"SLH-DSA-SHA2-128f", .sha2, ⟨16, 66, 22, 3, 6, 33, 4⟩,
        1, 34, 25, 8, 1, 32, 64, 17088⟩
  | .SLHDSA_SHAKE_128f =>
      ⟨"SLH-DSA-SHAKE-128f", .shake, ⟨16, 66, 22, 3, 6, 33, 4⟩,
        1, 34, 25, 8, 1, 32, 64, 17088⟩
  | .SLHDSA_SHA2_192s =>
      ⟨"SLH-DSA-SHA2-192s", .sha2, ⟨24, 63, 7, 9, 14, 17, 4⟩,
        3, 39, 30, 7, 2, 48, 96, 16224⟩
  | .SLHDSA_SHAKE_192s =>
      ⟨"SLH-DSA-SHAKE-192s", .shake, ⟨24, 63, 7, 9, 14, 17, 4⟩,
        3, 39, 30, 7, 2, 48, 96, 16224⟩
  | .SLHDSA_SHA2_192f =>
      ⟨"SLH-DSA-SHA2-192f", .sha2, ⟨24, 66, 22, 3, 8, 33, 4⟩,
        3, 42, 33, 8, 1, 48, 96, 35664⟩
  | .SLHDSA_SHAKE_192f =>
      ⟨"SLH-DSA-SHAKE-192f", .shake, ⟨24, 66, 22, 3, 8, 33, 4⟩,
        3, 42, 33, 8, 1, 48, 96, 35664⟩
  | .SLHDSA_SHA2_256s =>
      ⟨"SLH-DSA-SHA2-256s", .sha2, ⟨32, 64, 8, 8, 14, 22, 4⟩,
        5, 47, 39, 7, 1, 64, 128, 29792⟩
  | .SLHDSA_SHAKE_256s =>
      ⟨"SLH-DSA-SHAKE-256s", .shake, ⟨32, 64, 8, 8, 14, 22, 4⟩,
        5, 47, 39, 7, 1, 64, 128, 29792⟩
  | .SLHDSA_SHA2_256f =>
      ⟨"SLH-DSA-SHA2-256f", .sha2, ⟨32, 68, 17, 4, 9, 35, 4⟩,
        5, 49, 40, 8, 1, 64, 128, 49856⟩
  | .SLHDSA_SHAKE_256f =>
      ⟨"SLH-DSA-SHAKE-256f", .shake, ⟨32, 68, 17, 4, 9, 35, 4⟩,
        5, 49, 40, 8, 1, 64, 128, 49856⟩

/-- Primary parameters of an approved set. -/
def params (s : ParameterSet) : Params := s.profile.params

/-- Canonical FIPS Table 2 order. -/
def all : List ParameterSet :=
  [.SLHDSA_SHA2_128s, .SLHDSA_SHAKE_128s,
   .SLHDSA_SHA2_128f, .SLHDSA_SHAKE_128f,
   .SLHDSA_SHA2_192s, .SLHDSA_SHAKE_192s,
   .SLHDSA_SHA2_192f, .SLHDSA_SHAKE_192f,
   .SLHDSA_SHA2_256s, .SLHDSA_SHAKE_256s,
   .SLHDSA_SHA2_256f, .SLHDSA_SHAKE_256f]

@[simp] theorem all_length : all.length = 12 := by decide

theorem card : Fintype.card ParameterSet = 12 := by decide

/-- The derived widths agree with every independently recorded FIPS Table 2 value. -/
theorem profile_sizes (s : ParameterSet) :
    s.params.m = s.profile.expectedM ∧
    s.params.digestBytes = s.profile.digestBytes ∧
    s.params.treeIdxBytes = s.profile.treeIdxBytes ∧
    s.params.leafIdxBytes = s.profile.leafIdxBytes ∧
    s.params.publicKeyBytes = s.profile.publicKeyBytes ∧
    s.params.secretKeyBytes = s.profile.secretKeyBytes ∧
    s.params.signatureBytes = s.profile.signatureBytes := by
  cases s <;> decide

/-- All approved rows have FIPS's `lgw=4` and exact WOTS chain-count widths. -/
theorem wots_widths (s : ParameterSet) :
    s.params.lgw = 4 ∧ s.params.len1 = 2 * s.params.n ∧
    s.params.len2 = 3 ∧ s.params.len = 2 * s.params.n + 3 := by
  cases s <;> decide

/-- Reject a parameter record unless it is exactly one of the twelve approved rows. -/
def ofParams (p : Params) : Option ParameterSet :=
  all.find? (fun s => decide (s.params = p))

end ParameterSet

/-- Historical non-FIPS parameter-set identifiers kept outside `ParameterSet`. -/
inductive LegacyParameterSet where
  | SLHDSA_SHA2_128_24
deriving Repr, DecidableEq

namespace LegacyParameterSet

/-- Interpret the historical SP 800-230 IPD reduced set. -/
def params : LegacyParameterSet → Params
  | .SLHDSA_SHA2_128_24 => ⟨16, 22, 1, 22, 24, 6, 2⟩

end LegacyParameterSet

/-- The non-FIPS SLH-DSA-SHA2-128-24 parameter record. -/
def slhdsaSha2_128_24 : Params := LegacyParameterSet.params .SLHDSA_SHA2_128_24

namespace Params

/-- Executable approval predicate: equality with one of the twelve FIPS Table 2 rows. -/
def isApproved (p : Params) : Bool := ParameterSet.all.any (fun s => s.params == p)

/-- The structural and approval facts required of a FIPS parameter row. -/
def Valid (p : Params) : Prop :=
  p.isApproved = true ∧ 0 < p.n ∧ 0 < p.h ∧ 0 < p.d ∧ 0 < p.hp ∧
  0 < p.a ∧ 0 < p.k ∧ 0 < p.lgw ∧ p.h = p.hp * p.d

end Params

/-- Every named FIPS parameter set satisfies the approval and structural checks. -/
theorem ParameterSet.valid (s : ParameterSet) : s.params.Valid := by
  cases s <;>
    simp [Params.Valid, Params.isApproved, ParameterSet.all, ParameterSet.params,
      ParameterSet.profile]

/-- The historical reduced profile is deliberately excluded from FIPS approval. -/
theorem legacy_not_approved : slhdsaSha2_128_24.isApproved = false := by decide

end SLHDSA
