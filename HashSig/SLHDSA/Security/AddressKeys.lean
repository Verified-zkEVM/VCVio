/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Xmss
public import HashSig.SLHDSA.Fors

/-!
# Role addresses and their byte encodings

The role builders of SLH-DSA (`xmssNodeAdrs`, `wotsPkAdrs`, `wotsChainAdrs`, `wotsSkAdrs`,
`forsNodeAdrs`, `forsSkAdrs`, `forsPkAdrs`) each set the `type` field to a literal and keep some
of the base address's fields; seven `rfl` identities state every builder field by field.

The two byte-oriented address encodings, the 32-byte serialization `SLHDSA.Adrs.toBytes` and the
22-byte `ADRSc` compression `SLHDSA.Adrs.compressSha2`, concatenate fixed-width per-field blocks,
so equal encodings have equal blocks (`toBytes_blocks`, `compressSha2_blocks`).  Consequently a
secret-key address built from a role address has equal encoding whenever the role address does
(`toBytes_forsSkAdrs_congr`, `toBytes_wotsSkAdrs_congr`, `compressSha2_forsSkAdrs_congr`,
`compressSha2_wotsSkAdrs_congr`): at a primitive bundle whose tweak map is one of these encodings,
equal role-address keys give equal secret-key-address keys.

## Labels

Thirteen declarations.

*The role addresses, field by field*: `xmssNodeAdrs_eq`, `wotsPkAdrs_eq`,
`wotsChainAdrs_setHashAddress_eq`, `wotsSkAdrs_eq`, `forsNodeAdrs_eq`, `forsSkAdrs_eq`,
`forsPkAdrs_eq`.

*Block extraction from the two byte-oriented encodings*: `toBytes_blocks`,
`compressSha2_blocks`, `toBytes_forsSkAdrs_congr`, `toBytes_wotsSkAdrs_congr`,
`compressSha2_forsSkAdrs_congr`, `compressSha2_wotsSkAdrs_congr`.
-/

public section

namespace SLHDSA.Security

/-! ## The role addresses, field by field -/

/-- The XMSS node address in full. -/
theorem xmssNodeAdrs_eq (a : Adrs) (z t : ℕ) :
    xmssNodeAdrs a z t = ⟨a.layer, a.tree, 2, 0, z, t⟩ := rfl

/-- The WOTS+ public-key address in full. -/
theorem wotsPkAdrs_eq (a : Adrs) : wotsPkAdrs a = ⟨a.layer, a.tree, 1, a.word1, 0, 0⟩ := rfl

/-- The WOTS+ chain address at one hash address in full. -/
theorem wotsChainAdrs_setHashAddress_eq (a : Adrs) (i t : ℕ) :
    (wotsChainAdrs a i).setHashAddress t = ⟨a.layer, a.tree, 0, a.word1, i, t⟩ := rfl

/-- The WOTS+ secret-key address in full. -/
theorem wotsSkAdrs_eq (a : Adrs) (i : ℕ) :
    wotsSkAdrs a i = ⟨a.layer, a.tree, 5, a.word1, i, 0⟩ := rfl

/-- The FORS node address in full; height `0` is a FORS leaf. -/
theorem forsNodeAdrs_eq (a : Adrs) (z t : ℕ) :
    forsNodeAdrs a z t = ⟨a.layer, a.tree, 3, a.word1, z, t⟩ := rfl

/-- The FORS secret-key address in full. -/
theorem forsSkAdrs_eq (a : Adrs) (t : ℕ) :
    forsSkAdrs a t = ⟨a.layer, a.tree, 6, a.word1, 0, t⟩ := rfl

/-- The FORS roots address in full. -/
theorem forsPkAdrs_eq (a : Adrs) : forsPkAdrs a = ⟨a.layer, a.tree, 4, a.word1, 0, 0⟩ := rfl

/-! ## Block extraction from the two byte-oriented encodings -/

/-- Equal 32-byte address serializations have equal per-field byte blocks. -/
theorem toBytes_blocks {a b : Adrs} (h : a.toBytes = b.toBytes) :
    Adrs.toBytesBE a.layer 4 = Adrs.toBytesBE b.layer 4 ∧
      Adrs.toBytesBE a.tree 12 = Adrs.toBytesBE b.tree 12 ∧
      Adrs.toBytesBE a.type 4 = Adrs.toBytesBE b.type 4 ∧
      Adrs.toBytesBE a.word1 4 = Adrs.toBytesBE b.word1 4 ∧
      Adrs.toBytesBE a.word2 4 = Adrs.toBytesBE b.word2 4 ∧
      Adrs.toBytesBE a.word3 4 = Adrs.toBytesBE b.word3 4 := by
  simp only [Adrs.toBytes] at h
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h, h1⟩ := List.append_inj h (by simp)
  obtain ⟨h, hty⟩ := List.append_inj h (by simp)
  obtain ⟨hl, ht⟩ := List.append_inj h (by simp)
  exact ⟨hl, ht, hty, h1, h2, h3⟩

/-- Equal 22-byte `ADRSc` compressions have equal per-field byte blocks. -/
theorem compressSha2_blocks {a b : Adrs} (h : a.compressSha2 = b.compressSha2) :
    Adrs.toBytesBE a.layer 1 = Adrs.toBytesBE b.layer 1 ∧
      Adrs.toBytesBE a.tree 8 = Adrs.toBytesBE b.tree 8 ∧
      Adrs.toBytesBE a.type 1 = Adrs.toBytesBE b.type 1 ∧
      Adrs.toBytesBE a.word1 4 = Adrs.toBytesBE b.word1 4 ∧
      Adrs.toBytesBE a.word2 4 = Adrs.toBytesBE b.word2 4 ∧
      Adrs.toBytesBE a.word3 4 = Adrs.toBytesBE b.word3 4 := by
  simp only [Adrs.compressSha2] at h
  obtain ⟨h, h3⟩ := List.append_inj h (by simp)
  obtain ⟨h, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h, h1⟩ := List.append_inj h (by simp)
  obtain ⟨h, hty⟩ := List.append_inj h (by simp)
  obtain ⟨hl, ht⟩ := List.append_inj h (by simp)
  exact ⟨hl, ht, hty, h1, h2, h3⟩

/-- Two addresses with the same 32-byte serialization have FORS secret-key addresses with the
same 32-byte serialization. -/
theorem toBytes_forsSkAdrs_congr {a b : Adrs} (h : a.toBytes = b.toBytes) :
    (forsSkAdrs a a.word3).toBytes = (forsSkAdrs b b.word3).toBytes := by
  obtain ⟨hl, ht, -, h1, -, h3⟩ := toBytes_blocks h
  simp only [forsSkAdrs_eq, Adrs.toBytes, hl, ht, h1, h3]

/-- Two addresses with the same 32-byte serialization have WOTS+ secret-key addresses with the
same 32-byte serialization. -/
theorem toBytes_wotsSkAdrs_congr {a b : Adrs} (h : a.toBytes = b.toBytes) :
    (wotsSkAdrs a a.word2).toBytes = (wotsSkAdrs b b.word2).toBytes := by
  obtain ⟨hl, ht, -, h1, h2, -⟩ := toBytes_blocks h
  simp only [wotsSkAdrs_eq, Adrs.toBytes, hl, ht, h1, h2]

/-- Two addresses with the same `ADRSc` compression have FORS secret-key addresses with the same
`ADRSc` compression. -/
theorem compressSha2_forsSkAdrs_congr {a b : Adrs} (h : a.compressSha2 = b.compressSha2) :
    (forsSkAdrs a a.word3).compressSha2 = (forsSkAdrs b b.word3).compressSha2 := by
  obtain ⟨hl, ht, -, h1, -, h3⟩ := compressSha2_blocks h
  simp only [forsSkAdrs_eq, Adrs.compressSha2, hl, ht, h1, h3]

/-- Two addresses with the same `ADRSc` compression have WOTS+ secret-key addresses with the same
`ADRSc` compression. -/
theorem compressSha2_wotsSkAdrs_congr {a b : Adrs} (h : a.compressSha2 = b.compressSha2) :
    (wotsSkAdrs a a.word2).compressSha2 = (wotsSkAdrs b b.word2).compressSha2 := by
  obtain ⟨hl, ht, -, h1, h2, -⟩ := compressSha2_blocks h
  simp only [wotsSkAdrs_eq, Adrs.compressSha2, hl, ht, h1, h2]

end SLHDSA.Security
