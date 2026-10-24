/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Hashing
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Message inputs versus bounded structural addresses

The address bounds below overapproximate the standard 128s tree and chain ranges.
If PK.seed and PK.root are independently uniform, the probability that their
concatenation can be such an address is at most 2^-165. Establishing that key
distribution, and proving that every honest structural address satisfies these
bounds, are separate obligations; neither is assumed as a security theorem here.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.HashSeparation

/-- Loose power-of-two bounds enclosing the standard 128s structural addresses. -/
@[expose] def WithinBounds (address : Address) : Prop :=
  address.layer.toNat < 2 ^ 3 ∧ address.tree.toNat < 2 ^ 54 ∧
  address.keyPair.toNat < 2 ^ 9 ∧ address.chainOrHeight.toNat < 2 ^ 6 ∧
  address.hashOrIndex.toNat < 2 ^ 16

/-- The field widths of a bounded address: layer, tree, type code, key pair, chain or height,
and hash or index. It includes the unused type code 7 and a few unused indices, to keep counting
simple. -/
abbrev Prefix := BitVec 3 × BitVec 54 × BitVec 3 × BitVec 9 × BitVec 6 × BitVec 16

/-- The byte encoding of a bounded address, each field zero-extended to its full width. -/
@[expose] def prefixBytes (parts : Prefix) : Bytes :=
  bytesBE 4 (parts.1.setWidth 32) ++ bytesBE 12 (parts.2.1.setWidth 96) ++
    bytesBE 4 (parts.2.2.1.setWidth 32) ++ bytesBE 4 (parts.2.2.2.1.setWidth 32) ++
    bytesBE 4 (parts.2.2.2.2.1.setWidth 32) ++ bytesBE 4 (parts.2.2.2.2.2.setWidth 32)

/-- The concatenated bytes of a public seed and public root. -/
@[expose] def publicBytes (pair : Digest × Digest) : Bytes := bytesBE n pair.1 ++ bytesBE n pair.2

/-- A public seed and root whose concatenation is the encoding of some bounded address. -/
@[expose] def Possible (pair : Digest × Digest) : Prop :=
  ∃ parts : Prefix, publicBytes pair = prefixBytes parts

private theorem restore_width {wide narrow : Nat} (value : BitVec wide)
    (h : value.toNat < 2 ^ narrow) : (value.setWidth narrow).setWidth wide = value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt value.isLt]

/-- Every address within the bounds is encoded as some `Prefix`. -/
theorem bounded_address_has_prefix (address : Address) (h : WithinBounds address) :
    ∃ parts : Prefix, address.toBytes = prefixBytes parts := by
  have hkind : address.kind.code.toNat < 2 ^ 3 := by cases address.kind <;> decide
  refine ⟨(address.layer.setWidth 3, address.tree.setWidth 54, address.kind.code.setWidth 3,
    address.keyPair.setWidth 9, address.chainOrHeight.setWidth 6,
    address.hashOrIndex.setWidth 16), ?_⟩
  simp only [prefixBytes, restore_width _ h.1, restore_width _ h.2.1, restore_width _ hkind,
    restore_width _ h.2.2.1, restore_width _ h.2.2.2.1, restore_width _ h.2.2.2.2]
  rfl

/-- An overlap forces the public seed and root to form the structural address. -/
theorem message_tweakable_overlap {randomizer seed : Digest} {pk : PublicKey}
    {message payload : Bytes} {address : Address}
    (h : Hashing.messageInput randomizer pk message = Hashing.tweakableInput seed address payload) :
    randomizer = seed ∧ publicBytes (pk.seed, pk.root) = address.toBytes ∧ message = payload := by
  have heq : bytesBE n randomizer ++ ((bytesBE n pk.seed ++ bytesBE n pk.root) ++ message) =
      bytesBE n seed ++ (address.toBytes ++ payload) := by
    simpa only [Hashing.messageInput, Hashing.tweakableInput, List.append_assoc] using h
  obtain ⟨hrandomizer, hrest⟩ := List.append_inj heq (by simp)
  obtain ⟨haddress, hmessage⟩ := List.append_inj hrest
    (by rw [List.length_append, length_bytesBE, length_bytesBE]; simp [n])
  exact ⟨bytesBE_injective n hrandomizer, haddress, hmessage⟩

/-- A message input never equals a tweakable input at a bounded address, unless the public seed
and root are `Possible`. -/
theorem message_tweakable_ne {randomizer seed : Digest} {pk : PublicKey}
    {message payload : Bytes} {address : Address}
    (hpublic : ¬Possible (pk.seed, pk.root)) (haddress : WithinBounds address) :
    Hashing.messageInput randomizer pk message ≠ Hashing.tweakableInput seed address payload := by
  intro heq
  obtain ⟨parts, hprefix⟩ := bounded_address_has_prefix address haddress
  exact hpublic ⟨parts, (message_tweakable_overlap heq).2.1.trans hprefix⟩

/-- PRF_msg and structural hashing are disjoint whenever their first seed blocks differ. -/
theorem randomizer_tweakable_ne {prf seed publicSeed : Digest}
    {message payload : Bytes} {address : Address} (hne : prf ≠ publicSeed) :
    Hashing.randomizerInput prf seed message ≠
      Hashing.tweakableInput publicSeed address payload := by
  intro heq
  have h : bytesBE n prf ++ (bytesBE n seed ++ message) =
      bytesBE n publicSeed ++ (address.toBytes ++ payload) := by
    simpa only [Hashing.randomizerInput, Hashing.tweakableInput, List.append_assoc] using heq
  exact hne (bytesBE_injective n (List.append_inj h (by simp)).1)

/-- `publicBytes` is injective. -/
theorem publicBytes_injective : Function.Injective publicBytes := by
  rintro ⟨seed, root⟩ ⟨seed', root'⟩ h
  obtain ⟨hseed, hroot⟩ := List.append_inj h (by simp)
  exact Prod.ext (bytesBE_injective n hseed) (bytesBE_injective n hroot)

/-- A uniform seed and root hit any fixed byte string with probability at most `2 ^ -256`. -/
theorem prob_publicBytes_eq_le (target : Bytes) :
    Pr{let pair ← ($ᵗ (Digest × Digest) : ProbComp _)}[publicBytes pair = target] ≤
      1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  refine (SampleableType.prEvent_uniformSample_apply_eq_le publicBytes_injective target).trans
    (le_of_eq ?_)
  have hsize : Fintype.card (Digest × Digest) = 2 ^ 256 := by
    norm_num [Digest, n, Fintype.card_prod, Fintype.card_bitVec]
  rw [Nat.card_eq_fintype_card, hsize, one_div]

/-- A distributional input-separation bound, before connecting it to key generation. -/
theorem prob_possible_le :
    Pr{let x ← ($ᵗ (Digest × Digest) : ProbComp _)}[Possible x] ≤
      1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prEvent_exists_le_card_mul _
    (fun (parts : Prefix) (pair : Digest × Digest) => publicBytes pair = prefixBytes parts)
    fun parts => prob_publicBytes_eq_le (prefixBytes parts)) ?_
  have hcard : Fintype.card Prefix = 2 ^ 91 := by
    norm_num [Prefix, Fintype.card_prod, Fintype.card_bitVec]
  rw [hcard]
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

end SLHDSA.SHAKE128s.HashSeparation
