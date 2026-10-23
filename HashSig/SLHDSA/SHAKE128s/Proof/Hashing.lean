/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment

/-!
# Injectivity of the hash input encodings

The byte encodings fed to the hash are injective: big-endian byte strings (`bytesBE_injective`),
ADRS addresses (`Address.toBytes_injective`), the inputs of `PRF_msg`, `H_msg` and the tweakable
hashes (`Hashing.randomizerInput_injective`, `Hashing.messageInput_injective`,
`Hashing.tweakableInput_injective`), and the pure-mode message framing
(`Message.frame_injective`). Distinct hash calls therefore query the random oracle at distinct
points.
-/

@[expose] public section

namespace SlhDsaSecurity

/-- The big-endian encoding of a `count`-byte value has `count` bytes. -/
@[simp] theorem length_bytesBE (count : Nat) (value : BitVec (8 * count)) :
    (bytesBE count value).length = count := by simp [bytesBE]

/-- The big-endian byte encoding is injective. -/
theorem bytesBE_injective (count : Nat) : Function.Injective (bytesBE count) := by
  intro left right heq
  have hbytes := List.ofFn_injective (List.reverse_inj.mp heq)
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let byte : Fin count := ⟨bit / 8, by omega⟩
  have hbyte := congrArg UInt8.toBitVec (congrFun hbytes byte)
  have hlocal := congrArg (fun value => value.getLsbD (bit % 8)) hbyte
  have hmod : bit % 8 < 8 := Nat.mod_lt bit (by omega)
  have hposition : 8 * (bit / 8) + bit % 8 = bit := by omega
  simpa [byte, BitVec.getLsbD_extractLsb', hmod, hposition] using hlocal

/-- Distinct address types have distinct codes. -/
theorem AddressType.code_injective : Function.Injective AddressType.code := by
  intro left right h
  cases left <;> cases right <;> simp_all [AddressType.code]

/-- An encoded address is 32 bytes long. -/
@[simp] theorem Address.toBytes_length (address : Address) : address.toBytes.length = 32 := by
  simp [Address.toBytes]

/-- The byte encoding of addresses is injective. -/
theorem Address.toBytes_injective : Function.Injective Address.toBytes := by
  intro left right heq
  simp only [Address.toBytes] at heq
  obtain ⟨hfront, hlast⟩ := List.append_inj heq (by simp)
  obtain ⟨hfront, hheight⟩ := List.append_inj hfront (by simp)
  obtain ⟨hfront, hkey⟩ := List.append_inj hfront (by simp)
  obtain ⟨hfront, hkind⟩ := List.append_inj hfront (by simp)
  obtain ⟨hlayer, htree⟩ := List.append_inj hfront (by simp)
  have := bytesBE_injective 4 hlayer
  have := bytesBE_injective 12 htree
  have := AddressType.code_injective (bytesBE_injective 4 hkind)
  have := bytesBE_injective 4 hkey
  have := bytesBE_injective 4 hheight
  have := bytesBE_injective 4 hlast
  cases left
  cases right
  simp_all

namespace Hashing

/-- The `PRF_msg` input determines its key, seed and message. -/
theorem randomizerInput_injective {prf prf' seed seed' : Digest} {message message' : Bytes}
    (h : randomizerInput prf seed message = randomizerInput prf' seed' message') :
    prf = prf' ∧ seed = seed' ∧ message = message' := by
  unfold randomizerInput at h
  obtain ⟨hprefix, hmessage⟩ := List.append_inj h (by simp)
  obtain ⟨hprf, hseed⟩ := List.append_inj hprefix (by simp)
  exact ⟨bytesBE_injective n hprf, bytesBE_injective n hseed, hmessage⟩

/-- The `H_msg` input determines its randomizer, public key and message. -/
theorem messageInput_injective {randomizer randomizer' : Digest} {pk pk' : PublicKey}
    {message message' : Bytes}
    (h : messageInput randomizer pk message = messageInput randomizer' pk' message') :
    randomizer = randomizer' ∧ pk = pk' ∧ message = message' := by
  unfold messageInput at h
  obtain ⟨hprefix, hmessage⟩ := List.append_inj h (by simp)
  obtain ⟨hprefix, hroot⟩ := List.append_inj hprefix (by simp)
  obtain ⟨hrandomizer, hseed⟩ := List.append_inj hprefix (by simp)
  refine ⟨bytesBE_injective n hrandomizer, ?_, hmessage⟩
  have := bytesBE_injective n hroot
  have := bytesBE_injective n hseed
  cases pk
  cases pk'
  simp_all

/-- The tweakable-hash input determines its public seed, address and payload. -/
theorem tweakableInput_injective {seed seed' : Digest} {address address' : Address}
    {payload payload' : Bytes}
    (h : tweakableInput seed address payload = tweakableInput seed' address' payload') :
    seed = seed' ∧ address = address' ∧ payload = payload' := by
  unfold tweakableInput at h
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp)
  obtain ⟨hseed, haddress⟩ := List.append_inj hprefix (by simp)
  exact ⟨bytesBE_injective n hseed, Address.toBytes_injective haddress, hpayload⟩

end Hashing

/-- Successful framing preserves both the context and the message. -/
theorem Message.frame_injective {left right : Message} {framed : Bytes}
    (hleft : left.frame = some framed) (hright : right.frame = some framed) : left = right := by
  unfold Message.frame at hleft hright
  split at hleft <;> rename_i hl
  · split at hright <;> rename_i hr
    · have h := (Option.some.inj hleft).trans (Option.some.inj hright).symm
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
      obtain ⟨hlen, htail⟩ := h
      have hnat := congrArg UInt8.toNat hlen
      have hlength : left.context.length = right.context.length := by
        simpa only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show left.context.length < 256 by omega),
          Nat.mod_eq_of_lt (show right.context.length < 256 by omega)] using hnat
      obtain ⟨hcontext, hmessage⟩ := List.append_inj htail hlength
      cases left
      cases right
      simp_all
    · cases hright
  · cases hleft

end SlhDsaSecurity
