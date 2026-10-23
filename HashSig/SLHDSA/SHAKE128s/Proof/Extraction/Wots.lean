/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Correctness.Wots
public import HashSig.SLHDSA.SHAKE128s.Proof.Hashing

/-!
# Collision extraction from WOTS verification

A changed WOTS chain value reaching the canonical endpoint has a collision at one of the
verifier's remaining chain steps (`chain_eq_or_collision`). Assembled over all chains,
`publicKey_eq_canonical_or_collision` shows that a WOTS signature recovering the genuine public
key either is the canonical signature, or has a `CompressionCollision` at the final compression
call, or a `ChainCollision` at a concrete chain step.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.Extraction.Wots

variable [HasQuery HashSpec Id]

/-- A collision at chain step `start + offset`: advancing `actual` and `canonical` by `offset`
steps gives distinct values whose next chain step hashes them to the same output. -/
def ChainCollision (publicSeed : Digest) (address : Address)
    (start : Nat) (actual canonical : Digest) (offset : Nat) : Prop :=
  let actualValue := SlhDsaSecurity.Wots.chain (m := Id) publicSeed address start offset actual
  let canonicalValue :=
    SlhDsaSecurity.Wots.chain (m := Id) publicSeed address start offset canonical
  actualValue ≠ canonicalValue ∧
    Hashing.tweakable (m := Id) publicSeed
      { address with hashOrIndex := BitVec.ofNat 32 (start + offset) } (bytesBE n actualValue) =
    Hashing.tweakable (m := Id) publicSeed
      { address with hashOrIndex := BitVec.ofNat 32 (start + offset) } (bytesBE n canonicalValue)

/-- Two chain values that reach the same endpoint are equal or collide at a concrete step. -/
theorem chain_eq_or_collision (publicSeed : Digest) (address : Address)
    (start steps : Nat) (actual canonical : Digest)
    (hend : SlhDsaSecurity.Wots.chain (m := Id) publicSeed address start steps actual =
      SlhDsaSecurity.Wots.chain (m := Id) publicSeed address start steps canonical) :
    actual = canonical ∨ ∃ offset < steps,
      ChainCollision publicSeed address start actual canonical offset := by
  classical
  induction steps generalizing start actual canonical with
  | zero => exact Or.inl hend
  | succ steps ih =>
      by_cases heq : actual = canonical
      · exact Or.inl heq
      let next : Digest → Digest := fun value => Hashing.tweakable (m := Id) publicSeed
        { address with hashOrIndex := BitVec.ofNat 32 start } (bytesBE n value)
      have hnext : SlhDsaSecurity.Wots.chain (m := Id) publicSeed address (start + 1) steps
          (next actual) =
        SlhDsaSecurity.Wots.chain (m := Id) publicSeed address (start + 1) steps
          (next canonical) := hend
      rcases ih (start + 1) (next actual) (next canonical) hnext with
        hmerge | ⟨offset, hoffset, hcollision⟩
      · exact Or.inr ⟨0, by omega, by
          simpa only [ChainCollision, SlhDsaSecurity.Wots.chain, pure, Nat.add_zero]
            using And.intro heq hmerge⟩
      · refine Or.inr ⟨offset + 1, by omega, ?_⟩
        simpa only [ChainCollision, SlhDsaSecurity.Wots.chain, bind, Nat.add_assoc,
          Nat.add_comm 1 offset, next] using hcollision

omit [HasQuery HashSpec Id] in
/-- The concatenated byte encoding of a digest array is injective. -/
theorem digestArrayBytes_injective (size : Nat) :
    Function.Injective (digestArrayBytes (size := size)) := by
  induction size with
  | zero => intro _ _ _; funext i; exact Fin.elim0 i
  | succ size ih =>
      intro left right heq
      simp only [digestArrayBytes, List.ofFn_succ, List.flatten_cons] at heq
      obtain ⟨hfirst, hrest⟩ := List.append_inj heq (by simp)
      have hfirst' := bytesBE_injective n hfirst
      have hrest' := ih hrest
      funext i
      exact Fin.cases hfirst' (fun j => congrFun hrest' j) i

/-- The chain endpoints recomputed by WOTS verification: each signature value advanced from its
message digit to the end of its chain. -/
def endpoints (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) : Fin chains → Digest := fun i =>
  SlhDsaSecurity.Wots.chain (m := Id) publicSeed
    { address with chainOrHeight := BitVec.ofNat 32 i.val }
    (Checksum.encode message i).val (w - 1 - (Checksum.encode message i).val) (signature i)

/-- WOTS public-key recovery is the compression of the recomputed chain endpoints. -/
theorem publicKeyFromSignature_eq (signature : WotsSignature) (message publicSeed : Digest)
    (address : Address) :
    SlhDsaSecurity.Wots.publicKeyFromSignature (m := Id) signature message publicSeed address =
      Hashing.tweakable (m := Id) publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
        (digestArrayBytes (endpoints signature message publicSeed address)) := by
  simp only [SlhDsaSecurity.Wots.publicKeyFromSignature, Correctness.sequenceFin_id, bind]
  rfl

/-- A collision at the final WOTS public-key compression: the two endpoint tuples give distinct
oracle inputs that hash to the same output. -/
def CompressionCollision (actual canonical : WotsSignature) (message publicSeed : Digest)
    (address : Address) : Prop :=
  let actualInput :=
    Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
      (digestArrayBytes (endpoints actual message publicSeed address))
  let canonicalInput :=
    Hashing.tweakableInput publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
      (digestArrayBytes (endpoints canonical message publicSeed address))
  actualInput ≠ canonicalInput ∧
    Hashing.shortHash (m := Id) actualInput = Hashing.shortHash (m := Id) canonicalInput

/-- A signature recovering the genuine WOTS public key either equals the
canonical signature for this message or has a collision at its compression
call or at one of its chain calls. -/
theorem publicKey_eq_canonical_or_collision (signature : WotsSignature)
    (message secretSeed publicSeed : Digest) (address : Address)
    (hpk : SlhDsaSecurity.Wots.publicKeyFromSignature (m := Id) signature message publicSeed
        address =
      SlhDsaSecurity.Wots.publicKey (m := Id) secretSeed publicSeed address) :
    let canonical : WotsSignature := SlhDsaSecurity.Wots.sign (m := Id)
      message secretSeed publicSeed address
    signature = canonical ∨ CompressionCollision signature canonical message publicSeed address ∨
      ∃ i : Fin chains, ∃ offset < w - 1 - (Checksum.encode message i).val,
        ChainCollision publicSeed { address with chainOrHeight := BitVec.ofNat 32 i.val }
          (Checksum.encode message i).val (signature i) (canonical i) offset := by
  classical
  dsimp only
  let canonical : WotsSignature := SlhDsaSecurity.Wots.sign (m := Id)
    message secretSeed publicSeed address
  have houtputs : Hashing.tweakable (m := Id) publicSeed
      (SlhDsaSecurity.Wots.publicKeyAddress address)
      (digestArrayBytes (endpoints signature message publicSeed address)) =
    Hashing.tweakable (m := Id) publicSeed (SlhDsaSecurity.Wots.publicKeyAddress address)
      (digestArrayBytes (endpoints canonical message publicSeed address)) := by
    rw [← publicKeyFromSignature_eq, ← publicKeyFromSignature_eq]
    exact hpk.trans (Correctness.Wots.publicKeyFromSignature_sign
      message secretSeed publicSeed address).symm
  by_cases hendpoints : endpoints signature message publicSeed address =
      endpoints canonical message publicSeed address
  · by_cases hsignature : signature = canonical
    · exact Or.inl hsignature
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hsignature
      have hchain := chain_eq_or_collision publicSeed
        { address with chainOrHeight := BitVec.ofNat 32 i.val }
        (Checksum.encode message i).val (w - 1 - (Checksum.encode message i).val)
        (signature i) (canonical i) (congrFun hendpoints i)
      exact Or.inr (Or.inr ⟨i, hchain.resolve_left hi⟩)
  · refine Or.inr (Or.inl ⟨?_, houtputs⟩)
    intro hinput
    exact hendpoints (digestArrayBytes_injective chains
      (Hashing.tweakableInput_injective hinput).2.2)

end SlhDsaSecurity.Extraction.Wots
