/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.CompressionSource
public import Interop.Cryptol.Bridge.CompressionTotal
public import Interop.Cryptol.Bridge.ByteCompression

/-!
# Certified SHA-256 compression and specification transfer

The certificate connects the preserved recursive Foundation source to a finite
implementation. A second theorem crosses the real byte-array boundary under
explicit size and bounds hypotheses. Both directions quantify arbitrary predicates.
-/

public section

namespace Interop.Cryptol.Bridge

open Interop.Cryptol Interop.Cryptol.Finite

/-- Tupled interface to the preserved curried source, with the source itself retained. -/
@[expose] def compressionSourceTupled : Resolved.Term []
    (.arrow CompressionInput.core RoundOutput.core) :=
  .letE Foundation.compressionSource (.lam (.app (.app (.var (.succ .zero))
    (.fst (.var .zero))) (.snd (.var .zero))))

set_option maxRecDepth 4096 in
/-- The tupled source yields the complete represented compression result. -/
theorem compressionSourceTupled_correct (x : CompressionInput.Native) :
    DomainResult.applyContinuous (Resolved.denote compressionSourceTupled Environment.empty)
      (encodeData compressionInputShape x) = encodeData roundOutputShape (compressionNative x) := by
  rw [compressionSourceTupled, Resolved.denote_letE, Resolved.denote_lam_apply]
  simp (config := { dsimp := false }) only [Resolved.denote_app, Resolved.denote_var,
    Resolved.denote_fst, Resolved.denote_snd, Environment.extend_succ]
  change DomainResult.applyContinuous (DomainResult.applyContinuous
    (Resolved.denote Foundation.compressionSource Environment.empty) (wordsMeaning x.1))
      (wordsMeaning x.2) = wordsMeaning (compressionNative x)
  rw [compressionSource_correct, compressionMeaning_value]
  rfl

/-- Kernel-checked recurrence and fold compilation for full SHA-256 compression. -/
@[expose] noncomputable def compressionCertified :
    CertifiedFunction compressionInputShape roundOutputShape where
  source := compressionSourceTupled
  implementation := compressionTerm
  correct x := by
    rw [compressionTerm_denote]
    exact compressionSourceTupled_correct x

/-- Arbitrary total specifications transfer between preserved source and native word arrays. -/
theorem compression_contract_iff (pre : CompressionInput.Native → Prop)
    (post : CompressionInput.Native → RoundOutput.Native → Prop) :
    DataContract compressionInputShape (Resolved.lower compressionSourceTupled) pre post ↔
      ∀ x, pre x → post x (compressionNative x) :=
  compressionCertified.contract_iff compressionNative compressionTerm_denote pre post

/-- A valid call of VCVio's byte-array compression function, at any offset. -/
structure CompressionRequest where
  /-- The eight chaining words in register order. -/
  state : Array UInt32
  /-- A buffer containing at least the selected block. -/
  bytes : ByteArray
  /-- Start of the 64-byte block; alignment is unrestricted. -/
  base : Nat
  /-- The state has exactly the eight words required by compression. -/
  state_size : state.size = 8
  /-- Every byte of the selected block exists. -/
  block_bounds : base + 64 ≤ bytes.size

/-- Decode the valid request to the source's word-array representation. -/
@[expose] def CompressionRequest.input (r : CompressionRequest) : CompressionInput.Native :=
  (decodedState r.state r.state_size, decodedBlock r.bytes r.base r.block_bounds)

/-- The executable finite implementation at the byte-facing interface. -/
@[expose] def compiledCompress (r : CompressionRequest) : Array UInt32 :=
  Array.ofFn (fun i => UInt32.ofBitVec (compressionTerm.denote Env.empty r.input i))

/-- The actual VCVio implementation at the same byte-facing interface. -/
@[expose] def nativeCompress (r : CompressionRequest) : Array UInt32 :=
  VCVio.Algorithms.Sha2.compress r.state r.bytes r.base

/-- The byte implementation equals the certified finite implementation on all valid requests. -/
theorem compiledCompress_eq (r : CompressionRequest) : compiledCompress r = nativeCompress r := by
  rw [compiledCompress, compressionTerm_denote]
  exact (compress_eq_decoded r.state r.bytes r.base r.state_size r.block_bounds).symm

/-- Pull or push a byte-array contract through the complete source representation. -/
theorem compression_byte_contract_iff (pre : CompressionRequest → Prop)
    (post : CompressionRequest → Array UInt32 → Prop) :
    (∀ r, pre r → ∃ y : RoundOutput.Native,
      Represents RoundOutput y (DomainResult.applyContinuous
        ((Resolved.lower compressionSourceTupled).denote Environment.empty)
        (encodeData compressionInputShape r.input)) ∧
      post r (Array.ofFn (fun i => UInt32.ofBitVec (y i)))) ↔
    ∀ r, pre r → post r (nativeCompress r) := by
  have hr (r : CompressionRequest) : Represents RoundOutput
      (compressionTerm.denote Env.empty r.input)
      (DomainResult.applyContinuous ((Resolved.lower compressionSourceTupled).denote
        Environment.empty) (encodeData compressionInputShape r.input)) := by
    change Represents RoundOutput (compressionTerm.denote Env.empty r.input)
      (DomainResult.applyContinuous ((Resolved.lower compressionCertified.source).denote
        Environment.empty) (encodeData compressionInputShape r.input))
    rw [compressionCertified.lower_apply]
    exact represents_encodeData roundOutputShape _
  constructor
  · intro h r hp
    obtain ⟨y, hy, hpost⟩ := h r hp
    have he := Represents.functional roundOutputShape hy (hr r)
    rw [he] at hpost
    exact (compiledCompress_eq r) ▸ hpost
  · intro h r hp
    refine ⟨_, hr r, ?_⟩
    change post r (compiledCompress r)
    rw [compiledCompress_eq]
    exact h r hp

end Interop.Cryptol.Bridge
