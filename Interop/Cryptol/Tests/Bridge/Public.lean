/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Bridge

/-!
# Ordinary-import bridge canaries
-/

open Interop.Cryptol.Bridge Interop.Cryptol OracleComp

example (x : UInt32) : foundationSigma x = VCVio.Algorithms.Sha2.bsig0 x :=
  foundationSigma_eq x

example (x : UInt32) :
    (Expr.app Foundation.sigma256Zero.lower (.word x.toBitVec)).denote Environment.empty =
      .value (wordValue (VCVio.Algorithms.Sha2.bsig0 x).toBitVec) :=
  sigma256Zero_correct x

example (event : UInt32 × Nat → Prop) :
    Pr{let result ← experiment foundationSigma}[event result] =
      Pr{let result ← experiment VCVio.Algorithms.Sha2.bsig0}[event result] :=
  experiment_event_eq event

example : KeccakStatement.h2bPrefix (m := 2) (n := 14) (BitVec.ofNat 16 0xA32E) =
    fun i => (BitVec.ofNat 14 0b11000101011101).getMsbD i.val :=
  KeccakStatement.h2bTest

example (s : VCVio.Algorithms.Sha2.RoundState) (kt wt : UInt32) :
    Foundation.round256.denote Finite.Env.empty (stateBits s, kt.toBitVec, wt.toBitVec) =
      stateBits (VCVio.Algorithms.Sha2.round256 s kt wt) := round256_eq s kt wt

example (pre : RoundInput.Native → Prop) (post : RoundInput.Native → RoundOutput.Native → Prop) :
    Finite.DataContract roundInputShape (Resolved.lower Foundation.round256.source) pre post ↔
      ∀ x, pre x → post x (nativeRound x) := round_source_contract_iff pre post

example (x : CompressionInput.Native) :
    DomainResult.applyContinuous
      ((Resolved.lower compressionSourceTupled).denote Environment.empty)
      (Finite.encodeData compressionInputShape x) =
      Finite.encodeData roundOutputShape (compressionTerm.denote Finite.Env.empty x) :=
  compressionCertified.lower_apply x

example (r : CompressionRequest) : compiledCompress r = nativeCompress r :=
  compiledCompress_eq r

example (pre : CompressionInput.Native → Prop)
    (post : CompressionInput.Native → RoundOutput.Native → Prop) :
    Finite.DataContract compressionInputShape (Resolved.lower compressionSourceTupled) pre post ↔
      ∀ x, pre x → post x (compressionNative x) := compression_contract_iff pre post

example {α : Type} (program : OracleComp compressionSpec α) (state : Nat) :
    (simulateQ (compressionHandler compiledCompress) program).run state =ᵈ
      (simulateQ (compressionHandler nativeCompress) program).run state :=
  simulate_compressionHandler_eq program state
