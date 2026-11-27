/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.Program
import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw
import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Encoding.ActivatedClash
import HashSig.SLHDSA.SHAKE128s.Proof.DigestTape

/-!
# Support of a projected native execution

For any fixed signer and forger tapes, a reachable native terminal projects to a result in the
support of the deferred interpreter.
-/

public section
open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open scoped ENNReal
namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
open Guarded

/-- Fixed tapes of arbitrary lengths can produce only cache states in the ordinary deferred
support. The same projection retains the key, answer, log, raw cache, payment and metadata. -/
theorem projected_mem_deferred (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (caps : Nat × Nat) (fb : (i : LabCommon.Domain) → LabCommon.Range i) (a b : List HashOutput)
    (t : NativeTerminal) (mem : t ∈ support (nativeRun s adv true caps fb a b)) :
    ((((t.1, (PUnit.unit, t.2.2)), t.2.1.1.1), t.2.1.1.2.2), t.2.1.1.2.1) ∈
        support ((simulateQ (slhGraph FIPS205.core s).deferredImpl
          (GuardedFill.labProgram s adv true true caps fb)).run ((∅, ∅), [])) := by
  have h := native_deferred_marginal s adv true caps fb a.length b.length
  rw [GuardedFill.labProgram_eq_native, ← Averaging.support_eq_of_evalDistEq h, support_map]
  refine ⟨((a, b), t), ?_, rfl⟩
  rw [NoticingTape.blockRunOf, mem_support_bind_iff]
  refine ⟨a, (DigestTape.mem_support_padding_iff _ a).2 rfl, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨b, (DigestTape.mem_support_padding_iff _ b).2 rfl, ?_⟩
  rw [support_map]
  exact ⟨t, mem, rfl⟩

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Native
