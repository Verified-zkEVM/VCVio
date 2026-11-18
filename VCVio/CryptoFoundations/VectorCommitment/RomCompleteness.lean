/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Completeness
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Completeness of vector commitments in the random oracle model

Completeness (`VectorCommitment.PerfectlyCompleteForAll`) is stated against every fixed oracle
function, while position binding and hiding are stated against the lazily sampled random oracle
`ProbCompRuntime.rom (X →ₒ Y)`. This file transfers completeness to that oracle, started from any
cache, so that a scheme's completeness and its security are stated in the same model.

An output of a computation under the lazily sampled random oracle, started from a cache, is an
output of the same computation with the oracle answered by some fixed function that agrees with
the cache (`OracleComp.exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff`). So
every output of the honest experiment under the lazy oracle is an output against a fixed function,
where it is accepted.

## Main results

* `VectorCommitment.fixedOracleImpl_eq_unifFwdAnswerImpl`: answering the oracle with a fixed
  function is `OracleComp.unifFwdAnswerImpl` at that function.
* `VectorCommitment.PerfectlyCompleteForAll.evalDist_rom_completenessExp_eq_one`: completeness
  against every fixed function gives acceptance with probability one under the lazily sampled
  random oracle, from every initial cache.
-/

public section

open OracleComp OracleSpec

namespace VectorCommitment

variable {X Y : Type}

/-- Answering the oracle with the answer table `f` is `unifFwdAnswerImpl f`: both pass the coins
through and answer every oracle query with `f`. -/
theorem fixedOracleImpl_eq_unifFwdAnswerImpl (f : QueryImpl (X →ₒ Y) Id) :
    fixedOracleImpl (fun x ↦ f x) = unifFwdAnswerImpl f := by
  ext (n | x) <;> rfl

/-- **Completeness in the random oracle model.** A scheme that is complete against every fixed
function accepts the honest opening of every message and query set with probability one under the
lazily sampled random oracle, started from any cache `cache`; the empty cache is the default of
`ProbCompRuntime.rom`. -/
theorem PerfectlyCompleteForAll.evalDist_rom_completenessExp_eq_one [DecidableEq X]
    [SampleableType Y] {Msg : Type*} {Cm Td Pf : Type} {ℓ : ℕ}
    {vc : VectorCommitment X Y Msg Cm Td Pf ℓ} {cache : (X →ₒ Y).QueryCache}
    (h : vc.PerfectlyCompleteForAll) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) :
    (ProbCompRuntime.rom (X →ₒ Y) cache).evalDist (vc.completenessExp m Q) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, prEvent_eq_one_iff]
  intro b hb
  rw [StateT.run'_eq, support_map] at hb
  obtain ⟨⟨b', s⟩, hbs, rfl⟩ := hb
  obtain ⟨f, -, hf⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff _ cache b').mpr ⟨s, hbs⟩
  exact h (fun x ↦ f x) m Q b' (by rwa [fixedOracleImpl_eq_unifFwdAnswerImpl])

end VectorCommitment
