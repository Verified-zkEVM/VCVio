/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Completeness
public import VCVio.OracleComp.QueryTracking.RandomOracle.ExpectedFreshQueryInfinite

/-!
# Completeness of vector commitments in the random oracle model

Completeness (`VectorCommitment.PerfectlyCompleteForAll`) is stated against every fixed oracle
function, while position binding and hiding are stated against the lazily sampled random oracle
`ProbCompRuntime.rom (X →ₒ Y)`. This file transfers completeness to that oracle, so that a scheme's
completeness and its security are stated in the same model.

Every realized lazy execution also arises in an execution against a fixed table
(`OracleComp.mem_support_fixedTableLoggedRun_of_randomOracle`), and caching a fixed table changes no
answer (`OracleComp.mem_support_simulateQ_of_mem_support_fixedTableLoggedRun`). So every output of
the honest experiment under the lazy oracle is an output against some fixed function, where it is
accepted.

## Main results

* `VectorCommitment.PerfectlyCompleteForAll.evalDist_rom_completenessExp`: completeness against
  every fixed function gives acceptance with probability one under the lazily sampled random
  oracle.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe uM

namespace VectorCommitment

variable {X Y : Type} [DecidableEq X]

/-- **Completeness in the random oracle model.** A scheme that is complete against every fixed
function accepts the honest opening of every message and query set with probability one under the
lazily sampled random oracle. -/
theorem PerfectlyCompleteForAll.evalDist_rom_completenessExp [SampleableType Y]
    {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ} {vc : VectorCommitment X Y Msg Cm Td Pf ℓ}
    (h : vc.PerfectlyCompleteForAll) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)) :
    (ProbCompRuntime.rom (X →ₒ Y)).evalDist (vc.completenessExp m Q) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton, prEvent_eq_one_iff]
  intro b hb
  rw [StateT.run'_eq, support_map] at hb
  obtain ⟨⟨b', s⟩, hbs, rfl⟩ := hb
  rw [← randomOracleLoggedRun_project, support_map] at hbs
  obtain ⟨z, hz, hzeq⟩ := hbs
  obtain ⟨g, hg⟩ := mem_support_fixedTableLoggedRun_of_randomOracle _ ∅ z hz
  have hfix := mem_support_simulateQ_of_mem_support_fixedTableLoggedRun _ g ∅ (by simp) z hg
  rw [show z.1.1 = b' from congrArg Prod.fst hzeq] at hfix
  exact h g m Q b' hfix

end VectorCommitment
