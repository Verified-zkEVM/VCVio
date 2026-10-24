/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.OpenCache
public import HashSig.SLHDSA.SHAKE128s.Proof.StalledRun
public import HashSig.SLHDSA.SHAKE128s.Proof.CacheAvailability
public import HashSig.SLHDSA.SHAKE128s.Proof.LazyBridge

/-!
# Exchanging a finite sum and an expectation

The only result here is `sum_tsum_comm`, the exchange of a finite sum over cells with an
expectation over run results, used when per-cell charges are summed under one measure.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ChargedProbe

open CanonicalGraph SensitiveQuery OpenCache

variable {Node : Type}

/-- **A finite sum and an expectation may be exchanged.** Over `ℝ≥0∞` both sides are defined and
equal whatever the summands; it is stated for an arbitrary index set because this is the step at
which a factor of the index count would hide, and a general statement is easier to check than
one specialised to a type with `2 ^ 26` elements. -/
theorem sum_tsum_comm {Index Result : Type} (nodes : Finset Index)
    (summand : Index → Result → ℝ≥0∞) :
    ∑ index ∈ nodes, ∑' result : Result, summand index result =
      ∑' result : Result, ∑ index ∈ nodes, summand index result := by
  classical
  refine Finset.induction_on nodes ?_ ?_
  · simp
  · intro head rest hhead ih
    rw [Finset.sum_insert hhead, ih, ← ENNReal.tsum_add]
    exact tsum_congr fun result => by rw [Finset.sum_insert hhead]

variable (publicSeed : Digest)

end SlhDsaSecurity.ChargedProbe
