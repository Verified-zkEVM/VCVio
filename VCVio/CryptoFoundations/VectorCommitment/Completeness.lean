/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Basic
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Completeness of vector commitments

Perfect completeness (Chiesa, Di, Hu and Zheng, ePrint 2025/2166, Def 3.7) is relative to a
distribution `D` on oracle functions, a probability measure on `X → Y`
(`VectorCommitment.PerfectlyComplete`): the honest experiment accepts with probability `1` when the
oracle is sampled from `D`. Completeness against every fixed function
(`VectorCommitment.PerfectlyCompleteForAll`, and `DetVectorCommitment.PerfectlyComplete` for a
deterministic scheme) is a sufficient condition for every `D`.

## Main definitions

* `VectorCommitment.completenessExp`, `VectorCommitment.completenessProb`,
  `VectorCommitment.PerfectlyComplete` and `VectorCommitment.PerfectlyCompleteForAll`.
* `DetVectorCommitment.PerfectlyComplete`.

## Main results

* `VectorCommitment.PerfectlyCompleteForAll.perfectlyComplete`: completeness against every fixed
  function gives Def 3.7 for every oracle distribution.
* `VectorCommitment.perfectlyComplete_iff`: Def 3.7 holds for `D` exactly when the honest
  experiment accepts on every outcome, for `D`-almost every function.
* `DetVectorCommitment.PerfectlyComplete.toVectorCommitment`: the same sufficient condition for a
  deterministic scheme.
-/

public section

open OracleComp OracleSpec MeasureTheory

universe uX uM

namespace VectorCommitment

variable {X : Type uX} {Y : Type} {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ}

/-- The experiment of Def 3.7 (p. 27) for a message `m` and a query set `Q`, with the oracle
left abstract: `(cm, td) ← Commit^f(m)`, `pf ← Open(Q, td)`, and return
`Check^f(cm, Q, m[Q], pf)`. -/
@[expose]
def completenessExp (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (m : Fin ℓ → Msg)
    (Q : Finset (Fin ℓ)) : OracleComp (unifSpec + (X →ₒ Y)) Bool := do
  let z ← vc.commit m
  let pf ← liftComp (vc.opening Q z.2) (unifSpec + (X →ₒ Y))
  vc.check z.1 (PartialVec.restrict m Q) pf

/-- The acceptance probability of the experiment of Def 3.7 (p. 27) when the oracle is
sampled from the measure `D` on functions,
`Pr[Check^f(cm, Q, m[Q], pf) = 1 : f ← D, (cm, td) ← Commit^f(m), pf ← Open(Q, td)]`, extended to
an arbitrary measurable space on `X → Y` as the lower integral over `D` of the acceptance
probability against each fixed function. The integrand need not be measurable, and the lower
integral then may undercount: with the indiscrete σ-algebra on `Unit → Bool`, `D` the Dirac
measure at `fun _ ↦ true`, and a check that returns the oracle answer, the value is `0` although
the experiment against that function accepts. When the integrand is measurable, for example on a
countable function space with the discrete σ-algebra, the value is the operational acceptance
probability. `perfectlyComplete_iff` characterizes the value `1` without any measurability. -/
@[expose]
noncomputable def completenessProb [MeasurableSpace (X → Y)]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (D : Measure (X → Y)) (m : Fin ℓ → Msg)
    (Q : Finset (Fin ℓ)) : ENNReal :=
  ∫⁻ H, Pr{let b ← simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)}[b = true] ∂D

/-- **Perfect completeness** in the `D`-oracle model (ePrint 2025/2166, Def 3.7, p. 27):
for every message `m` and every query set `Q`, the experiment accepts with probability `1` when
the oracle is sampled from `D`. `D` is meant to be a probability measure. -/
@[expose]
def PerfectlyComplete [MeasurableSpace (X → Y)] (vc : VectorCommitment X Y Msg Cm Td Pf ℓ)
    (D : Measure (X → Y)) : Prop :=
  ∀ (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)), vc.completenessProb D m Q = 1

/-- Perfect completeness against every fixed function `H`: for every message and query set, every
outcome of the experiment with the oracle answered by `H` accepts. It implies Def 3.7 for every
oracle distribution (`PerfectlyCompleteForAll.perfectlyComplete`). -/
@[expose]
def PerfectlyCompleteForAll (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) : Prop :=
  ∀ (H : X → Y) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)),
    ∀ b ∈ support (simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)), b = true

/-- Def 3.7 holds for a probability measure `D` exactly when, for every message and query set and
for `D`-almost every function `H`, every outcome of the experiment with the oracle answered by `H`
accepts. No measurability of the acceptance probability in `H` is needed. -/
theorem perfectlyComplete_iff [MeasurableSpace (X → Y)]
    (vc : VectorCommitment X Y Msg Cm Td Pf ℓ) (D : Measure (X → Y)) [IsProbabilityMeasure D] :
    vc.PerfectlyComplete D ↔ ∀ (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)), ∀ᵐ H ∂D,
      ∀ b ∈ support (simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)), b = true := by
  refine forall₂_congr fun m Q ↦ ?_
  set p : (X → Y) → ENNReal :=
    fun H ↦ Pr{let b ← simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)}[b = true]
  have hp : ∀ H, p H = 1 ↔
      ∀ b ∈ support (simulateQ (fixedOracleImpl H) (vc.completenessExp m Q)), b = true :=
    fun H ↦ prEvent_eq_one_iff _ _
  have hle : ∀ H, p H ≤ 1 := fun H ↦ prEvent_le_one _
  change ∫⁻ H, p H ∂D = 1 ↔ _
  constructor
  · intro h
    obtain ⟨g, hg, hgp, hint⟩ := exists_measurable_le_lintegral_eq D p
    have hg1 : g =ᵐ[D] fun _ ↦ 1 :=
      ae_eq_of_ae_le_of_lintegral_le (Filter.Eventually.of_forall fun H ↦ (hgp H).trans (hle H))
        (by rw [← hint, h]; exact ENNReal.one_ne_top) aemeasurable_const
        (by rw [← hint, h, lintegral_const, measure_univ, mul_one])
    filter_upwards [hg1] with H hH
    exact (hp H).mp (le_antisymm (hle H) (hH ▸ hgp H))
  · intro h
    rw [lintegral_congr_ae (h.mono fun H hH ↦ (hp H).mpr hH), lintegral_const, measure_univ,
      mul_one]

/-- Completeness against every fixed function gives Def 3.7 for every oracle distribution `D`. -/
theorem PerfectlyCompleteForAll.perfectlyComplete [MeasurableSpace (X → Y)]
    {vc : VectorCommitment X Y Msg Cm Td Pf ℓ} (h : vc.PerfectlyCompleteForAll)
    (D : Measure (X → Y)) [IsProbabilityMeasure D] : vc.PerfectlyComplete D :=
  (perfectlyComplete_iff vc D).mpr fun m Q ↦ Filter.Eventually.of_forall fun H ↦ h H m Q

end VectorCommitment

namespace DetVectorCommitment

variable {X : Type uX} {Y : Type} {Msg : Type uM} {Cm Td Pf : Type} {ℓ : ℕ}

/-- Perfect completeness of a deterministic scheme against every fixed function `H`
(ePrint 2025/2166, Def 3.7, p. 27): for every message `m`, every query set `Q` and every outcome
of `Commit^H(m)`, the honest opening of `Q` passes `Check^H` on `m[Q]`. It implies Def 3.7 for
every oracle distribution (`PerfectlyComplete.toVectorCommitment`). -/
@[expose]
def PerfectlyComplete (vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ) : Prop :=
  ∀ (H : X → Y) (m : Fin ℓ → Msg) (Q : Finset (Fin ℓ)),
    ∀ z ∈ support (simulateQ (VectorCommitment.fixedOracleImpl H) (vc.commit m)),
      evalWithAnswerFn (QueryImpl.ofFn H)
        (vc.check z.1 (PartialVec.restrict m Q) (vc.opening Q z.2)) = true

/-- Pointwise completeness of a deterministic scheme is pointwise completeness of its general
form. -/
theorem PerfectlyComplete.perfectlyCompleteForAll {vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ}
    (h : vc.PerfectlyComplete) : vc.toVectorCommitment.PerfectlyCompleteForAll := by
  intro H m Q b hb
  simp only [VectorCommitment.completenessExp, toVectorCommitment, simulateQ_bind] at hb
  rw [mem_support_bind_iff] at hb
  obtain ⟨z, hz, hb⟩ := hb
  rw [liftComp_pure, simulateQ_pure, pure_bind,
    VectorCommitment.simulateQ_fixedOracleImpl_liftComp, support_pure,
    Set.mem_singleton_iff] at hb
  exact hb ▸ h H m Q z hz

/-- **Perfect completeness relative to every oracle distribution** (Def 3.7, p. 27) of a
deterministic scheme that is complete against every fixed function. -/
theorem PerfectlyComplete.toVectorCommitment [MeasurableSpace (X → Y)]
    {vc : DetVectorCommitment X Y Msg Cm Td Pf ℓ} (h : vc.PerfectlyComplete)
    (D : Measure (X → Y)) [IsProbabilityMeasure D] : vc.toVectorCommitment.PerfectlyComplete D :=
  h.perfectlyCompleteForAll.perfectlyComplete D

end DetVectorCommitment
