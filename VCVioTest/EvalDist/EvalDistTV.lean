/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Positivity
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.ProbComp.Basic

/-!
# Event-keyed total variation regressions

The event-keyed distance `etvDist` bounds every event, contracts under post-processing and
sequencing, vanishes exactly on computations equal in distribution (in any two monads), and
agrees with the measure-level distance on a discrete output space. Its real form `tvDist` is
nonnegative by `positivity`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace VCVioTest.EvalDistTV

variable {α β : Type}

example (mx my : ProbComp α) (p : α → Prop) :
    ENNReal.absDiff Pr{let x ← mx}[p x] Pr{let y ← my}[p y] ≤ etvDist mx my :=
  absDiff_prEvent_le_etvDist mx my p

example (mx my : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← my}[p y] + etvDist mx my :=
  prEvent_le_prEvent_add_etvDist mx my p

/-- The distance is keyed on events, so the two computations may live in different monads. -/
example (mx : ProbComp α) (my : OptionT ProbComp α) : etvDist mx my = 0 ↔ mx =ᵈ my :=
  etvDist_eq_zero_iff mx my

example (mx my : ProbComp α) (f : α → β) : etvDist (f <$> mx) (f <$> my) ≤ etvDist mx my :=
  etvDist_map_le mx my f

example (mx my : ProbComp α) (f : α → ProbComp β) :
    etvDist (mx >>= f) (my >>= f) ≤ etvDist mx my :=
  etvDist_bind_le mx my f

/-- Continuations of a shared prefix are within the expected pointwise distance. -/
example (mx : ProbComp α) (f g : α → ProbComp β) (bound : α → ℝ≥0∞)
    (h : ∀ a, etvDist (f a) (g a) ≤ bound a) :
    etvDist (mx >>= f) (mx >>= g) ≤ wp⟦mx⟧ bound :=
  etvDist_bind_bind_le_wp mx f g bound h

/-- On a discrete output space the event-keyed distance is the measure-level one. -/
example [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx my : ProbComp α) :
    etvDist mx my = measureETVDist mx my :=
  etvDist_eq_measureETVDist mx my

/-- On any σ-algebra the measure-level distance is at most the event-keyed one. -/
example [MeasurableSpace α] (mx my : ProbComp α) : measureETVDist mx my ≤ etvDist mx my :=
  measureETVDist_le_etvDist mx my

example (mx my : ProbComp α) : 0 ≤ tvDist mx my := by positivity

example (mx my : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] ≤ Pr{let y ← my}[p y] + ENNReal.ofReal (tvDist mx my) :=
  prEvent_le_prEvent_add_ofReal_tvDist mx my p

/-- A hybrid chain is within the sum of its steps' distances. -/
example (f : ℕ → ProbComp α) (n : ℕ) :
    etvDist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, etvDist (f i) (f (i + 1)) :=
  etvDist_le_sum_etvDist_succ f n

/-- Steps each within `ε` end within `n * ε`. -/
example (f : ℕ → ProbComp α) (n : ℕ) (ε : ℝ≥0∞)
    (h : ∀ i < n, etvDist (f i) (f (i + 1)) ≤ ε) : etvDist (f 0) (f n) ≤ n * ε :=
  etvDist_le_of_forall_etvDist_succ_le f n ε h

/-- The real distance of a chain is within the sum of its steps' real distances. -/
example (f : ℕ → ProbComp α) (n : ℕ) :
    tvDist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, tvDist (f i) (f (i + 1)) :=
  tvDist_le_sum_tvDist_succ f n

/-- Two sequences are within the distance of their prefixes plus the expected distance of the
continuations, on the support of the second prefix. -/
example (mx my : ProbComp α) (f g : α → ProbComp β) (bound : α → ℝ≥0∞)
    (h : ∀ a ∈ support my, etvDist (f a) (g a) ≤ bound a) :
    etvDist (mx >>= f) (my >>= g) ≤ etvDist mx my + wp⟦my⟧ bound :=
  etvDist_bind_bind_le_add_wp_of_support mx my f g bound h

end VCVioTest.EvalDistTV
