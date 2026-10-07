/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Two-phase potential bound checks

A guessing oracle answers each query with a uniform element of `Fin 4` and records whether `0`
has been drawn and how many answers have been drawn.  Charging `4⁻¹` per answer, the two-phase
bound `OracleComp.prEvent_bind_run_and_le_of_potential` bounds a run followed by a second run by
`K` for the event "`0` was drawn with at most `4 * K` answers".  Two checks protect it:

* with one query in each phase the bound is `2⁻¹`, so it is not vacuous;
* with no query in the first phase and one in the second, the event the bound `4⁻¹` is about
  has probability exactly `4⁻¹`, so the firing mass of the terminal phase is charged rather than
  discarded.

A second phase on a different state type exercises a non-identity handover.  A coin oracle on
`Bool` keeps a hit flag, a count of handed-over answers charged `4⁻¹` each, and a count of drawn
coins charged `2⁻¹` each.  The handover passes on the guessing oracle's flag and count and starts
with no coin drawn, so one budget covers a draw of `0` in the first phase and a draw of `true` in
the second.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace TwoPhaseToy

/-- One query with answers in `Fin 4`. -/
abbrev spec : OracleSpec Unit := Unit →ₒ Fin 4

/-- The state update of a draw: whether `0` has been drawn, and how many answers have been
drawn. -/
def update (s : Bool × ℕ) (u : Fin 4) : Bool × ℕ := (s.1 || decide (u = 0), s.2 + 1)

/-- A guessing oracle answering with a uniform element of `Fin 4`. -/
def guessImpl : QueryImpl spec (StateT (Bool × ℕ) ProbComp) := fun _ =>
  StateT.mk fun s => (fun u => (u, update s u)) <$> ($ᵗ Fin 4)

/-- The potential: `4⁻¹` per drawn answer. -/
noncomputable def potential (s : Bool × ℕ) : ℝ≥0∞ := s.2 * 4⁻¹

/-- A uniform draw from `Fin 4` hits `0` with probability `4⁻¹`. -/
theorem prEvent_uniformSample_eq_zero :
    Pr{let u ← ($ᵗ Fin 4 : ProbComp (Fin 4))}[u = 0] = 4⁻¹ := by
  rw [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton,
    Fintype.card_fin, Nat.cast_ofNat]

/-- A draw never lowers the potential. -/
theorem potential_le_of_mem_support (t : spec.Domain) (s : Bool × ℕ) :
    ∀ z ∈ support ((guessImpl t).run s), potential s ≤ potential z.2 := by
  intro z hz
  change z ∈ support ((fun u => (u, update s u)) <$> ($ᵗ Fin 4)) at hz
  rw [support_map] at hz
  obtain ⟨u, -, rfl⟩ := hz
  unfold potential update
  gcongr
  exact Nat.le_succ _

/-- The guessing oracle charges drawing `0` to the potential: no draw lowers it, and out of a
state where `0` has not been drawn a draw is a uniform sample that draws `0` with probability
`4⁻¹` and raises the potential by `4⁻¹`. -/
theorem isPotentialStep : IsPotentialStep guessImpl (fun s => s.1 = true) potential where
  mono := potential_le_of_mem_support
  step _ s hs := by
    refine Or.inr ⟨$ᵗ Fin 4, update s, 4⁻¹, rfl, ?_, fun u => ?_⟩
    · rw [Bool.not_eq_true] at hs
      simp only [update, hs, Bool.false_or, decide_eq_true_eq]
      exact prEvent_uniformSample_eq_zero.le
    · simp only [potential, update, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm,
        le_refl]

/-- The two-phase bound for the guessing oracle: a run of `oa` followed by a run of `ob z` from
the first run's final state draws `0` within `4 * K` answers with probability at most `K`. -/
theorem prEvent_twoPhase_le {α β : Type} (oa : OracleComp spec α)
    (ob : α × (Bool × ℕ) → OracleComp spec β) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Pr{
      let z ← (simulateQ guessImpl oa).run (false, 0)
      let y ← (simulateQ guessImpl (ob z)).run z.2}[
        y.2.1 = true ∧ potential y.2 ≤ K] ≤ K := by
  have h := prEvent_bind_run_and_le_of_potential isPotentialStep isPotentialStep Prod.snd
    (fun _ h => h) (fun _ => le_rfl) oa ob K hK (false, 0) Bool.false_ne_true
  simpa only [potential, Nat.cast_zero, zero_mul, tsub_zero] using h

/-- A single query. -/
def guess : OracleComp spec (Fin 4) := liftM (spec.query ())

/-- With one query in each phase the two-phase bound is `2⁻¹ < 1`. -/
example :
    Pr{
      let z ← (simulateQ guessImpl guess).run (false, 0)
      let y ← (simulateQ guessImpl guess).run z.2}[y.2.1 = true ∧ potential y.2 ≤ 2⁻¹] ≤ 2⁻¹ :=
  prEvent_twoPhase_le guess (fun _ => guess) 2⁻¹ (by simp)

/-- With no query in the first phase, the second phase alone draws `0` within one answer with
probability exactly `4⁻¹`. -/
theorem prEvent_terminal_fire_and_le_eq :
    Pr{
      let z ← (simulateQ guessImpl (pure () : OracleComp spec Unit)).run (false, 0)
      let y ← (simulateQ guessImpl guess).run z.2}[
        y.2.1 = true ∧ potential y.2 ≤ 4⁻¹] = 4⁻¹ := by
  simp only [simulateQ_pure, StateT.run_pure, pure_bind, guess, simulateQ_spec_query]
  change Pr{let y ← (fun u => (u, update (false, 0) u)) <$> ($ᵗ Fin 4)}[
    y.2.1 = true ∧ potential y.2 ≤ 4⁻¹] = 4⁻¹
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, update,
    Bool.false_or, decide_eq_true_eq, potential, zero_add, Nat.cast_one, one_mul, le_refl,
    and_true]
  exact prEvent_uniformSample_eq_zero

/-- The terminal phase is charged: with no query in the first phase, the two-phase bound `4⁻¹`
on drawing `0` within one answer holds and is attained by the same event. -/
theorem prEvent_terminal_fire_le_eq :
    Pr{
      let z ← (simulateQ guessImpl (pure () : OracleComp spec Unit)).run (false, 0)
      let y ← (simulateQ guessImpl guess).run z.2}[
        y.2.1 = true ∧ potential y.2 ≤ 4⁻¹] ≤ 4⁻¹ ∧
    Pr{
      let z ← (simulateQ guessImpl (pure () : OracleComp spec Unit)).run (false, 0)
      let y ← (simulateQ guessImpl guess).run z.2}[
        y.2.1 = true ∧ potential y.2 ≤ 4⁻¹] = 4⁻¹ :=
  ⟨prEvent_twoPhase_le _ (fun _ => guess) 4⁻¹ (by simp), prEvent_terminal_fire_and_le_eq⟩

/-! ## A second phase on another state type -/

/-- One query with answers in `Bool`. -/
abbrev coinSpec : OracleSpec Unit := Unit →ₒ Bool

/-- A coin oracle answering with a uniform bit.  Its state records whether a hit has occurred
(a bit `true` here, or a `0` handed over), the number of answers handed over, and the number of
coins drawn. -/
def coinImpl : QueryImpl coinSpec (StateT (Bool × ℕ × ℕ) ProbComp) := fun _ =>
  StateT.mk fun s => (fun b => (b, (s.1 || b, s.2.1, s.2.2 + 1))) <$> ($ᵗ Bool)

/-- The coin oracle's potential: `4⁻¹` per handed-over answer and `2⁻¹` per drawn coin. -/
noncomputable def coinPotential (s : Bool × ℕ × ℕ) : ℝ≥0∞ := s.2.1 * 4⁻¹ + s.2.2 * 2⁻¹

/-- The coin oracle charges a hit to its potential: no draw lowers it, and out of a state
without a hit a draw is a uniform bit that is `true` with probability `2⁻¹` and raises the
potential by `2⁻¹`. -/
theorem coin_isPotentialStep :
    IsPotentialStep coinImpl (fun s => s.1 = true) coinPotential where
  mono _ s z hz := by
    change z ∈ support ((fun b => (b, (s.1 || b, s.2.1, s.2.2 + 1))) <$> ($ᵗ Bool)) at hz
    rw [support_map] at hz
    obtain ⟨b, -, rfl⟩ := hz
    unfold coinPotential
    gcongr
    exact Nat.le_succ _
  step _ s hs := by
    refine Or.inr ⟨$ᵗ Bool, fun b => (s.1 || b, s.2.1, s.2.2 + 1), 2⁻¹, rfl, ?_, fun b => ?_⟩
    · rw [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_or]
      rw [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton,
        Fintype.card_bool, Nat.cast_ofNat]
    · refine le_of_eq ?_
      simp only [coinPotential, Nat.cast_add, Nat.cast_one]
      ring

/-- The handover from the guessing oracle to the coin oracle: a hit if `0` has been drawn, the
number of answers drawn, and no coin drawn yet. -/
def handover {α : Type} (z : α × (Bool × ℕ)) : Bool × ℕ × ℕ := (z.2.1, z.2.2, 0)

/-- A run of the guessing oracle followed by a run of the coin oracle from the handed-over state
draws `0` or `true` within potential `K` with probability at most `K`. -/
theorem prEvent_guess_coin_le {α β : Type} (oa : OracleComp spec α)
    (ob : α × (Bool × ℕ) → OracleComp coinSpec β) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Pr{
      let z ← (simulateQ guessImpl oa).run (false, 0)
      let y ← (simulateQ coinImpl (ob z)).run (handover z)}[
        y.2.1 = true ∧ coinPotential y.2 ≤ K] ≤ K := by
  have h := prEvent_bind_run_and_le_of_potential isPotentialStep coin_isPotentialStep handover
    (fun _ h => h) (fun z => by simp [handover, potential, coinPotential]) oa ob K hK
    (false, 0) Bool.false_ne_true
  simpa only [potential, Nat.cast_zero, zero_mul, tsub_zero] using h

/-- A coin toss. -/
def toss : OracleComp coinSpec Bool := liftM (coinSpec.query ())

/-- With one guess and then one coin the bound is `4⁻¹ + 2⁻¹ < 1`. -/
example :
    Pr{
      let z ← (simulateQ guessImpl guess).run (false, 0)
      let y ← (simulateQ coinImpl toss).run (handover z)}[
        y.2.1 = true ∧ coinPotential y.2 ≤ 4⁻¹ + 2⁻¹] ≤ 4⁻¹ + 2⁻¹ :=
  prEvent_guess_coin_le guess (fun _ => toss) _ (by simp)

end TwoPhaseToy
