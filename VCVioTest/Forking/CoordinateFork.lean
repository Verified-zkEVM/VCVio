/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.MultiRound

/-!
# Adversarial regression checks for coordinate-wise table forking

These checks exercise facts that a green build does not establish on its own.

**Non-vacuity.** `docs/agents/gotchas.md` §14 asks for a kernel-checked witness whenever a
hypothesis bundle's joint satisfiability is not immediate. The coordinate-fork headline carries
`[SampleableType (ι → S)]`, whose synthesis for a `Pi` type is delicate, and its conclusion is an
`ℝ≥0∞` truncated subtraction that collapses to `0 ≤ _` whenever `ℓ * (k - 1) ≥ N`. The checks below
instantiate it at `ι = Fin 2`, `S = Fin 5`, `k = 2` — so `ℓ * (k - 1) = 2 < 5 = N` — and exhibit a
strictly positive bound.

**Payload sensitivity.** A meaningful output bound must constrain what the computation returns.
`goodOutput_empty_false` witnesses that an empty challenge set fails `GoodOutput`.

**Adversarial cases.** Further checks use a nonconstant table, exhibit equal marginals with
different joint fork behavior, exercise `μ = 2`, and pin down truncation and empty-coordinate
boundaries.
-/

@[expose] public section

open OracleComp OracleComp.EvalDist CoordinateWise

open scoped ENNReal

namespace VCVioTest.Forking

/-- The parameters: two coordinates over a five-element challenge alphabet, `k = 2`. -/
abbrev Chal : Type := Fin 2 → Fin 5

/-- The instance bundle of the headline is satisfiable at concrete types: this elaborates, so
`[SampleableType (Fin 2 → Fin 5)]` is discharged rather than assumed. -/
example (D : ProbComp (Chal → Bool)) :
    acceptRatio D - (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5)
      ≤ Pr[GoodOutput 2 | coordFork 2 D] :=
  sub_div_le_probEvent_goodOutput_coordFork 2 D

/-- At these parameters the loss is `2/5`, so the bound is not truncated away. -/
example : (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 2 / 5 := by
  simp

/-- The all-accepting table, the simplest distribution with no failure mass. -/
def allAccept : Chal → Bool := fun _ => true

example : Pr[⊥ | (pure allAccept : ProbComp (Chal → Bool))] = 0 := by simp

/-- The all-accepting table accepts every challenge, so `ε = 1`. -/
theorem acceptRatio_allAccept : acceptRatio (pure allAccept : ProbComp (Chal → Bool)) = 1 := by
  rw [acceptRatio]
  have hone : ∀ c : Chal, Pr[fun ρ => ρ c | (pure allAccept : ProbComp (Chal → Bool))] = 1 :=
    fun c => by simp [allAccept]
  rw [Finset.sum_congr rfl fun c _ => hone c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ENNReal.div_self (by simp) (by finiteness)]

private theorem one_sub_two_fifths : (1 : ℝ≥0∞) - 2 / 5 = 3 / 5 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 2 = 5 by norm_num,
    ENNReal.div_self (by simp) (by finiteness)]

/-- **Non-vacuity.** Against the all-accepting table the headline gives a strictly positive lower
bound of `3/5` on the extractor's success probability, so neither the truncated subtraction nor the
instance hypotheses have hollowed the statement out. -/
theorem three_fifths_le_probEvent_goodOutput :
    (3 : ℝ≥0∞) / 5 ≤ Pr[GoodOutput 2 | coordFork 2 (pure allAccept : ProbComp (Chal → Bool))] := by
  have h := sub_div_le_probEvent_goodOutput_coordFork 2
    (pure allAccept : ProbComp (Chal → Bool))
  refine le_trans (le_of_eq ?_) h
  rw [acceptRatio_allAccept,
    show (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 2 / 5 from by simp,
    one_sub_two_fifths]

/-- **Payload sensitivity.** An extractor returning an empty challenge set fails `GoodOutput`, so
the headline genuinely constrains the output and is not a bound on `isSome` alone. -/
theorem goodOutput_empty_false (k : ℕ) (ρ : Chal → Bool) :
    ¬ GoodOutput k (some (ρ, (∅ : Finset Chal))) := by
  rintro ⟨ρ', X, hEq, ⟨⟨e, heX, -⟩, -⟩, -⟩
  rw [Option.some.injEq, Prod.mk.injEq] at hEq
  exact absurd (hEq.2 ▸ heX) (Finset.notMem_empty e)

/-! ## The transcript layer -/

/-- The trivial verifier that reads a `Bool` response as its own verdict. -/
def selfVerify : Chal → Bool → Bool := fun _ y => y

/-- Responses in the model are a strict generalization: at `Y := Bool` with the verdict-reading
verifier the induced acceptance table is the response table itself. -/
theorem acceptTable_selfVerify (D : ProbComp (Chal → Bool)) :
    acceptTable selfVerify D = D := by
  simp [acceptTable, selfVerify]

/-- **Non-vacuity of the transcript headline.** The same `3/5` bound, now on the event that the
extractor returns `ℓ(k-1)+1` *accepting transcripts* whose challenges are `SS(S, ℓ, k)`. -/
theorem three_fifths_le_probEvent_goodTranscripts :
    (3 : ℝ≥0∞) / 5 ≤ Pr[GoodTranscripts selfVerify 2 |
      coordForkT selfVerify 2 (pure allAccept : ProbComp (Chal → Bool))] := by
  have h := sub_div_le_probEvent_goodTranscripts_coordForkT selfVerify 2
    (pure allAccept : ProbComp (Chal → Bool))
  refine le_trans (le_of_eq ?_) h
  rw [acceptTable_selfVerify, acceptRatio_allAccept,
    show (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 2 / 5 from by simp,
    one_sub_two_fifths]

/-- **Payload sensitivity, transcript layer.** An empty transcript set fails `GoodTranscripts`, so
the transcript headline is not a bound on `isSome` either. -/
theorem goodTranscripts_empty_false (k : ℕ) (τ : Chal → Bool) :
    ¬ GoodTranscripts selfVerify k (some (τ, (∅ : Finset Chal))) := by
  rw [goodTranscripts_some_iff]
  rintro ⟨⟨⟨e, heX, -⟩, -⟩, -⟩
  exact absurd heX (Finset.notMem_empty e)

/-! ## Coupling sensitivity -/

/-- The smallest challenge space on which two table entries can be correlated differently. -/
abbrev CouplingChal : Type := Fin 1 → Fin 2

/-- Both entries take the same uniformly chosen bit. -/
def correlatedTable (b : Bool) : CouplingChal → Bool := fun _ => b

/-- Exactly one of the two entries accepts; the chosen bit decides which one. -/
def anticorrelatedTable (b : Bool) (c : CouplingChal) : Bool :=
  if c 0 = 0 then b else !b

/-- The two table families have identical uniform `1/2` marginals at every challenge. -/
theorem coupling_tables_same_marginal_counts :
    ∀ c : CouplingChal,
      (Finset.univ.filter fun b : Bool => correlatedTable b c).card = 1 ∧
      (Finset.univ.filter fun b : Bool => anticorrelatedTable b c).card = 1 := by
  decide

/-- The correlated coupling has two successful `(table, centre)` pairs at `k = 2`. -/
theorem sum_goodSet_correlated :
    (∑ b : Bool, (goodSet 2 (correlatedTable b)).card) = 2 := by
  decide

/-- The anticorrelated coupling has none, despite having the same marginals. This is a negative
control against silently treating `forkSuccOf` as a function of marginals alone. -/
theorem sum_goodSet_anticorrelated :
    (∑ b : Bool, (goodSet 2 (anticorrelatedTable b)).card) = 0 := by
  decide

/-! ## A nonconstant table -/

/-- One coordinate over five values; exactly challenges `0` and `1` accept. -/
abbrev PartialChal : Type := Fin 1 → Fin 5

def partialAccept (c : PartialChal) : Bool := decide (c 0 < 2)

example : partialAccept ![0] = true := by decide
example : partialAccept ![3] = false := by decide

/-- An accepting centre with both accepting values in its column is good at `k = 2`. -/
example : ![0] ∈ goodSet 2 partialAccept := by decide

/-- A rejecting centre is not good. -/
example : ![3] ∉ goodSet 2 partialAccept := by decide

theorem acceptRatio_partialAccept :
    acceptRatio (pure partialAccept : ProbComp (PartialChal → Bool)) = 2 / 5 := by
  rw [acceptRatio]
  simp only [probEvent_pure]
  rw [← Finset.natCast_card_filter]
  have hcard : (Finset.univ.filter fun c : PartialChal => partialAccept c).card = 2 := by
    decide
  rw [hcard]
  norm_num

private theorem two_fifths_sub_one_fifth : (2 : ℝ≥0∞) / 5 - 1 / 5 = 1 / 5 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 1 = 2 by norm_num]

/-- A nonconstant acceptance table leaves a strictly positive `1/5` lower bound. -/
theorem one_fifth_le_probEvent_goodOutput_partial :
    (1 : ℝ≥0∞) / 5 ≤
      Pr[GoodOutput 2 | coordFork 2 (pure partialAccept : ProbComp (PartialChal → Bool))] := by
  have h := sub_div_le_probEvent_goodOutput_coordFork 2
    (pure partialAccept : ProbComp (PartialChal → Bool))
  refine le_trans (le_of_eq ?_) h
  rw [acceptRatio_partialAccept,
    show (Fintype.card (Fin 1) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 1 / 5 from by simp,
    two_fifths_sub_one_fifth]

/-! ## Boundary canaries -/

/-- Because subtraction is truncated, `k = 0` and `k = 1` are definitionally identical. -/
example (X : Finset PartialChal) :
    IsCoordSpecialSound 0 X ↔ IsCoordSpecialSound 1 X := Iff.rfl

/-- With no coordinates the per-round loss is zero. -/
example : roundLoss (Fin 0) (Fin 3) 2 = 0 := by simp [roundLoss]

/-- Asking for a column thicker than the alphabet makes even the all-accepting table fail. -/
example : goodSet 4 (fun _ : Fin 1 → Fin 3 => true) = ∅ := by decide

/-- The zero-round recurrence is exactly its input value. -/
example (p : Transcript (Fin 1) (Fin 3) 0 → ℝ≥0∞) : multiSucc 2 p = p PUnit.unit := rfl

/-! ## A nontrivial two-round recurrence -/

def twoRoundAlways : Transcript (Fin 1) (Fin 5) 2 → ℝ≥0∞ := fun _ => 1

/-- At `μ = 2`, the analytic recurrence has the positive lower bound `1 - 2/5 = 3/5`. This checks
the induction beyond its definitional zero- and one-round cases; it is not an execution theorem. -/
theorem three_fifths_le_multiSucc_two :
    (3 : ℝ≥0∞) / 5 ≤ multiSucc 2 twoRoundAlways := by
  have h := sub_le_multiSucc (ι := Fin 1) (S := Fin 5) 2 twoRoundAlways (by
    intro t
    simp [twoRoundAlways])
  refine le_trans (le_of_eq ?_) h
  have havg : avgTranscript twoRoundAlways = 1 := by
    simp only [avgTranscript, twoRoundAlways, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    rw [ENNReal.div_self (by norm_num) (by finiteness)]
    rw [mul_one, ENNReal.div_self (by norm_num) (by finiteness)]
  rw [havg]
  simp only [roundLoss, Fintype.card_fin, Nat.cast_one, Nat.reduceSub, one_mul]
  norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one]
  rw [← mul_div_assoc, mul_one]
  exact one_sub_two_fifths.symm

end VCVioTest.Forking
