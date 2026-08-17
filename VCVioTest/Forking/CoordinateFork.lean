/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.MultiRound

/-!
# Regression checks for coordinate-wise forking

Two things a green build does not establish on its own.

**Non-vacuity.** `docs/agents/gotchas.md` §14 asks for a kernel-checked witness whenever a
hypothesis bundle's joint satisfiability is not immediate. The coordinate-fork headline carries
`[SampleableType (ι → S)]`, whose synthesis for a `Pi` type is delicate, and its conclusion is an
`ℝ≥0∞` truncated subtraction that collapses to `0 ≤ _` whenever `ℓ * (k - 1) ≥ N`. The checks below
instantiate it at `ι = Fin 2`, `S = Fin 5`, `k = 2` — so `ℓ * (k - 1) = 2 < 5 = N` — and exhibit a
strictly positive bound.

**Payload sensitivity.** The success bound is only Lemma 7.1 if it constrains what the extractor
returns. `goodOutput_empty_false` witnesses that: an extractor emitting an empty challenge set
would fail `GoodOutput`, so the bound cannot be satisfied vacuously by a degenerate payload.
-/

@[expose] public section

open OracleComp OracleComp.EvalDist CoordinateWise

open scoped ENNReal

namespace VCVioTest.Forking

/-- The parameters: two coordinates over a five-element challenge alphabet, `k = 2`. -/
abbrev Chal : Type := Fin 2 → Fin 5

/-- The instance bundle of the headline is satisfiable at concrete types: this elaborates, so
`[SampleableType (Fin 2 → Fin 5)]` is discharged rather than assumed. -/
example (D : ProbComp (Chal → Bool)) (hmass : Pr[⊥ | D] = 0) :
    acceptRatio D - (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5)
      ≤ Pr[GoodOutput 2 | coordFork 2 D] :=
  sub_div_le_probEvent_goodOutput_coordFork 2 D hmass

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
    (pure allAccept : ProbComp (Chal → Bool)) (by simp)
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

end VCVioTest.Forking
