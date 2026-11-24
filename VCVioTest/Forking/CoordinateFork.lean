/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.Operational
public import VCVio.CryptoFoundations.CoordinateFork.Realizability

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
different joint fork behavior, exhaust a coordinate's pool, and pin down the `k - 1` truncation
and a column thicker than the alphabet.

**Realizability.** The table bound is only interesting if some ordinary adversary induces a table
distribution with a known accepting ratio. `advSucc_partialAdv` computes one, and
`one_fifth_le_prEvent_goodTranscripts_indepTable` is the resulting strictly positive bound.
`prEvent_coord_mOfFn_failFactor` is the matching negative control: without the full-mass
hypothesis the coordinate marginal of an independent product is not the factor's own.

**`indepTable` is not a rewound prover.** `coinFlip_same_marginals` and
`coinFlip_allAccept_{sharedTape,indepTable}` separate independent per-challenge randomness from a
single shared coin tape: identical single-challenge marginals, joint probabilities `1/2` against
`1/4`. Only the marginals feed `acceptRatio_acceptTable_indepTable`, which is why the transfer
holds and why it says nothing about rewinding.
-/

public section

open OracleComp CoordinateWise MeasureTheory

open scoped ENNReal

namespace VCVioTest.Forking

/-- The parameters: two coordinates over a five-element challenge alphabet, `k = 2`. -/
abbrev Chal : Type := Fin 2 → Fin 5

/-- The instance bundle of the headline is satisfiable at concrete types: this elaborates, so
`[SampleableType (Fin 2 → Fin 5)]` is discharged rather than assumed. -/
example (D : ProbComp (Chal → Bool)) :
    acceptRatio D - (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5)
      ≤ Pr{let r ← coordFork 2 D}[GoodOutput 2 r] :=
  sub_div_le_prEvent_goodOutput_coordFork 2 D

/-- At these parameters the loss is `2/5`, so the bound is not truncated away. -/
example : (Fintype.card (Fin 2) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 2 / 5 := by
  simp

/-- The all-accepting table, the simplest distribution with no failure mass. -/
def allAccept : Chal → Bool := fun _ => true

example : IsProbabilityMeasure 𝒟[(pure allAccept : ProbComp (Chal → Bool))] := by infer_instance

/-- The all-accepting table accepts every challenge, so `ε = 1`. -/
theorem acceptRatio_allAccept : acceptRatio (pure allAccept : ProbComp (Chal → Bool)) = 1 := by
  rw [acceptRatio]
  have hone : ∀ c : Chal, Pr{let ρ ← (pure allAccept : ProbComp (Chal → Bool))}[ρ c] = 1 :=
    fun c => by rw [prEvent_eq_evalDist_map]; simp [allAccept]
  rw [Finset.sum_congr rfl fun c _ => hone c, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ENNReal.div_self (by simp) (by finiteness)]

private theorem one_sub_two_fifths : (1 : ℝ≥0∞) - 2 / 5 = 3 / 5 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 2 = 5 by norm_num,
    ENNReal.div_self (by simp) (by finiteness)]

/-- **Non-vacuity.** Against the all-accepting table the headline gives a strictly positive lower
bound of `3/5` on the extractor's success probability, so neither the truncated subtraction nor the
instance hypotheses have hollowed the statement out. -/
theorem three_fifths_le_prEvent_goodOutput :
    (3 : ℝ≥0∞) / 5
      ≤ Pr{let r ← coordFork 2 (pure allAccept : ProbComp (Chal → Bool))}[GoodOutput 2 r] := by
  have h := sub_div_le_prEvent_goodOutput_coordFork 2
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
theorem three_fifths_le_prEvent_goodTranscripts :
    (3 : ℝ≥0∞) / 5
      ≤ Pr{let r ← coordForkT selfVerify 2 (pure allAccept : ProbComp (Chal → Bool))}[
          GoodTranscripts selfVerify 2 r] := by
  have h := sub_div_le_prEvent_goodTranscripts_coordForkT selfVerify 2
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

/-! ## `indepTable` is not a shared coin tape

`Realizability.lean` builds a response table by pre-sampling **independent** randomness at every
challenge. A prover rewound against one coin tape is a different object, and the difference shows
at the smallest possible scale: `coinFlipAdv` ignores its challenge and answers with one fair bit.
The two constructions agree on every single-challenge marginal — which is all the transfer in
`acceptRatio_acceptTable_indepTable` reads — and disagree on the joint law, which is why that
transfer does not license reading `indepTable` as a rewound prover. -/

/-- A prover that ignores its challenge and answers with one fair bit. -/
noncomputable def coinFlipAdv : CouplingChal → ProbComp Bool := fun _ => $ᵗ Bool

/-- The shared-tape table: one bit, copied to every challenge. -/
noncomputable def coinFlipSharedTape : ProbComp (CouplingChal → Bool) :=
  (fun b _ => b) <$> ($ᵗ Bool)

private theorem prEvent_coinFlip (c : CouplingChal) : Pr{let y ← coinFlipAdv c}[y] = 1 / 2 := by
  rw [coinFlipAdv, SampleableType.prEvent_uniformSample,
    show (Finset.univ.filter fun y : Bool => y = true).card = 1 from by decide]
  norm_num

/-- Identical single-challenge marginals. -/
theorem coinFlip_same_marginals (c : CouplingChal) :
    Pr{let τ ← indepTable coinFlipAdv}[τ c] = Pr{let τ ← coinFlipSharedTape}[τ c] := by
  rw [indepTable,
    prEvent_coord_mPi coinFlipAdv c (fun y => y = true)
      (fun c' _ => prEvent_true_probComp (coinFlipAdv c')),
    prEvent_coinFlip, coinFlipSharedTape, prEvent_map]
  exact (prEvent_coinFlip c).symm

/-- **The joint laws differ.** Two challenges accept together half the time under a shared tape
and a quarter of the time under independent pre-sampling. -/
theorem coinFlip_allAccept_sharedTape :
    Pr{let τ ← coinFlipSharedTape}[∀ c, τ c] = 1 / 2 := by
  rw [coinFlipSharedTape, prEvent_map,
    prEvent_congr ($ᵗ Bool) (fun b => ∀ c : CouplingChal, (fun _ => b) c) (fun b => b = true)
      fun b => by simp]
  exact prEvent_coinFlip ![0]

theorem coinFlip_allAccept_indepTable :
    Pr{let τ ← indepTable coinFlipAdv}[∀ c, τ c] = 1 / 4 := by
  rw [indepTable, prEvent_forall_coord_mPi coinFlipAdv fun _ y => y = true]
  rw [Finset.prod_congr rfl fun c _ => prEvent_coinFlip c, Finset.prod_const, Finset.card_univ,
    show Fintype.card CouplingChal = 2 from rfl]
  simp only [one_div, ← ENNReal.inv_pow]
  norm_num

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
  have hsum : (∑ c : PartialChal,
      Pr{let ρ ← (pure partialAccept : ProbComp (PartialChal → Bool))}[ρ c])
      = ((Finset.univ.filter fun c : PartialChal => partialAccept c).card : ℝ≥0∞) := by
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [prEvent_eq_evalDist_map, map_pure, evalDist_pure,
      Measure.dirac_apply' _ MeasurableSet.of_discrete]
    by_cases h : partialAccept c <;> simp [Set.indicator, h]
  rw [acceptRatio, hsum]
  have hcard : (Finset.univ.filter fun c : PartialChal => partialAccept c).card = 2 := by
    decide
  rw [hcard]
  norm_num

private theorem two_fifths_sub_one_fifth : (2 : ℝ≥0∞) / 5 - 1 / 5 = 1 / 5 := by
  refine ENNReal.sub_eq_of_eq_add (by finiteness) ?_
  rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 1 = 2 by norm_num]

/-- A nonconstant acceptance table leaves a strictly positive `1/5` lower bound. -/
theorem one_fifth_le_prEvent_goodOutput_partial :
    (1 : ℝ≥0∞) / 5 ≤
      Pr{let r ← coordFork 2 (pure partialAccept : ProbComp (PartialChal → Bool))}[GoodOutput 2 r]
      := by
  have h := sub_div_le_prEvent_goodOutput_coordFork 2
    (pure partialAccept : ProbComp (PartialChal → Bool))
  refine le_trans (le_of_eq ?_) h
  rw [acceptRatio_partialAccept,
    show (Fintype.card (Fin 1) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 1 / 5 from by simp,
    two_fifths_sub_one_fifth]

/-! ## Realizing a response table by an adversary -/

/-- The adversary of `partialAccept`, read as a computation: it answers `true` exactly on the two
accepting challenges and never fails. -/
def partialAdv (c : PartialChal) : ProbComp Bool := pure (partialAccept c)

/-- Reading the response itself as the verdict. -/
def selfVerify1 : PartialChal → Bool → Bool := fun _ y => y

/-- The adversary convinces the verifier on exactly two of five challenges. -/
theorem advSucc_partialAdv : advSucc selfVerify1 partialAdv = 2 / 5 := by
  have hsum : (∑ c : PartialChal, Pr{let y ← partialAdv c}[selfVerify1 c y])
      = ((Finset.univ.filter fun c : PartialChal => partialAccept c).card : ℝ≥0∞) := by
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [partialAdv, selfVerify1]
    rw [prEvent_eq_evalDist_map, map_pure, evalDist_pure,
      Measure.dirac_apply' _ MeasurableSet.of_discrete]
    by_cases h : partialAccept c <;> simp [Set.indicator, h]
  rw [advSucc_eq_sum_div, hsum]
  have hcard : (Finset.univ.filter fun c : PartialChal => partialAccept c).card = 2 := by decide
  rw [hcard]
  norm_num

/-- The table the adversary induces has the adversary's own accepting ratio: the transfer is not
vacuous. -/
theorem acceptRatio_indepTable_partialAdv :
    acceptRatio (acceptTable selfVerify1 (indepTable partialAdv)) = 2 / 5 := by
  rw [acceptRatio_acceptTable_indepTable selfVerify1 partialAdv, advSucc_partialAdv]

/-- **Lemma 7.1 against an actual adversary**, with a strictly positive bound. -/
theorem one_fifth_le_prEvent_goodTranscripts_indepTable :
    (1 : ℝ≥0∞) / 5 ≤
      Pr{let r ← coordForkT selfVerify1 2 (indepTable partialAdv)}[GoodTranscripts selfVerify1 2 r]
      := by
  have h := sub_div_le_prEvent_goodTranscripts_indepTable selfVerify1 2 partialAdv
  refine le_trans (le_of_eq ?_) h
  rw [advSucc_partialAdv,
    show (Fintype.card (Fin 1) : ℝ≥0∞) * (2 - 1 : ℕ) / Fintype.card (Fin 5) = 1 / 5 from by simp,
    two_fifths_sub_one_fifth]

/-- A two-factor independent product whose second factor always fails. A `ProbComp` cannot fail,
so this lives in `OptionT ProbComp`, where the marginal lemma's hypothesis has content. -/
def failFactor : Fin 2 → OptionT ProbComp Bool := fun i => if i = 0 then pure true else failure

/-- The first factor accepts with certainty. -/
theorem prEvent_failFactor_zero : Pr{let b ← failFactor 0}[b] = 1 := by
  simp [failFactor]

/-- Yet the product's first coordinate accepts with probability zero: a failing factor removes mass
from every coordinate at once. So the full-mass hypothesis of `prEvent_coord_mOfFn` is
load-bearing, and only `prEvent_coord_mOfFn_le` survives without it. -/
theorem prEvent_coord_mOfFn_failFactor :
    Pr{let v ← Fin.mOfFn 2 failFactor}[v 0] = 0 := by
  simp [Fin.mOfFn, failFactor]

/-! ## The resampling loop -/

/-- At these parameters exactly the two accepting challenges are good. -/
theorem card_goodSet_partial : (goodSet 2 partialAccept).card = 2 := by decide

/-- **The loop is faithful to the table core.** Resampling the column in a random order until two
accepting values are found succeeds exactly on `goodSet`, so with probability `2/5` here. -/
theorem prEvent_isSome_coordForkOp_partial :
    Pr{let r ← coordForkOp 2 partialAccept}[r.1.isSome] = 2 / 5 := by
  rw [prEvent_isSome_coordForkOp, card_goodSet_partial]
  simp

/-- The Lemma 7.1 bound for the loop, at parameters where it is strictly positive. -/
theorem one_fifth_le_prEvent_isSome_coordForkOp :
    (1 : ℝ≥0∞) / 5 ≤ Pr{let r ← coordForkOp 2 partialAccept}[r.1.isSome] := by
  rw [prEvent_isSome_coordForkOp_partial]
  gcongr
  norm_num

/-- **Exhaustion.** Asking for four accepting values in a column that holds two, the loop drains
every coordinate and never succeeds. This is behaviour the total-lookup core cannot exhibit, since
it reads the column rather than sampling it. -/
theorem prEvent_isSome_coordForkOp_exhausted :
    Pr{let r ← coordForkOp 4 partialAccept}[r.1.isSome] = 0 := by
  rw [prEvent_isSome_coordForkOp, show (goodSet 4 partialAccept).card = 0 from by decide]
  simp

/-- **The expected-query clause at concrete parameters.** One lookup for the sampled challenge and
at most `k - 1 = 1` more for the single coordinate. The bound is tight here: two of the five
challenges accept, each with one further accepting value in its column, so the loop makes
`(1/5)(2·(1 + 5/2) + 3·1) = 2` lookups on average. -/
theorem lintegral_cost_coordForkOp_partial_le :
    ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> coordForkOp 2 partialAccept] ≤ 2 := by
  have h := lintegral_cost_coordForkOp_le (ι := Fin 1) (S := Fin 5) 2 partialAccept
  refine h.trans (le_of_eq ?_)
  simp
  norm_num

/-! ## The weighted cost -/

/-- **Unit charges recover the count bound.** At the parameters of
`lintegral_cost_coordForkOp_partial_le` the weighted bound reads `≤ 2`, the same number. -/
theorem lintegral_weight_coordForkOpW_partial_le :
    ∫⁻ w, w ∂𝒟[Prod.snd <$> coordForkOpW 2 partialAccept (fun _ => 1)] ≤ 2 := by
  have h := lintegral_weight_coordForkOpW_le (ι := Fin 1) (S := Fin 5) 2 partialAccept
    (fun _ => 1)
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    show (Fintype.card (Fin 1 → Fin 5) : ℕ) = 5 from by decide]
  simp only [Fintype.card_fin, Nat.cast_one, one_mul, show (2 - 1 : ℕ) = 1 from rfl]
  rw [Nat.cast_ofNat, ENNReal.div_self (by norm_num) (by finiteness), mul_one]
  norm_num

/-- **The bound tracks the charges.** Charging ten to the single challenge `![0]` and nothing to
the rest leaves an average charge of two, and the bound doubles it. -/
theorem lintegral_weight_coordForkOpW_partial_skew_le :
    ∫⁻ w, w ∂𝒟[Prod.snd <$> coordForkOpW 2 partialAccept (fun c => if c 0 = 0 then 10 else 0)]
      ≤ 4 := by
  have h := lintegral_weight_coordForkOpW_le (ι := Fin 1) (S := Fin 5) 2 partialAccept
    (fun c => if c 0 = 0 then 10 else 0)
  refine h.trans (le_of_eq ?_)
  have hsum : (∑ c : PartialChal, if c 0 = 0 then (10 : ℝ≥0∞) else 0) = 10 := by
    rw [Finset.sum_eq_single (fun _ => 0 : PartialChal)]
    · simp
    · intro c _ hne
      refine ite_eq_right fun h => hne ?_
      funext i
      fin_cases i
      simpa using h
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum, show (Fintype.card (Fin 1 → Fin 5) : ℕ) = 5 from by decide]
  simp only [Fintype.card_fin, Nat.cast_one, one_mul, show (2 - 1 : ℕ) = 1 from rfl]
  rw [Nat.cast_ofNat, show (10 : ℝ≥0∞) / 5 = 2 from by
    rw [eq_comm, ENNReal.eq_div_iff (by norm_num) (by finiteness)]
    norm_num]
  norm_num

/-! ## Boundary canaries -/

/-- Because subtraction is truncated, `k = 0` and `k = 1` are definitionally identical. -/
example (X : Finset PartialChal) :
    IsCoordSpecialSound 0 X ↔ IsCoordSpecialSound 1 X := Iff.rfl

/-- Asking for a column thicker than the alphabet makes even the all-accepting table fail. -/
example : goodSet 4 (fun _ : Fin 1 → Fin 3 => true) = ∅ := by decide

end VCVioTest.Forking
