/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork.MultiRound
public import VCVio.EvalDist.IndepProduct

/-!
# Realizing a response table by an adversary

The table computations of `VCVio/CryptoFoundations/CoordinateFork.lean` consume a distribution of
complete response tables. This module exhibits such a distribution for an ordinary adversary
`A : (ι → S) → ProbComp Y`, and identifies its accepting ratio with the adversary's own success
probability `advSucc V A = Pr_{c ← C}[V c (A c)]`.

This is the step Lemma 7.1 of Fenzi–Moghaddas–Nguyen leaves implicit. Its proof reasons about
`X_i = |{x ∈ S : V (C x) (A (C x))}|` and uses `Pr[V = 1 ∣ X_i = l] = l / N`; both statements
presuppose that `A` is a *function* of the challenge, i.e. that its coins are fixed before any
challenge is chosen. A fixed-coin adversary is exactly a response table, and `indepTable` is the
table distribution obtained by fixing them.

The success bound only ever reads the marginals of the table distribution
(`OracleComp.EvalDist.le_tsum_probOutput_mul_goodSet`), so realizing *some* distribution with the
adversary's marginals is all the transfer needs; `acceptRatio_acceptTable_indepTable` does that,
and `sub_div_le_probEvent_goodTranscripts_indepTable` restates the transcript bound with
`advSucc V A` on the left.

`probOutput_acceptTable_indepTable_eq_bernoulliTable` goes further and computes the *whole* joint
law of the induced acceptance table, which is the independent Bernoulli table at the adversary's
per-challenge acceptance probabilities. That discharges the hypothesis of
`forkSucc_eq_probEvent_isSome_coordFork`, so the analytic multi-round recurrence is anchored to a
computation rather than to a distribution nothing produces.

No side condition on `A` is needed. Marginalizing one coordinate out of an independent product is
an equality only when the remaining factors carry full mass — `probEvent_coord_mOfFn` assumes that
and `probEvent_coord_mOfFn_le` is what survives without it — but a `ProbComp` never fails
(`probFailure_of_liftM_PMF`), so the hypothesis is discharged here rather than assumed.

Still absent, and unchanged by this file: the expected-query clause. `indepTable` runs the
adversary once per challenge, so it is not the paper's extractor, which queries it `ℓ(k-1)+1` times
in expectation. The independence across challenges is likewise a property of *this* table
distribution, not something derived from an interactive prover.
-/

@[expose] public section

open Finset CoordinateWise OracleComp OracleComp.EvalDist

open scoped ENNReal

namespace OracleComp

variable {ι S Y : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable [SampleableType (ι → S)]

/-! ## The induced response table -/

/-- The response table of an adversary whose coins are fixed once and for all: run `A`
independently at every challenge and record the answers. -/
noncomputable def indepTable (A : (ι → S) → ProbComp Y) : ProbComp ((ι → S) → Y) :=
  Fintype.mPi A

/-- The verdict the verifier reaches on the adversary's answer to a single challenge. -/
noncomputable def verdict (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) (c : ι → S) :
    ProbComp Bool :=
  (fun y => V c y) <$> A c

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
/-- The verdict is `true` exactly as often as the verifier accepts. -/
theorem probOutput_true_verdict (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) (c : ι → S) :
    Pr[= true | verdict V A c] = Pr[fun y => V c y | A c] := by
  rw [verdict, probOutput_map]

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
/-- The complementary verdict probability, which is where the adversary's inability to fail is
used: a `ProbComp` carries full mass, so rejection takes up all of what acceptance leaves. -/
theorem probOutput_false_verdict (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) (c : ι → S) :
    Pr[= false | verdict V A c] = 1 - Pr[fun y => V c y | A c] := by
  rw [probOutput_false_eq_sub, probOutput_true_verdict, verdict, probFailure_map,
    probFailure_of_liftM_PMF (A c), tsub_zero]

/-! ## The adversary's success probability -/

/-- `ε_V(A)`: the probability that the verifier accepts the adversary's answer to a uniformly
random challenge. -/
noncomputable def advSucc (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) : ℝ≥0∞ :=
  Pr[fun p => V p.1 p.2 | (do let c ← $ᵗ (ι → S); let y ← A c; return (c, y))]

omit [DecidableEq S] in
/-- Unfolding the uniform challenge: `ε_V(A)` is the average over challenges of the adversary's
per-challenge acceptance probability. This is the shape `acceptRatio` is stated in. -/
theorem advSucc_eq_sum_div (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) :
    advSucc V A = (∑ c : ι → S, Pr[fun y => V c y | A c]) / Fintype.card (ι → S) := by
  have hinner : ∀ c : ι → S,
      Pr[fun p : (ι → S) × Y => V p.1 p.2 | (A c >>= fun y => pure (c, y) : ProbComp _)]
        = Pr[fun y => V c y | A c] := by
    intro c
    rw [show (A c >>= fun y => pure (c, y) : ProbComp ((ι → S) × Y)) = (fun y => (c, y)) <$> A c
      from by simp [map_eq_bind_pure_comp], probEvent_map]
    rfl
  rw [advSucc, probEvent_bind_eq_tsum]
  simp only [hinner, probOutput_uniformSample]
  rw [ENNReal.tsum_mul_left, tsum_fintype (L := .unconditional _), div_eq_mul_inv, mul_comm]

/-! ## Transfer to the table bound -/

omit [DecidableEq S] [SampleableType (ι → S)] in
/-- The marginal of the induced acceptance table at a challenge is the adversary's acceptance
probability there. -/
theorem probEvent_apply_acceptTable_indepTable (V : (ι → S) → Y → Bool)
    (A : (ι → S) → ProbComp Y) (c : ι → S) :
    Pr[fun ρ => ρ c | acceptTable V (indepTable A)] = Pr[fun y => V c y | A c] := by
  rw [acceptTable, indepTable, probEvent_map]
  exact probEvent_coord_mPi A (fun c' => probFailure_of_liftM_PMF (A c')) c fun y => V c y

omit [DecidableEq S] in
/-- The accepting ratio of the induced table is the adversary's own success probability. -/
theorem acceptRatio_acceptTable_indepTable (V : (ι → S) → Y → Bool)
    (A : (ι → S) → ProbComp Y) :
    acceptRatio (acceptTable V (indepTable A)) = advSucc V A := by
  rw [acceptRatio, advSucc_eq_sum_div]
  exact congrArg (· / _)
    (Finset.sum_congr rfl fun c _ => probEvent_apply_acceptTable_indepTable V A c)

/-- **The success and output clauses of Lemma 7.1, for an adversary.** Against the response table
induced by fixing `A`'s coins, the coordinate fork returns `ℓ(k-1)+1` accepting transcripts whose
challenges form an `SS(S, ℓ, k)` set, with probability at least `ε_V(A) - ℓ(k-1)/N`.

The expected-query clause is not part of this statement: `indepTable` queries `A` once per
challenge, not `ℓ(k-1)+1` times. -/
theorem sub_div_le_probEvent_goodTranscripts_indepTable [Nonempty S] [DecidableEq Y]
    (V : (ι → S) → Y → Bool)
    (k : ℕ) (A : (ι → S) → ProbComp Y) :
    advSucc V A - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr[GoodTranscripts V k | coordForkT V k (indepTable A)] := by
  rw [← acceptRatio_acceptTable_indepTable V A]
  exact sub_div_le_probEvent_goodTranscripts_coordForkT V k (indepTable A)

/-! ## The joint law of the induced acceptance table -/

omit [DecidableEq S] [SampleableType (ι → S)] in
/-- The induced acceptance table is a product across challenges. -/
theorem probOutput_acceptTable_indepTable (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y)
    (ρ : (ι → S) → Bool) :
    Pr[= ρ | acceptTable V (indepTable A)] = ∏ c : ι → S, Pr[= ρ c | verdict V A c] := by
  rw [acceptTable, indepTable, probOutput_map,
    show (fun τ : (ι → S) → Y => (fun c => V c (τ c)) = ρ)
      = (fun τ => ∀ c, V c (τ c) = ρ c) from by funext τ; simp [funext_iff],
    probEvent_forall_coord_mPi A fun c y => V c y = ρ c]
  exact Finset.prod_congr rfl fun c _ => by rw [verdict, probOutput_map]

omit [SampleableType (ι → S)] in
/-- The induced acceptance table *is* the independent Bernoulli table at the adversary's
per-challenge acceptance probabilities. This is what makes the Bernoulli coupling of the analytic
multi-round recurrence realizable rather than assumed. -/
theorem probOutput_acceptTable_indepTable_eq_bernoulliTable (V : (ι → S) → Y → Bool)
    (A : (ι → S) → ProbComp Y) (ρ : (ι → S) → Bool) :
    Pr[= ρ | acceptTable V (indepTable A)] =
      Pr[= ρ | (PMF.bernoulliTable (fun c => Pr[fun y => V c y | A c])
        (fun _ => probEvent_le_one) : PMF ((ι → S) → Bool))] := by
  rw [probOutput_acceptTable_indepTable, PMF.probOutput_eq_apply, PMF.bernoulliTable_apply]
  refine Finset.prod_congr rfl fun c _ => ?_
  cases hρ : ρ c
  · rw [PMF.tableWeight_false, probOutput_false_verdict V A c]
  · rw [PMF.tableWeight_true, probOutput_true_verdict V A c]

/-- **The multi-round single-step bridge, discharged.** The analytic `forkSucc` at the adversary's
per-challenge acceptance probabilities is the success probability of the table fork run against the
table the adversary actually induces. -/
theorem forkSucc_eq_probEvent_isSome_coordFork_indepTable (V : (ι → S) → Y → Bool) (k : ℕ)
    (A : (ι → S) → ProbComp Y) :
    forkSucc k (fun c => Pr[fun y => V c y | A c])
      = Pr[fun r => r.isSome | coordFork k (acceptTable V (indepTable A))] :=
  forkSucc_eq_probEvent_isSome_coordFork k _ (fun _ => probEvent_le_one) _
    (probOutput_acceptTable_indepTable_eq_bernoulliTable V A)

end OracleComp
