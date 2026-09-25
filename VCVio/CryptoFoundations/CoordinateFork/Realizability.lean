/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.CryptoFoundations.CoordinateFork
public import ToMathlib.Probability.UniformOn
public import VCVio.EvalDist.IndepProduct
public import VCVio.EvalDist.IndepProductMeasure

/-!
# Realizing a response table by an adversary

The table computations of `VCVio/CryptoFoundations/CoordinateFork.lean` consume a distribution of
complete response tables. This module exhibits such a distribution for an ordinary adversary
`A : (ι → S) → ProbComp Y`, and identifies its accepting ratio with the adversary's own success
probability `advSucc V A = Pr_{c ← C}[V c (A c)]`.

This is the step Lemma 7.1 of Fenzi–Moghaddas–Nguyen leaves implicit. Its proof reasons about
`X_i = |{x ∈ S : V (C x) (A (C x))}|` and uses `Pr[V = 1 ∣ X_i = l] = l / N`; both presuppose that
`A` is a *function* of the challenge, so that "how many values of coordinate `i` would have been
accepted" is well defined at all. A response table is exactly such a function.

**What `indepTable` is, and is not.** It pre-samples independent randomness for every challenge.
That is not the same object as a prover rewound against one coin tape: a prover that ignores its
challenge and returns a single fair bit answers two challenges alike with probability `1` under a
shared tape, and with probability `1/2` here, while the two agree on every single-challenge
marginal. `VCVioTest/Forking/CoordinateFork.lean` exhibits that separation. This file makes no
claim about the rewind coupling.

That is enough for the transfer, because the success bound reads only the marginals of the table
distribution (`OracleComp.le_lintegral_card_goodSet`): realizing *some* distribution with the
adversary's marginals is all it needs. `acceptRatio_acceptTable_indepTable` does that, and
`sub_div_le_prEvent_goodTranscripts_indepTable` restates the transcript bound with `advSucc V A`
on the left. `prEvent_eq_acceptTable_indepTable` records the whole joint law of the induced
acceptance table — a product across challenges — which is a fact about this construction only.

No side condition on `A` is needed. Marginalizing one coordinate out of an independent product is
an equality only when the remaining factors carry full mass; a `ProbComp` always does
(`prEvent_true_probComp`), so the hypothesis is discharged here rather than assumed.

Still absent, and unchanged by this file: the expected-query clause. `indepTable` runs the
adversary once per challenge, so it is not the paper's extractor, which queries it `ℓ(k-1)+1` times
in expectation.
-/

public section

open Finset CoordinateWise OracleComp MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace OracleComp

variable {ι S Y : Type} [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S]
variable [SampleableType (ι → S)]

/-! ## The induced response table -/

/-- The response table obtained by pre-sampling **independent** randomness for every challenge:
run `A` once at each challenge and record the answers.

This is not a rewound prover. A prover holding a single coin tape answers two challenges with
values that share those coins; `Fintype.mPi` gives the two answers independent coins. The two
constructions have the same single-challenge marginals and different joint laws — a prover that
ignores its challenge and returns one fair bit answers two challenges alike with probability `1`
under a shared tape and `1/2` here, which
`VCVioTest/Forking/CoordinateFork.lean` exhibits. What the transfer below needs is only the
marginals, which is why an independently pre-sampled table suffices for it; identifying a rewound
prover's joint law is a different statement, and not one this file makes. -/
@[expose] noncomputable def indepTable (A : (ι → S) → ProbComp Y) : ProbComp ((ι → S) → Y) :=
  Fintype.mPi A

/-- The verdict the verifier reaches on the adversary's answer to a single challenge. -/
@[expose] noncomputable def verdict (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y)
    (c : ι → S) : ProbComp Bool :=
  (fun y => V c y) <$> A c

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
/-- The verdict is `true` exactly as often as the verifier accepts. -/
theorem prEvent_verdict (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) (c : ι → S) :
    Pr{let b ← verdict V A c}[b] = Pr{let y ← A c}[V c y] := by
  rw [verdict, prEvent_map]

omit [DecidableEq ι] [Fintype ι] [DecidableEq S] [Fintype S] [SampleableType (ι → S)] in
/-- A `ProbComp` carries full mass, which is the losslessness the coordinate marginals need. -/
theorem prEvent_true_probComp {α : Type} (mx : ProbComp α) : Pr{let _ ← mx}[True] = 1 := by
  rw [prEvent_true_eq_evalDist_apply_univ]
  exact measure_univ

/-! ## The adversary's success probability -/

/-- `ε_V(A)`: the probability that the verifier accepts the adversary's answer to a uniformly
random challenge. -/
@[expose] noncomputable def advSucc (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) : ℝ≥0∞ :=
  Pr{let c ← $ᵗ (ι → S); let y ← A c}[V c y]

omit [DecidableEq S] in
/-- Unfolding the uniform challenge: `ε_V(A)` is the average over challenges of the adversary's
per-challenge acceptance probability. This is the shape `acceptRatio` is stated in. -/
theorem advSucc_eq_sum_div (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y) :
    advSucc V A = (∑ c : ι → S, Pr{let y ← A c}[V c y]) / Fintype.card (ι → S) := by
  classical
  -- The statement mentions no measure on the challenge space, so the discrete structure the
  -- averaging step needs is introduced here rather than carried as a hypothesis.
  let _ : MeasurableSpace (ι → S) := ⊤
  let _ : MeasurableSingletonClass (ι → S) := ⟨fun _ => trivial⟩
  have key := prEvent_bind_eq_lintegral_of_discrete ($ᵗ (ι → S))
    (fun c => (A c >>= fun y => pure (V c y = true))) id
  simp only [id_eq, bind_pure] at key
  rw [advSucc, key, SampleableType.evalDist_uniformSample, lintegral_uniformOn_univ]

/-! ## Transfer to the table bound -/

omit [DecidableEq S] [SampleableType (ι → S)] in
/-- The marginal of the induced acceptance table at a challenge is the adversary's acceptance
probability there. -/
theorem prEvent_apply_acceptTable_indepTable (V : (ι → S) → Y → Bool)
    (A : (ι → S) → ProbComp Y) (c : ι → S) :
    Pr{let ρ ← acceptTable V (indepTable A)}[ρ c] = Pr{let y ← A c}[V c y] := by
  simp only [acceptTable, indepTable]
  rw [prEvent_map]
  exact prEvent_coord_mPi A c (fun y => V c y) fun c' _ => prEvent_true_probComp (A c')

omit [DecidableEq S] in
/-- The accepting ratio of the induced table is the adversary's own success probability. -/
theorem acceptRatio_acceptTable_indepTable (V : (ι → S) → Y → Bool)
    (A : (ι → S) → ProbComp Y) :
    acceptRatio (acceptTable V (indepTable A)) = advSucc V A := by
  rw [acceptRatio, advSucc_eq_sum_div]
  exact congrArg (· / _)
    (Finset.sum_congr rfl fun c _ => prEvent_apply_acceptTable_indepTable V A c)

/-- **The success and output clauses of Lemma 7.1, for an adversary.** Against the response table
of an adversary whose randomness is pre-sampled per challenge, the coordinate fork returns
`ℓ(k-1)+1` accepting transcripts whose challenges form an `SS(S, ℓ, k)` set, with probability at
least `ε_V(A) - ℓ(k-1)/N`.

The expected-query clause is not part of this statement: `indepTable` queries `A` once per
challenge, not `ℓ(k-1)+1` times. -/
theorem sub_div_le_prEvent_goodTranscripts_indepTable [Nonempty S] [DecidableEq Y]
    (V : (ι → S) → Y → Bool) (k : ℕ) (A : (ι → S) → ProbComp Y) :
    advSucc V A - (Fintype.card ι : ℝ≥0∞) * (k - 1 : ℕ) / Fintype.card S
      ≤ Pr{let r ← coordForkT V k (indepTable A)}[GoodTranscripts V k r] := by
  rw [← acceptRatio_acceptTable_indepTable V A]
  exact sub_div_le_prEvent_goodTranscripts_coordForkT V k (indepTable A)

/-! ## The joint law of the induced acceptance table -/

omit [DecidableEq S] [SampleableType (ι → S)] in
/-- The induced acceptance table is a product across challenges. This is a fact about *this*
construction, not about a rewound prover. -/
theorem prEvent_eq_acceptTable_indepTable (V : (ι → S) → Y → Bool) (A : (ι → S) → ProbComp Y)
    (ρ : (ι → S) → Bool) :
    Pr{let ρ' ← acceptTable V (indepTable A)}[ρ' = ρ]
      = ∏ c : ι → S, Pr{let b ← verdict V A c}[b = ρ c] := by
  simp only [acceptTable, indepTable]
  rw [prEvent_map,
    prEvent_congr (Fintype.mPi A) (fun τ : (ι → S) → Y => (fun c => V c (τ c)) = ρ)
      (fun τ => ∀ c, V c (τ c) = ρ c) (fun τ => by simp [funext_iff]),
    prEvent_forall_coord_mPi A fun c y => V c y = ρ c]
  exact Finset.prod_congr rfl fun c _ => by rw [verdict, prEvent_map]

end OracleComp
