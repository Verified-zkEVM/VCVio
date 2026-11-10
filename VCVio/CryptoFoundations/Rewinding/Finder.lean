/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.Rewinding.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Black-box finders for accepting challenge trees

Rounds are indexed by any finite linearly ordered type. A challenge tree assigns a vector to
each branch path, with the challenge at a round depending only on the path through that round.
The finder sees only a Boolean acceptance oracle and its own independent random coins.

## References

* Attema, Cramer and Kohl, *A compressed Σ-protocol theory for lattices*, CRYPTO 2021.
-/

public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Rewinding

variable {R : Type} {C : R → Type}

/-- The Boolean oracle deciding acceptance of a complete challenge vector. -/
abbrev accSpec (C : R → Type) : OracleSpec ((r : R) → C r) :=
  rerunSpec ((r : R) → C r) Bool

/-- A challenge tree with `k r` branches at round `r`. The challenge at a round depends only
on branch choices up to and including that round. -/
structure VecTree [LinearOrder R] (C : R → Type) (k : R → ℕ) where
  /-- The challenge vector at a branch path. -/
  leaf : ((r : R) → Fin (k r)) → (r : R) → C r
  /-- Challenge selection respects the order of rounds. -/
  causal : ∀ (p p' : (r : R) → Fin (k r)) (r : R),
    (∀ s, s ≤ r → p s = p' s) → leaf p r = leaf p' r

/-- Sibling challenges at the node reached by the path before round `r`. -/
@[expose] def VecTree.siblings [LinearOrder R] {k : R → ℕ}
    (t : VecTree C k) (p : (r : R) → Fin (k r)) (r : R) : Fin (k r) → C r :=
  fun j => t.leaf (Function.update p r j) r

/-- Every node of the challenge tree satisfies the prescribed sibling predicate. -/
@[expose] def VecTree.IsStructured [LinearOrder R] {k : R → ℕ}
    (nodeOk : (r : R) → (Fin (k r) → C r) → Prop) (t : VecTree C k) : Prop :=
  ∀ p r, nodeOk r (t.siblings p r)

/-- Run a finder against a fixed acceptance function, returning its output and the number of
acceptance-oracle calls. Coin queries and local work are not charged. -/
@[expose] def runFinder {β : Type} (find : OracleComp (unifSpec + accSpec C) β)
    (f : ((r : R) → C r) → Bool) : ProbComp (β × ℕ) :=
  (simulateQ (coins (S := ℕ) + counted f) find).run 0

/-- The complete-run expectation depends only on the natural-valued counter marginal. -/
theorem expectedCalls_eq_lintegral_counter {β : Type} (mx : ProbComp (β × ℕ)) :
    expectedCalls mx = ∫⁻ n, (n : ℝ≥0∞) ∂𝒟[Prod.snd <$> mx] := by
  rw [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]
  simp only [WriterT.run_mk, Functor.map_map]
  rfl

/-- The complete-run expectation integrates the counter projection of the joint law. -/
theorem expectedCalls_eq_lintegral {β : Type} [MeasurableSpace β]
    (mx : ProbComp (β × ℕ)) : expectedCalls mx = ∫⁻ z, (z.2 : ℝ≥0∞) ∂𝒟[mx] := by
  rw [expectedCalls, AddWriterT.expectedCostNat, AddWriterT.expectedCost,
    AddWriterT.costs_def]
  simp only [WriterT.run_mk, Functor.map_map]
  exact lintegral_evalDist_map mx measurable_snd Measurable.of_discrete

/-- Equal joint output and counter laws have equal expected complete-run counts. -/
theorem expectedCalls_eq_of_evalDistEq {β : Type} {mx my : ProbComp (β × ℕ)}
    (h : mx =ᵈ my) : expectedCalls mx = expectedCalls my := by
  let : MeasurableSpace β := ⊤
  rw [expectedCalls_eq_lintegral, expectedCalls_eq_lintegral, h.evalDist_eq]

/-- The expected counter after a random choice is the average of its conditional expectations. -/
theorem expectedCalls_bind {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : ProbComp α) (f : α → ProbComp (β × ℕ)) :
    expectedCalls (mx >>= f) = ∫⁻ x, expectedCalls (f x) ∂𝒟[mx] := by
  let : MeasurableSpace β := ⊤
  simp only [expectedCalls_eq_lintegral]
  exact lintegral_evalDist_bind_of_discrete mx f (Measurable.of_discrete.comp measurable_snd)

/-- Fraction of complete challenge vectors accepted by `f`. -/
@[expose] noncomputable def acceptRate [Fintype R] [DecidableEq R] [∀ r, Fintype (C r)]
    (f : ((r : R) → C r) → Bool) : ℝ≥0∞ :=
  ((Finset.univ.filter fun c => f c = true).card : ℝ≥0∞) /
    (Fintype.card ((r : R) → C r) : ℝ≥0∞)

/-- A black-box tree finder with branching factors `k`, node predicate `nodeOk`, error `κ` and
cost `T`. Against every acceptance function `f`, every returned tree is structured and accepting,
the acceptance rate `ε` of `f` and the success probability `p` satisfy `ε ≤ κ + (1 - κ) * p`, and
the expected number of acceptance-oracle calls is at most `T`, counted over complete runs whether
or not they succeed. Coin queries and local work are not charged.

Every branching factor is at least one. At `k r = 0` there are no branch paths, so every tree is
vacuously structured and accepting, and a finder that returns a tree without calling the oracle
would meet the contract at error `0` and cost `0`. -/
structure IsTreeFinder [Fintype R] [LinearOrder R] [∀ r, Fintype (C r)] (k : R → ℕ)
    (nodeOk : (r : R) → (Fin (k r) → C r) → Prop)
    (find : OracleComp (unifSpec + accSpec C) (Option (VecTree C k))) (κ T : ℝ≥0∞) : Prop where
  /-- Every round has at least one branch, so the leaves of a returned tree are not vacuous. -/
  one_le : ∀ r, 1 ≤ k r
  /-- Every returned tree is structured and all of its leaves accept. -/
  sound : ∀ f, ∀ z ∈ support (runFinder find f), ∀ t, z.1 = some t →
    t.IsStructured nodeOk ∧ ∀ p, f (t.leaf p) = true
  /-- The acceptance rate is at most the error plus its complement times the success
  probability, uniformly over all acceptance functions. -/
  success : ∀ f, acceptRate f ≤ κ + (1 - κ) * Pr{let z ← runFinder find f}[z.1.isSome]
  /-- Complete-run cost is bounded without conditioning on success. -/
  cost : ∀ f, expectedCalls (runFinder find f) ≤ T

/-- A tree finder succeeds with probability at least the acceptance rate minus its error. -/
theorem IsTreeFinder.acceptRate_sub_le [Fintype R] [LinearOrder R] [∀ r, Fintype (C r)]
    {k : R → ℕ} {nodeOk : (r : R) → (Fin (k r) → C r) → Prop}
    {find : OracleComp (unifSpec + accSpec C) (Option (VecTree C k))} {κ T : ℝ≥0∞}
    (h : IsTreeFinder k nodeOk find κ T) (f : ((r : R) → C r) → Bool) :
    acceptRate f - κ ≤ Pr{let z ← runFinder find f}[z.1.isSome] :=
  tsub_le_iff_left.mpr ((h.success f).trans
    (add_le_add le_rfl (mul_le_of_le_one_left zero_le tsub_le_self)))

/-- Threshold knowledge error `1 − ∏ᵣ (1 − (kᵣ − 1)/|Cᵣ|)`: the knowledge error of a protocol
that is special sound with threshold `k r` and challenge set `C r` in each round (Attema, Cramer
and Kohl, Remark 1, eq. (3)). -/
@[expose] noncomputable def thresholdError [Fintype R]
    (C : R → Type) [∀ r, Fintype (C r)] (k : R → ℕ) : ℝ≥0∞ :=
  1 - ∏ r, (1 - ((k r - 1 : ℕ) : ℝ≥0∞) / (Fintype.card (C r) : ℝ≥0∞))

end Rewinding
