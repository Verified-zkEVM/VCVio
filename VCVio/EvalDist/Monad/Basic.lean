/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.EvalDist.Monad.Support
public import VCVio.EvalDist.Defs.Basic
public import ToMathlib.Data.ENNReal.Gauss
import VCVio.EvalDist.Monad.Measure

/-!
# Evaluation Distributions of Computations with `Bind`

File for lemmas about `evalSPMF` and `support` involving the monadic `pure` and `bind`.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u} {m : Type u → Type v}

open ENNReal OracleComp.EvalDist

/- The monad/functor laws are confluent (terminating) rewrites. Tagging them for `grind` lets it
normalize a computation's structure (`mx >>= pure = mx`, reassociation, `f <$> pure a = pure (f a)`)
*before* it falls into `probOutput`/`tsum` expansion — turning what would otherwise be a `grind`
explosion on a structured-computation equality into a quick solve. `pure_bind` is not listed: core
already ships it in the default set (`attribute [grind <=] pure_bind` in `Init.Control.Lawful`),
and re-tagging it would add a redundant E-match entry. (The analogous
`bind_pure_comp`/`map_eq_bind` laws are deliberately omitted: their function argument sits under a
binder that `grind`'s pattern compiler cannot index; so do `pure_seq`/`seq_pure`, whose `Seq.seq`
thunk argument makes even their LHS an invalid pattern. `Functor.map_map` is binder-free and joins
the set.) -/
attribute [grind =] bind_pure bind_assoc map_pure Functor.map_map

/-! ## Bounds that use only the lift

Statements about a single computation's evaluation distribution need neither `Monad m` nor the
lawful-lift class. -/

section lift

variable [MonadLiftT m SPMF]

/-! ## Expectation sums -/

/-- Expectation is monotone in the functional. -/
lemma tsum_probOutput_mul_mono (mx : m α) {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    ∑' x, Pr[= x | mx] * f x ≤ ∑' x, Pr[= x | mx] * g x :=
  expectedValue_mono mx h

/-- A finite sum inside an expectation may be taken outside: linearity of expectation over a
`Finset` of summands. -/
lemma tsum_probOutput_mul_finsetSum {ι' : Type*} (mx : m α) (s : Finset ι') (f : ι' → α → ℝ≥0∞) :
    ∑' x, Pr[= x | mx] * (∑ i ∈ s, f i x) = ∑ i ∈ s, ∑' x, Pr[= x | mx] * f i x := by
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable

end lift

variable [Monad m]

/-! ## Probabilities of `pure` -/

section pure
@[grind =]
lemma evalSPMF_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] {α : Type u} (x : α) :
    𝒮[(pure x : m α)] = pure x := by simp [evalSPMF]

@[simp]
lemma evalSPMF_comp_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    evalSPMF ∘ (pure : α → m α) = pure := by aesop

@[simp]
lemma evalSPMF_comp_pure' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (f : α → β) :
    evalSPMF ∘ (pure : β → m β) ∘ f = pure ∘ f := by grind

@[simp, grind =]
lemma probOutput_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probOutput_pure_self [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    Pr[= x | (pure x : m α)] = 1 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probOutput_pure_eq_indicator [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator {y} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

@[simp, grind =]
lemma probEvent_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) (p : α → Prop)
    [DecidablePred p] :
    Pr[ p | (pure x : m α)] = if p x then 1 else 0 := by
  aesop (rule_sets := [UnfoldEvalDist])

/-- Fallback when we don't have decidable equality. -/
@[grind =]
lemma probEvent_pure_eq_indicator [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α)
    (p : α → Prop) :
    Pr[ p | (pure x : m α)] = Set.indicator {x | p x} (Function.const α 1) x := by
  aesop (rule_sets := [UnfoldEvalDist])

-- Keep the direct pure rule ahead of the generic NeverFails rule, which lives in a later module.
@[simp 1100, grind =]
lemma probFailure_pure [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    Pr[⊥ | (pure x : m α)] = 0 := by aesop (rule_sets := [UnfoldEvalDist])

@[simp]
lemma tsum_probOutput_pure' [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑' y : α, Pr[= x | (pure y : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

@[simp]
lemma sum_probOutput_pure' [Fintype α] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (x : α) :
    ∑ y : α, Pr[= x | (pure y : m α)] = 1 := by
  have : DecidableEq α := Classical.decEq α; simp

end pure

/-! ## Probabilities of `bind` -/

section bind

@[grind =]
lemma evalSPMF_bind [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α) (my : α → m β) :
    𝒮[mx >>= my] = 𝒮[mx] >>= fun x => 𝒮[my x] :=
  monadLift_bind mx my

section bind_tsum

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

@[grind =]
lemma probOutput_bind_eq_tsum (mx : m α)
    (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput_def]

@[grind =]
lemma probEvent_bind_eq_tsum (mx : m α)
    (my : α → m β) (q : β → Prop) :
    Pr[ q | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[ q | my x] := by
  simp only [probEvent_eq_tsum_indicator, Set.indicator, Set.mem_ofPred_eq, probOutput_bind_eq_tsum,
    ← ENNReal.tsum_mul_left, mul_ite, mul_zero]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => by split_ifs <;> simp

/-- `probOutput_bind_eq_tsum` with the sum packaged as an `expectedValue`, the head `gcongr`
descends through. -/
lemma probOutput_bind_eq_expectedValue (mx : m α)
    (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = expectedValue mx fun x => Pr[= y | my x] :=
  probOutput_bind_eq_tsum mx my y

/-- `probEvent_bind_eq_tsum` with the sum packaged as an `expectedValue`. -/
lemma probEvent_bind_eq_expectedValue (mx : m α)
    (my : α → m β) (q : β → Prop) :
    Pr[ q | mx >>= my] = expectedValue mx fun x => Pr[ q | my x] :=
  probEvent_bind_eq_tsum mx my q

end bind_tsum

@[grind =]
lemma probFailure_bind_eq_add_tsum [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] (mx : m α)
    (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : α, Pr[= x | mx] * Pr[⊥ | my x] := by
  simp [probFailure_def, Option.elimM, tsum_option, probOutput_def,
    SPMF.apply_eq_toPMF_some]

@[grind =]
lemma probFailure_bind_eq_add_tsum_support [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by
  rw [probFailure_bind_eq_add_tsum]
  congr 1
  rw [tsum_subtype (support mx) fun x => Pr[= x | mx] * Pr[⊥ | my x]]
  refine tsum_congr fun x => ?_
  aesop (add simp Set.indicator)

-- `grind`-safe in isolation: this support-quantifier characterization saturates `grind` only in
-- combination with the `probEvent_eq_one_iff` family (kept `simp`-only). See `probability.md`.
@[simp, grind =]
lemma probFailure_bind_eq_zero_iff [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m] (mx : m α) (my : α → m β) :
    Pr[⊥ | mx >>= my] = 0 ↔ Pr[⊥ | mx] = 0 ∧ ∀ x ∈ support mx, Pr[⊥ | my x] = 0 := by
  simp [probFailure_bind_eq_add_tsum, or_iff_not_imp_left]

/-- Version of `probEvent_bind_eq_tsum` that sums only over the subtype given by the support
of the first computation, avoiding edge cases that the first computation never reaches. -/
lemma probEvent_bind_eq_tsum_subtype [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m] (mx : m α) (my : α → m β) (q : β → Prop) :
    Pr[ q | mx >>= my] = ∑' x : support mx, Pr[= x | mx] * Pr[ q | my x] := by
  rw [tsum_subtype _ (fun x ↦ Pr[= x | mx] * Pr[ q | my x]), probEvent_bind_eq_tsum]
  refine tsum_congr (fun x ↦ ?_)
  by_cases hx : x ∈ support mx <;> aesop

/-- If `Pr[q | my x] ≤ ε` for every `x` in the support of `mx`, then the bound also
holds for the bind. -/
lemma probEvent_bind_le_of_forall_le [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    {mx : m α} {my : α → m β} {q : β → Prop} {ε : ENNReal}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ ε) :
    Pr[ q | mx >>= my] ≤ ε := by
  rw [probEvent_bind_eq_expectedValue]
  exact expectedValue_le_of_support h

/-- If a continuation event is bounded by `ε` exactly on a prefix event and is
impossible off that event, then only the prefix mass is charged. -/
lemma probEvent_bind_le_probEvent_mul [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m]
    {mx : m α} {my : α → m β} {q : β → Prop} {p : α → Prop} {ε : ENNReal}
    (hle : ∀ x ∈ support mx, p x → Pr[ q | my x] ≤ ε)
    (hzero : ∀ x ∈ support mx, ¬ p x → Pr[ q | my x] = 0) :
    Pr[ q | mx >>= my] ≤ Pr[ p | mx] * ε := by
  classical
  rw [probEvent_bind_eq_expectedValue, ← expectedValue_ite_one, ← expectedValue_mul_const]
  gcongr with x hx
  by_cases hp : p x
  · simp only [ite_eq_left hp, one_mul]; exact hle x hx hp
  · simp only [ite_eq_right hp, zero_mul, hzero x hx hp, le_refl]

lemma probOutput_bind_eq_sum_finSupport [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadAttach m] [EvalDistCompatible m] [HasEvalFinset m]
    (mx : m α) (my : α → m β) [DecidableEq α] (y : β) :
    Pr[= y | mx >>= my] = ∑ x ∈ finSupport mx, Pr[= x | mx] * Pr[= y | my x] :=
  (probOutput_bind_eq_tsum mx my y).trans (tsum_eq_sum' <| by simp)

section const

section support

variable [LawfulMonad m] [MonadAttach m] [ExactMonadAttach m]

lemma support_bind_const (mx : m α) (my : m β) :
    support (mx >>= fun _ => my) = {y ∈ support my | (support mx).Nonempty} := by
  grind [= Set.Nonempty]

lemma finSupport_bind_const [HasEvalFinset m]
    [DecidableEq β] [DecidableEq α] (mx : m α) (my : m β) :
    finSupport (mx >>= fun _ => my) = if (finSupport mx).Nonempty then finSupport my else ∅ := by
  ext x
  simp only [finSupport_bind, Finset.mem_biUnion]
  split_ifs <;> simp_all [Finset.nonempty_def]

end support

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

/-- The compatibility adapter satisfies the Giry `pure`/`bind` laws for every lawful `SPMF`
lift, so the `𝒟`-level laws (`evalDist_pure`, `evalDist_bind`, `evalDist_map`, …) hold with no
measure specification in scope. -/
instance instLawfulEvalDistSemanticsOfMonadLiftTSPMF : LawfulEvalDistSemantics m where
  denote_pure x := by
    change (𝒮[(pure x : m _)]).toMeasure = _
    simp
  denote_bind mx f hf := by
    change (𝒮[mx >>= f]).toMeasure = _
    rw [evalSPMF_bind]
    exact (𝒮[mx]).toMeasure_bind' _ hf

variable [MonadAttach m] [EvalDistCompatible m]

lemma probOutput_bind_of_const (mx : m α)
    {my : α → m β} {y : β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[= y | my x] = r) :
    Pr[= y | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  rw [probOutput_bind_eq_expectedValue, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  exact expectedValue_congr_of_support h

@[simp, grind =_]
lemma probOutput_bind_const (mx : m α) (my : m β) (y : β) :
    Pr[= y | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[= y | my] := by
  rw [probOutput_bind_of_const mx fun _ _ => rfl]

lemma probEvent_bind_of_const (mx : m α)
    {my : α → m β} {p : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ p | my x] = r) :
    Pr[ p | mx >>= my] = (1 - Pr[⊥ | mx]) * r := by
  rw [probEvent_bind_eq_expectedValue, ← tsum_probOutput_eq_sub, ← ENNReal.tsum_mul_right]
  exact expectedValue_congr_of_support h

@[simp, grind =_]
lemma probEvent_bind_const (mx : m α) (my : m β) (p : β → Prop) :
    Pr[ p | mx >>= fun _ => my] = (1 - Pr[⊥ | mx]) * Pr[ p | my] := by
  rw [probEvent_bind_of_const mx fun _ _ => rfl]

/-- Write the probability of `mx >>= my` failing given that `my` has constant failure chance over
the possible outputs in `support mx` as a fixed expression without any sums. -/
lemma probFailure_bind_of_const
    {mx : m α} {my : α → m β} {r : ℝ≥0∞} (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r * (1 - Pr[⊥ | mx]) := by
  calc Pr[⊥ | mx >>= my]
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by grind
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * r := by grind
    _ = Pr[⊥ | mx] + r * (1 - Pr[⊥ | mx]) := by
      rw [ENNReal.tsum_mul_right, mul_comm, tsum_support_probOutput_eq_sub]

lemma probFailure_bind_of_const'
    {mx : m α} {my : α → m β} {r : ℝ≥0∞} (hr : r ≠ ⊤) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + r - Pr[⊥ | mx] * r := by
  rw [probFailure_bind_of_const h, ENNReal.mul_sub, AddLECancellable.add_tsub_assoc_of_le,
    mul_comm Pr[⊥ | mx] r, mul_one] <;> simp [hr, ENNReal.mul_eq_top]

@[simp, grind =_]
lemma probFailure_bind_const (mx : m α) (my : m β) :
    Pr[⊥ | mx >>= fun _ => my] = Pr[⊥ | mx] + Pr[⊥ | my] - Pr[⊥ | mx] * Pr[⊥ | my] := by
  rw [probFailure_bind_of_const' (by simp) fun _ _ => rfl]

lemma probFailure_bind_eq_sub_mul
    (mx : m α) (my : α → m β) (r : ℝ≥0∞) (hr : r ≠ ⊤) (h : ∀ x ∈ support mx, Pr[⊥ | my x] = r) :
    Pr[⊥ | mx >>= my] = 1 - (1 - Pr[⊥ | mx]) * (1 - r) := by
  rcases (support mx).eq_empty_or_nonempty with h' | ⟨x, hx⟩
  · rw [probFailure_bind_of_const' hr h, probFailure_eq_one h']
    simp [ENNReal.add_sub_cancel_right hr]
  · rw [probFailure_bind_of_const' hr h,
      ENNReal.one_sub_one_sub_mul_one_sub (by simp) (h x hx ▸ probFailure_le_one)]

end const

section mono

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadAttach m] [EvalDistCompatible m]

lemma probFailure_bind_le_add_of_forall {mx : m α}
    {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) :
    Pr[⊥ | mx >>= my] ≤ Pr[⊥ | mx] + (1 - Pr[⊥ | mx]) * r := by
  calc Pr[⊥ | mx >>= my]
    _ = Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * Pr[⊥ | my x] := by
      rw [probFailure_bind_eq_add_tsum_support]
    _ ≤ Pr[⊥ | mx] + ∑' x : support mx, Pr[= x | mx] * r := by
      gcongr with x
      exact hr x.1 x.2
    _ ≤ Pr[⊥ | mx] + (1 - Pr[⊥ | mx]) * r := by simp [ENNReal.tsum_mul_right]

/-- Version of `probFailure_bind_le_of_forall` when `mx` never fails. -/
lemma probFailure_bind_le_of_forall {mx : m α}
    (h' : Pr[⊥ | mx] = 0) {my : α → m β} {r : ℝ≥0∞}
    (hr : ∀ x ∈ support mx, Pr[⊥ | my x] ≤ r) : Pr[⊥ | mx >>= my] ≤ r := by
  refine (probFailure_bind_le_add_of_forall hr).trans (by simp [h'])

end mono

end bind

/-! ## Congruence and monotonicity for `bind` -/

section congr_mono

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  [MonadAttach m] [EvalDistCompatible m]

lemma probOutput_bind_congr {mx : m α} {ob₁ ob₂ : α → m β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | ob₁ x] = Pr[= y | ob₂ x]) :
    Pr[= y | mx >>= ob₁] = Pr[= y | mx >>= ob₂] := by
  simp only [probOutput_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probOutput_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (y : β)
    (h : ∀ x, Pr[= y | ob₁ x] = Pr[= y | ob₂ x]) :
    Pr[= y | mx >>= ob₁] = Pr[= y | mx >>= ob₂] :=
  probOutput_bind_congr fun x _ => h x

lemma probOutput_bind_mono {mx : m α}
    {my : α → m β} {oc : α → m γ} {y : β} {z : γ}
    (h : ∀ x ∈ support mx, Pr[= y | my x] ≤ Pr[= z | oc x]) :
    Pr[= y | mx >>= my] ≤ Pr[= z | mx >>= oc] := by
  rw [probOutput_bind_eq_expectedValue, probOutput_bind_eq_expectedValue]
  gcongr with x hx
  exact h x hx

lemma probEvent_bind_congr {mx : m α} {ob₁ ob₂ : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, Pr[ q | ob₁ x] = Pr[ q | ob₂ x]) :
    Pr[ q | mx >>= ob₁] = Pr[ q | mx >>= ob₂] := by
  simp only [probEvent_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

lemma probEvent_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β} (q : β → Prop)
    (h : ∀ x, Pr[ q | ob₁ x] = Pr[ q | ob₂ x]) :
    Pr[ q | mx >>= ob₁] = Pr[ q | mx >>= ob₂] :=
  probEvent_bind_congr fun x _ => h x

lemma evalSPMF_bind_congr {mx : m α} {ob₁ ob₂ : α → m β}
    (h : ∀ x ∈ support mx, 𝒮[ob₁ x] = 𝒮[ob₂ x]) :
    𝒮[mx >>= ob₁] = 𝒮[mx >>= ob₂] :=
  evalSPMF_ext fun y => probOutput_bind_congr fun x hx => evalSPMF_ext_iff.mp (h x hx) y

lemma evalSPMF_bind_congr' (mx : m α) {ob₁ ob₂ : α → m β}
    (h : ∀ x, 𝒮[ob₁ x] = 𝒮[ob₂ x]) :
    𝒮[mx >>= ob₁] = 𝒮[mx >>= ob₂] :=
  evalSPMF_bind_congr fun x _ => h x

lemma probEvent_bind_mono {mx : m α} {my oc : α → m β} {q : β → Prop}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ Pr[ q | oc x]) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] := by
  rw [probEvent_bind_eq_expectedValue, probEvent_bind_eq_expectedValue]
  gcongr with x hx
  exact h x hx

lemma probEvent_bind_congr_div_const {mx : m α}
    {ob₁ ob₂ : α → m β} {q : β → Prop} {r : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ q | ob₁ x] = Pr[ q | ob₂ x] / r) :
    Pr[ q | mx >>= ob₁] = Pr[ q | mx >>= ob₂] / r := by
  simp only [probEvent_bind_eq_tsum, div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support mx
  · rw [h x hx, div_eq_mul_inv, mul_assoc]
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- Union bound for bind: if `Pr[ ¬p | mx] ≤ ε₁` and `Pr[ ¬q | my x] ≤ ε₂` for all `x` satisfying
`p`, then `Pr[ ¬q | mx >>= my] ≤ ε₁ + ε₂`. Useful for sequential composition of error bounds. -/
lemma probEvent_bind_le_add {mx : m α} {my : α → m β}
    {p : α → Prop} {q : β → Prop} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : Pr[ fun x => ¬p x | mx] ≤ ε₁)
    (h₂ : ∀ x ∈ support mx, p x → Pr[ fun y => ¬q y | my x] ≤ ε₂) :
    Pr[ fun y => ¬q y | mx >>= my] ≤ ε₁ + ε₂ := by
  classical
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have hs : ∀ᵐ x ∂𝒟[mx], x ∈ support mx := by
    rw [MeasureTheory.ae_iff]
    simpa only [evalDist_apply_setOf] using
      (probEvent_eq_zero_iff (mx := mx) (p := fun x => x ∉ support mx)).2 (by simp)
  have hbound := evalDist_bind_apply_le_add_lintegral_of_bad
    (bad := {x | ¬p x}) (event := {y | ¬q y}) mx my Measurable.of_discrete
    MeasurableSet.of_discrete MeasurableSet.of_discrete (fun _ => 0) (by
      filter_upwards [hs] with x hx hp
      simpa only [evalDist_apply_setOf, zero_add] using h₂ x hx (not_not.mp hp))
  have h₁' : 𝒟[mx] {x | ¬p x} ≤ ε₁ := by simpa only [evalDist_apply_setOf] using h₁
  simpa only [evalDist_apply_setOf] using hbound.trans (by
    simpa only [MeasureTheory.lintegral_zero, add_zero] using add_le_add_left h₁' ε₂)

/-- `probEvent` version of `probEvent_bind_mono` with additive error bound. -/
lemma probEvent_bind_congr_le_add {mx : m α} {my oc : α → m β}
    {q : β → Prop} {ε : ℝ≥0∞}
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ Pr[ q | oc x] + ε) :
    Pr[ q | mx >>= my] ≤ Pr[ q | mx >>= oc] + ε := by
  simp only [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ q | my x]
      ≤ ∑' x, (Pr[= x | mx] * Pr[ q | oc x] + Pr[= x | mx] * ε) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact (mul_le_mul' le_rfl (h x hx)).trans_eq (left_distrib ..)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ ≤ (∑' x, Pr[= x | mx] * Pr[ q | oc x]) + ε := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        gcongr
        exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

end congr_mono

/-! ## Swapping independent draws -/

section swap_compl

variable [MonadLiftT m SPMF]

/-- Swapping two independent random draws preserves the output distribution: although
`mx >>= fun a => my >>= fun b => f a b` and `my >>= fun b => mx >>= fun a => f a b` need not be
equal as `m`-computations when `m` is non-commutative, the two draws are independent, so their
output distributions agree. The `probEvent`/`probOutput` forms (`probEvent_bind_bind_swap`,
`probOutput_bind_bind_swap`) are corollaries. -/
lemma evalSPMF_bind_bind_swap [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : m β) (f : α → β → m γ) :
    𝒮[mx >>= fun a => my >>= fun b => f a b] =
      𝒮[my >>= fun b => mx >>= fun a => f a b] := by
  refine evalSPMF_ext fun x => ?_
  simp only [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => mul_left_comm _ _ _

/-- Swapping two independent random draws preserves probability of any event. Corollary of
`evalSPMF_bind_bind_swap`. -/
lemma probEvent_bind_bind_swap [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : m β) (f : α → β → m γ) (q : γ → Prop) :
    Pr[ q | mx >>= fun a => my >>= fun b => f a b] =
      Pr[ q | my >>= fun b => mx >>= fun a => f a b] := by
  rw [probEvent_def, probEvent_def, evalSPMF_bind_bind_swap]

/-- Swapping two independent random draws preserves the probability of any fixed output. Corollary
of `evalSPMF_bind_bind_swap`. -/
lemma probOutput_bind_bind_swap [LawfulMonadLiftT m SPMF]
    (mx : m α) (my : m β) (f : α → β → m γ) (z : γ) :
    Pr[= z | mx >>= fun a => my >>= fun b => f a b] =
      Pr[= z | my >>= fun b => mx >>= fun a => f a b] := by
  rw [probOutput_def, probOutput_def, evalSPMF_bind_bind_swap]

end swap_compl

/-! ## Expectation algebra for nonnegative functionals -/

section tsum_probOutput_mul

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

/-- Expectation of a nonnegative functional under a `pure` computation. -/
@[simp]
lemma tsum_probOutput_pure_mul (y : α) (f : α → ℝ≥0∞) :
    ∑' z, Pr[= z | (pure y : m α)] * f z = f y := by
  classical
  simp

end tsum_probOutput_mul
