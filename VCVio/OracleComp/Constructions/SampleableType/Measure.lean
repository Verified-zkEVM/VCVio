/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.Replicate.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.OracleComp.SimSemantics.Measure
public import ToMathlib.MeasureTheory.DiscreteInstances
import VCVio.EvalDist.Monad.Measure
import VCVio.EvalDist.ProbabilityBounds
import Mathlib.Logic.Equiv.Bool

/-!
# Measure laws for uniform sampling constructions

Finite-range sampling and transport through an equivalence preserve the uniform output measure
certified by `SampleableType`. Events of a uniform sample are counting statements: comparisons with
fractions of the sample space reduce to comparisons of counts, probability one and zero are
universal and empty events, and independent uniform draws combined by a bijection are a single
uniform draw. Every uniform sampler of a type denotes the same measure, so statements about `$ᵗ α`
do not depend on the chosen sampler.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampleableType

/-- Every singleton of a uniform finite sample has the reciprocal cardinality mass. -/
@[simp↓ high, grind norm↓]
theorem evalDist_uniformSample_singleton {α : Type} [SampleableType α] [_root_.Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (x : α) :
    𝒟[($ᵗ α : ProbComp α)] {x} = (Fintype.card α : ENNReal)⁻¹ := by
  rw [evalDist_uniformSample, uniformOn_univ_apply_singleton]

/-- A uniform finite sample satisfies a decidable event with its accepted fraction of outputs.
For events it takes precedence over the average `wp_uniformSample_eq_sum`, wherever in a `simp`
run the event appears. -/
@[simp high, grind norm↓]
theorem prEvent_uniformSample {α : Type} [SampleableType α] [_root_.Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Pr{let x ← $ᵗ α}[p x] = (Finset.univ.filter p).card / (Fintype.card α : ENNReal) := by
  classical
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, SampleableType.evalDist_uniformSample, uniformOn_univ]
  have hset : {x | p x} = (Finset.univ.filter p : Finset α) := by ext x; simp
  rw [hset, Measure.count_apply_finset]

/-- The finite sampler directly denotes a uniform measure. -/
theorem evalDist_fin (n : ℕ) :
    𝒟[(SampleableType.Fin n).selectElem] = uniformOn Set.univ :=
  (SampleableType.Fin n).evalDist_selectElem_eq_uniform

/-- A sample from any nonempty `Fin n` denotes its uniform measure. -/
theorem evalDist_fin_neZero (n : ℕ) [NeZero n] :
    𝒟[$ᵗ (_root_.Fin n)] = uniformOn Set.univ := by
  exact SampleableType.evalDist_uniformSample

/-- Transporting a uniformly distributed sampler through an equivalence stays uniform. -/
theorem evalDist_ofEquiv {α β : Type} [SampleableType α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (e : α ≃ β) :
    𝒟[(SampleableType.ofEquiv e).selectElem] = uniformOn Set.univ :=
  (SampleableType.ofEquiv e).evalDist_selectElem_eq_uniform

/-- Finite enumeration gives a uniform sampler. -/
theorem evalDist_finEnum {α : Type} [h : FinEnum α] [_root_.Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    𝒟[(FinEnum.SampleableType α).selectElem] = uniformOn Set.univ :=
  (FinEnum.SampleableType α).evalDist_selectElem_eq_uniform

/-- Independent uniform samples give the uniform measure on a product type. -/
theorem evalDist_prod {α β : Type} [SampleableType α] [SampleableType β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    𝒟[$ᵗ (α × β)] = uniformOn Set.univ :=
  SampleableType.evalDist_uniformSample

/-- A sampled bit vector has the uniform measure. -/
@[simp]
theorem evalDist_bitVec (n : ℕ) :
    𝒟[$ᵗ BitVec n] = uniformOn Set.univ :=
  SampleableType.evalDist_uniformSample

/-! ## Counting events of a uniform sample -/

/-- A uniform sample satisfies an event with probability one exactly when every element does. -/
theorem prEvent_uniformSample_eq_one_iff {α : Type} [SampleableType α] (p : α → Prop) :
    Pr{let x ← $ᵗ α}[p x] = 1 ↔ ∀ x, p x := by
  rw [OracleComp.prEvent_eq_one_iff, support_uniformSample]
  simp

/-- A uniform sample satisfies an event with probability zero exactly when no element does. -/
theorem prEvent_uniformSample_eq_zero_iff {α : Type} [SampleableType α] (p : α → Prop) :
    Pr{let x ← $ᵗ α}[p x] = 0 ↔ ∀ x, ¬ p x := by
  rw [OracleComp.prEvent_eq_zero_iff, support_uniformSample]
  simp

/-- A uniform sample satisfies an event with positive probability exactly when some element
does. -/
theorem prEvent_uniformSample_pos_iff {α : Type} [SampleableType α] (p : α → Prop) :
    0 < Pr{let x ← $ᵗ α}[p x] ↔ ∃ x, p x := by
  rw [OracleComp.prEvent_pos_iff, support_uniformSample]
  simp

/-- The probability of drawing one particular element uniformly. -/
theorem prEvent_uniformSample_eq_singleton {α : Type} [SampleableType α] [_root_.Fintype α]
    (a : α) : Pr{let x ← $ᵗ α}[x = a] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton, evalDist_uniformSample_singleton]

/-- An expectation over a uniform draw from a finite type is the average of the observation.
`simp` applies it through the simproc `wp_uniformSample_sum` to observations that are not
events; an event is counted by `prEvent_uniformSample`. -/
theorem wp_uniformSample_eq_sum {α : Type} [SampleableType α] [_root_.Fintype α]
    (g : α → ENNReal) : wp⟦($ᵗ α : ProbComp α)⟧ g = (∑ x, g x) / Fintype.card α := by
  rw [wp_eq_sum_fintype, ENNReal.div_eq_inv_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [prEvent_uniformSample_eq_singleton]

open Lean Meta Simp ProbabilityNotation in
/-- `wp_uniformSample_eq_sum` for an observation that is not an event, `predInd p` or an
indicator that normalization folds into one. -/
simproc [simp] wp_uniformSample_sum (@Std.Internal.Do.WP.wp _ _ _ _ _ _ ?_ _ _ _) := fun e => do
  unless e.isAppOfArity ``Std.Internal.Do.WP.wp 10 do return .continue
  let g := e.getArg! 8
  if g.isAppOfArity ``predInd 2 || isIndicatorLambda g then return .continue
  let some (rhs, pf) ← rewriteWith? ``wp_uniformSample_eq_sum e | return .continue
  return .visit { expr := rhs, proof? := pf }

/-- Each length-`n` list is drawn by `n` independent uniform samples with probability
`(|α| ^ n)⁻¹`. -/
theorem prEvent_replicate_uniformSample {α : Type} [SampleableType α] [_root_.Fintype α]
    {n : ℕ} {xs : List α} (hlen : xs.length = n) :
    Pr{let v ← OracleComp.replicate n ($ᵗ α)}[v = xs] =
      ((Fintype.card α ^ n : ℕ) : ℝ≥0∞)⁻¹ := by
  induction n generalizing xs with
  | zero =>
      obtain rfl : xs = [] := List.eq_nil_of_length_eq_zero hlen
      simp [OracleComp.replicate_zero]
  | succ n ih =>
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
      rw [OracleComp.replicate_succ_bind, prEvent_bind,
        OracleComp.prEvent_bind_eq_mul_of_unique _ _ y _
        fun x' _ hx' => by
          obtain ⟨xs, -, hxs⟩ := (mem_support_bind_iff _ _ _).mp hx'
          exact (List.cons.inj ((mem_support_pure_iff' (m := ProbComp) _ _).mp hxs)).1]
      simp only [expect_norm, List.cons.injEq, true_and]
      rw [prEvent_uniformSample_eq_singleton, ih (by simpa using hlen), pow_succ', Nat.cast_mul,
        ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

section counting

variable {α : Type} [SampleableType α] [_root_.Fintype α] (p : α → Prop) [DecidablePred p]

/-- A uniform event is below a fraction of the sample space exactly when the count is. -/
theorem prEvent_uniformSample_lt_div_iff {c : ℕ} :
    Pr{let x ← $ᵗ α}[p x] < c / (Fintype.card α : ℝ≥0∞) ↔
      (Finset.univ.filter p).card < c := by
  rw [prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp)]
  exact Nat.cast_lt

/-- A uniform event is at most a fraction of the sample space exactly when the count is. -/
theorem prEvent_uniformSample_le_div_iff {c : ℕ} :
    Pr{let x ← $ᵗ α}[p x] ≤ c / (Fintype.card α : ℝ≥0∞) ↔
      (Finset.univ.filter p).card ≤ c := by
  rw [← not_lt, prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp),
    Nat.cast_lt, not_lt]

/-- A fraction of the sample space is below a uniform event exactly when the count is. -/
theorem div_lt_prEvent_uniformSample_iff {c : ℕ} :
    c / (Fintype.card α : ℝ≥0∞) < Pr{let x ← $ᵗ α}[p x] ↔
      c < (Finset.univ.filter p).card := by
  rw [prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp)]
  exact Nat.cast_lt

/-- A fraction of the sample space is at most a uniform event exactly when the count is. -/
theorem div_le_prEvent_uniformSample_iff {c : ℕ} :
    c / (Fintype.card α : ℝ≥0∞) ≤ Pr{let x ← $ᵗ α}[p x] ↔
      c ≤ (Finset.univ.filter p).card := by
  rw [← not_lt, prEvent_uniformSample, ENNReal.div_lt_div_iff_left (by simp) (by simp),
    Nat.cast_lt, not_lt]

/-- A uniform event equals a fraction of the sample space exactly when the count does. -/
theorem prEvent_uniformSample_eq_div_iff {c : ℕ} :
    Pr{let x ← $ᵗ α}[p x] = c / (Fintype.card α : ℝ≥0∞) ↔
      (Finset.univ.filter p).card = c := by
  rw [le_antisymm_iff, prEvent_uniformSample_le_div_iff, div_le_prEvent_uniformSample_iff,
    le_antisymm_iff]

/-- A uniform event as a real-valued fraction. -/
theorem prEvent_uniformSample_eq_ofReal :
    Pr{let x ← $ᵗ α}[p x] =
      ENNReal.ofReal ((Finset.univ.filter p).card / Fintype.card α : ℝ) := by
  rw [prEvent_uniformSample, ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos)]
  simp

end counting

/-! ## Transport between uniform samples -/

section transport

variable {α β γ : Type} [SampleableType α] [SampleableType β]

/-- A bijection of sample spaces carries a uniform sample to a uniform sample. -/
theorem map_uniformSample_evalDistEq_of_bijective {f : α → β} (hf : Function.Bijective f) :
    f <$> ($ᵗ α : ProbComp α) =ᵈ ($ᵗ β : ProbComp β) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have h : 𝒟[f <$> ($ᵗ α : ProbComp α)] = 𝒟[($ᵗ β : ProbComp β)] := by
    rw [evalDist_map_of_discrete, evalDist_uniformSample, evalDist_uniformSample]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete hf
  exact EvalDistEq.of_evalDist_eq h

/-- Transport a uniform event along a bijection of sample spaces. -/
theorem prEvent_uniformSample_comp_of_bijective {f : α → β} (hf : Function.Bijective f)
    (p : β → Prop) :
    Pr{let x ← $ᵗ α}[p (f x)] = Pr{let y ← $ᵗ β}[p y] := by
  rw [← prEvent_map]
  exact (map_uniformSample_evalDistEq_of_bijective hf).prEvent_eq p

/-- Transport a uniform event along an equivalence of sample spaces. -/
theorem prEvent_uniformSample_equiv (e : α ≃ β) (p : β → Prop) :
    Pr{let x ← $ᵗ α}[p (e x)] = Pr{let y ← $ᵗ β}[p y] :=
  prEvent_uniformSample_comp_of_bijective e.bijective p

/-- Two independent uniform draws combined by a bijection are one uniform draw. -/
theorem prEvent_uniformSample_pair_of_bijective [SampleableType γ] {g : α → β → γ}
    (hg : Function.Bijective (Function.uncurry g)) (p : γ → Prop) :
    Pr{let x ← $ᵗ α; let y ← $ᵗ β}[p (g x y)] = Pr{let z ← $ᵗ γ}[p z] := by
  have h : Function.uncurry g <$> (do let x ← $ᵗ α; let y ← $ᵗ β; return (x, y) :
      ProbComp (α × β)) =ᵈ ($ᵗ γ : ProbComp γ) := by
    refine evalDistEq_iff_evalDist_eq.mpr ?_
    let : MeasurableSpace α := ⊤
    let : MeasurableSpace β := ⊤
    let : MeasurableSpace γ := ⊤
    rw [evalDist_map_of_discrete, evalDist_pair, evalDist_uniformSample,
      evalDist_uniformSample, evalDist_uniformSample, ← uniformOn_univ_prod]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete hg
  simpa only [expect_norm, Function.uncurry_apply_pair] using h.prEvent_eq p

/-- A uniform draw from a product is two independent uniform draws. -/
theorem prEvent_uniformSample_prod (p : α × β → Prop) :
    Pr{let z ← $ᵗ (α × β)}[p z] = Pr{let x ← $ᵗ α; let y ← $ᵗ β}[p (x, y)] :=
  (prEvent_uniformSample_pair_of_bijective (g := Prod.mk) Function.bijective_id p).symm

/-- A uniform bound after fixing the first coordinate bounds an event of a uniform product. -/
theorem prEvent_uniformSample_prod_le_of_forall_fst (p : α × β → Prop) {ε : ℝ≥0∞}
    (h : ∀ x, Pr{let y ← $ᵗ β}[p (x, y)] ≤ ε) :
    Pr{let z ← $ᵗ (α × β)}[p z] ≤ ε := by
  rw [prEvent_uniformSample_prod]
  simpa only [expect_norm] using
    prEvent_bind_le_of_forall_le ($ᵗ α)
      (fun x => do let y ← $ᵗ β; return (x, y)) p
      (fun x => by simpa only [expect_norm] using h x)

/-- A uniform bound after fixing the second coordinate bounds an event of a uniform product. -/
theorem prEvent_uniformSample_prod_le_of_forall_snd (p : α × β → Prop) {ε : ℝ≥0∞}
    (h : ∀ y, Pr{let x ← $ᵗ α}[p (x, y)] ≤ ε) :
    Pr{let z ← $ᵗ (α × β)}[p z] ≤ ε := by
  rw [← prEvent_uniformSample_pair_of_bijective
    (g := fun y x => (x, y)) (Equiv.prodComm β α).bijective]
  simpa only [expect_norm] using
    prEvent_bind_le_of_forall_le ($ᵗ β)
      (fun y => do let x ← $ᵗ α; return (x, y)) p
      (fun y => by simpa only [expect_norm] using h y)

/-- The first coordinate of a uniform product draw is a uniform draw. -/
theorem prEvent_uniformSample_fst (p : α → Prop) :
    Pr{let z ← $ᵗ (α × β)}[p z.1] = Pr{let x ← $ᵗ α}[p x] := by
  rw [prEvent_uniformSample_prod]
  have h := prEvent_bind_bind_and ($ᵗ α) ($ᵗ β) p (fun _ ↦ True)
  simp only [and_true] at h
  rw [h, (prEvent_uniformSample_eq_one_iff (fun _ ↦ True)).mpr (fun _ ↦ trivial), mul_one]

/-- A uniform vector of length `N + 1` is a uniform head followed by an independent uniform
vector of length `N`. -/
theorem evalDistEq_uniformSample_vector_succ (N : ℕ) :
    ($ᵗ (List.Vector α (N + 1)) : ProbComp _) =ᵈ
      (do let a ← $ᵗ α; let rest ← $ᵗ (List.Vector α N); pure (a ::ᵥ rest)) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace (List.Vector α (N + 1)) := ⊤
  have hbij : Function.Bijective
      (Function.uncurry fun (a : α) (rest : List.Vector α N) => a ::ᵥ rest) :=
    ⟨fun ⟨a, v⟩ ⟨b, w⟩ h => by
      have h₁ := congrArg List.Vector.head h
      have h₂ := congrArg List.Vector.tail h
      simp only [Function.uncurry_apply_pair, List.Vector.head_cons,
        List.Vector.tail_cons] at h₁ h₂
      rw [h₁, h₂],
      fun v => ⟨(v.head, v.tail), List.Vector.cons_head_tail v⟩⟩
  refine Measure.ext fun A _ => ?_
  change 𝒟[_] {x | x ∈ A} = 𝒟[_] {x | x ∈ A}
  rw [← prEvent_eq_evalDist_of_discrete,
    ← prEvent_eq_evalDist_of_discrete,
    ← prEvent_uniformSample_pair_of_bijective hbij (· ∈ A)]
  simp only [expect_norm]

/-- A continuation of the first coordinate of a uniform pair has the output measure of the same
continuation of a uniform first coordinate. -/
theorem evalDist_uniformSample_prod_bind_fst {δ : Type} [MeasurableSpace δ]
    (f : α → ProbComp δ) :
    𝒟[(do let p ← $ᵗ (α × β); f p.1)] = 𝒟[(do let a ← $ᵗ α; f a)] := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  exact evalDist_bind_congr _ _ _ fun a => OracleComp.evalDist_bind_const _ _

/-- A uniform draw of a successor-indexed tuple is a uniform tuple followed by a uniform last
entry. -/
theorem prEvent_uniformSample_finSnoc {n : ℕ} (p : (_root_.Fin (n + 1) → α) → Prop) :
    Pr{let v ← $ᵗ (_root_.Fin (n + 1) → α)}[p v] =
      Pr{let w ← $ᵗ (_root_.Fin n → α); let x ← $ᵗ α}[p (Fin.snoc w x)] := by
  refine (prEvent_uniformSample_pair_of_bijective (g := fun w x ↦ Fin.snoc w x) ?_ p).symm
  refine ⟨fun a b hab ↦ ?_, fun v ↦ ⟨(Fin.init v, v (Fin.last n)), Fin.snoc_init_self v⟩⟩
  obtain ⟨w₁, x₁⟩ := a
  obtain ⟨w₂, x₂⟩ := b
  simp only [Function.uncurry_apply_pair] at hab
  have hw : w₁ = w₂ := by simpa using congrArg Fin.init hab
  have hx : x₁ = x₂ := by simpa using congrArg (fun v ↦ v (Fin.last n)) hab
  rw [hw, hx]

/-- If a successor tuple event is conditionally bounded after every prefix outside a bad-prefix
event, its probability is at most the bad-prefix probability plus the conditional bound. -/
theorem prEvent_uniformSample_finSnoc_le_add {n : ℕ}
    (event : (_root_.Fin (n + 1) → α) → Prop)
    (bad : (_root_.Fin n → α) → Prop) {ε : ℝ≥0∞}
    (h : ∀ y, ¬ bad y → Pr{let x ← $ᵗ α}[event (Fin.snoc y x)] ≤ ε) :
    Pr{let z ← $ᵗ (_root_.Fin (n + 1) → α)}[event z] ≤
      Pr{let y ← $ᵗ (_root_.Fin n → α)}[bad y] + ε := by
  rw [prEvent_uniformSample_finSnoc]
  simpa only [expect_norm] using
    prEvent_bind_le_prEvent_add ($ᵗ (_root_.Fin n → α))
      (fun y => do let x ← $ᵗ α; return Fin.snoc y x) bad event
      (fun y hy => by simpa only [expect_norm] using h y hy)

end transport

/-! ## Independence of the chosen sampler -/

section samplerIrrelevance

variable {α : Type}

/-- Every uniform sampler of a type denotes the same measure. -/
theorem evalDist_uniformSample_inst_irrel (i₁ i₂ : SampleableType α)
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    𝒟[@uniformSample α i₁] = 𝒟[@uniformSample α i₂] := by
  rw [@evalDist_uniformSample α i₁, @evalDist_uniformSample α i₂]

/-- Every uniform sampler of a type assigns the same probability to every event. -/
theorem prEvent_uniformSample_inst_irrel (i₁ i₂ : SampleableType α) (p : α → Prop) :
    Pr{let x ← @uniformSample α i₁}[p x] = Pr{let x ← @uniformSample α i₂}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete,
    evalDist_uniformSample_inst_irrel]

end samplerIrrelevance

end SampleableType

namespace ProbComp

open OracleComp OracleSpec ENNReal

/-- Complementing a fair hidden bit does not change the measure of any subsequent computation. -/
theorem evalDist_bind_not_uniformBool {α : Type} [MeasurableSpace α]
    (f : Bool → ProbComp α) :
    𝒟[do let b ← ($ᵗ Bool); f (!b)] = 𝒟[do let b ← ($ᵗ Bool); f b] :=
  evalDist_bind_bijective_of_uniform ($ᵗ Bool : ProbComp Bool)
    SampleableType.evalDist_uniformSample Bool.not Bool.not_bijective f

/-- A fair hidden bit is guessed with probability one half when the guess distribution does not
depend on that bit. -/
theorem evalDist_decide_eq_uniformBool_half
    (f : Bool → ProbComp Bool) (heq : 𝒟[f true] = 𝒟[f false]) :
    𝒟[do let b ← ($ᵗ Bool); let b' ← f b; return decide (b = b')] {true} = 1 / 2 := by
  have hinner (b : Bool) :
      𝒟[do let b' ← f b; return decide (b = b')] {true} = 𝒟[f b] {b} := by
    rw [← prEvent_eq_evalDist_decide (mx := f b) (p := fun b' => b = b'),
      prEvent_eq_evalDist_of_discrete]
    congr 1
    ext x
    simp [eq_comm]
  change 𝒟[($ᵗ Bool : ProbComp Bool) >>= fun b => do
    let b' ← f b
    return decide (b = b')] {true} = _
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) (Measurable.of_discrete).aemeasurable]
  simp_rw [hinner]
  rw [lintegral_fintype, Fintype.sum_bool, heq]
  have hbool : 𝒟[($ᵗ Bool : ProbComp Bool)] = uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  rw [hbool]
  simp only [uniformOn_univ_apply_singleton, Fintype.card_bool]
  have hmass : 𝒟[f false] {true} + 𝒟[f false] {false} = 1 := by
    have hprob : 𝒟[f false] Set.univ = 1 :=
      OracleComp.evalDist_apply_univ_eq_one (f false)
    have hset : (Set.univ : Set Bool) = {true} ∪ {false} := by
      ext b
      cases b <;> simp
    rw [hset, measure_union (by simp) (measurableSet_singleton false)] at hprob
    exact hprob
  rw [← add_mul, hmass]
  norm_num

end ProbComp

namespace uniformSampleImpl

open OracleSpec OracleComp

variable {ι : Type*} {spec : OracleSpec ι} [∀ t, SampleableType (spec.Range t)]
  [OracleSpec.IsUniformMeasureSpec spec]

/-- Answering every query with the canonical uniform sampler preserves the output measure of every
computation under uniform oracle semantics. -/
theorem evalDist_simulateQ {α : Type} [MeasurableSpace α] (oa : OracleComp spec α) :
    𝒟[simulateQ uniformSampleImpl oa] = 𝒟[oa] :=
  evalDist_simulateQ_eq_of_forall _ (fun t ↦ by
    let : MeasurableSpace (spec.Range t) := ⊤
    rw [uniformSampleImpl_apply, SampleableType.evalDist_uniformSample,
      OracleSpec.IsMeasureSpec.toMeasure_eq_uniformOn]) oa

/-- Answering every query with the canonical uniform sampler gives a probabilistic computation
equal in distribution to the oracle computation. -/
theorem evalDistEq_simulateQ {α : Type} (oa : OracleComp spec α) :
    simulateQ uniformSampleImpl oa =ᵈ oa :=
  letI : MeasurableSpace α := ⊤
  EvalDistEq.of_evalDist_eq (evalDist_simulateQ oa)

end uniformSampleImpl
