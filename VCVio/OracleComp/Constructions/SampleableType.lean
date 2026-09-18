/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.EvalDist
public import VCVio.EvalDist.Bool
public import VCVio.EvalDist.Prod
public import VCVio.EvalDist.Fintype
public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.Monad.UniformTable
public import ToMathlib.Probability.UniformOn
public import ToMathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector

/-!
# Uniform Selection Over a Type

This file defines a typeclass `SampleableType β` for types `β` with a canonical uniform selection
operation, using the `ProbComp` monad.

Unlike `HasUniformSelect`, the class certifies full support and the uniform output measure.
-/

@[expose] public section

universe u v w

open ENNReal MeasureTheory ProbabilityTheory

/-- All points have the same mass under a canonical uniform sampler. -/
theorem SampleableType.probOutput_selectElem_eq {β : Type} [SampleableType β]
    (x y : β) :
    Pr[= x | (SampleableType.selectElem : ProbComp β)] =
      Pr[= y | (SampleableType.selectElem : ProbComp β)] := by
  classical
  let : _root_.Fintype β := _root_.Fintype.ofFinite β
  let : MeasurableSpace β := ⊤
  rw [← evalDist_apply_singleton, ← evalDist_apply_singleton]
  rw [SampleableType.evalDist_selectElem_eq_uniform,
    uniformOn_univ_apply_singleton, uniformOn_univ_apply_singleton]

variable (α : Type) [hα : SampleableType α]

/-- Every element of a uniform sample over a `Fintype` has output probability `card⁻¹`. -/
@[simp, grind =]
lemma probOutput_uniformSample [Fintype α] (x : α) :
    Pr[= x | $ᵗ α] = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  let : Nonempty α := ⟨OracleComp.defaultResult ($ᵗ α)⟩
  let : MeasurableSpace α := ⊤
  rw [← evalDist_apply_singleton, SampleableType.evalDist_uniformSample,
    uniformOn_univ_apply_singleton]

@[grind .]
lemma probOutput_uniformSample_inj (x y : α) : Pr[= x | $ᵗ α] = Pr[= y | $ᵗ α] :=
  SampleableType.probOutput_selectElem_eq _ _

/-- Pushing a uniform sample through a bijection of `α` preserves each output probability. -/
lemma probOutput_map_bijective_uniformSample
    {f : α → α} (hf : Function.Bijective f) (x : α) :
    Pr[= x | f <$> ($ᵗ α)] = Pr[= x | $ᵗ α] := by
  obtain ⟨x', rfl⟩ := hf.surjective x
  rw [probOutput_map_injective ($ᵗ α) hf.injective x']
  exact SampleableType.probOutput_selectElem_eq _ _

/-- Pushing forward uniform sampling along a bijection preserves output probabilities. -/
lemma probOutput_map_bijective_uniform_cross
    {β : Type} [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (y : β) :
    Pr[= y | f <$> ($ᵗ α)] = Pr[= y | ($ᵗ β)] := by
  classical
  let := Fintype.ofFinite α
  let := Fintype.ofBijective f hf
  obtain ⟨x, rfl⟩ := hf.surjective y
  simp [probOutput_map_injective ($ᵗ α) hf.injective x, Fintype.card_of_bijective hf]

/-- Binding after pushing forward uniform sampling along a bijection preserves output
probabilities. -/
lemma probOutput_bind_bijective_uniform_cross
    {β γ : Type} [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (g : β → ProbComp γ) (z : γ) :
    Pr[= z | ($ᵗ α) >>= fun x => g (f x)] =
      Pr[= z | ($ᵗ β) >>= fun y => g y] := by
  simp_rw [show (($ᵗ α) >>= fun x => g (f x)) = ((f <$> ($ᵗ α)) >>= g) from by simp [monad_norm],
    probOutput_bind_eq_tsum, probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf]

/-- Left-translation by a constant in `AddGroup α` preserves the uniform output distribution,
since `(m + ·)` is a bijection on `α` with inverse `(-m + ·)`. -/
lemma probOutput_add_left_uniform [AddGroup α] (m x : α) :
    Pr[= x | (m + ·) <$> ($ᵗ α)] = Pr[= x | $ᵗ α] :=
  probOutput_map_bijective_uniformSample α (hf := AddGroup.addLeft_bijective m) x

/-- Left-translating the bound variable of a uniform sample by a constant in `AddGroup α`
preserves the output distribution of the subsequent computation. -/
lemma probOutput_bind_add_left_uniform [AddGroup α] {β : Type}
    (m : α) (f : α → ProbComp β) (z : β) :
    Pr[= z | (do let y ← $ᵗ α; f (m + y))] =
      Pr[= z | (do let y ← $ᵗ α; f y)] := by
  simp_rw [show (do let y ← $ᵗ α; f (m + y)) =
      (((fun y : α => m + y) <$> ($ᵗ α)) >>= fun y => f y) from by simp [monad_norm],
    probOutput_bind_eq_tsum, probOutput_add_left_uniform (α := α) m]

/-- Right-translation analogue of `probOutput_add_left_uniform`: right-adding a constant to a
uniform sample in `AddGroup α` preserves the output distribution, since `(· + m)` is a bijection
on `α` with inverse `(· + (-m))`. -/
lemma probOutput_add_right_uniform [AddGroup α] (m x : α) :
    Pr[= x | ((· + m) : α → α) <$> ($ᵗ α)] = Pr[= x | $ᵗ α] :=
  probOutput_map_bijective_uniformSample α (hf := AddGroup.addRight_bijective m) x

/-- Right-translating the bound variable of a uniform sample by a constant in `AddGroup α`
preserves the output distribution of the subsequent computation. -/
lemma probOutput_bind_add_right_uniform [AddGroup α] {β : Type}
    (m : α) (f : α → ProbComp β) (z : β) :
    Pr[= z | (do let y ← $ᵗ α; f (y + m))] =
      Pr[= z | (do let y ← $ᵗ α; f y)] := by
  simp_rw [show (do let y ← $ᵗ α; f (y + m)) =
      (((fun y : α => y + m) <$> ($ᵗ α)) >>= fun y => f y) from by simp [monad_norm],
    probOutput_bind_eq_tsum, probOutput_add_right_uniform (α := α) m]

/-- Translating a uniform additive sample preserves the full evaluation distribution. -/
lemma evalSPMF_add_left_uniform [AddGroup α] (m : α) :
    𝒮[((m + ·) : α → α) <$> ($ᵗ α)] = 𝒮[$ᵗ α] :=
  evalSPMF_ext (probOutput_add_left_uniform (α := α) m)

/-- Two additive translations of a uniform sample have the same evaluation distribution. -/
lemma evalSPMF_add_left_uniform_eq [AddGroup α] (m₁ m₂ : α) :
    𝒮[((m₁ + ·) : α → α) <$> ($ᵗ α)] =
      𝒮[((m₂ + ·) : α → α) <$> ($ᵗ α)] :=
  (evalSPMF_add_left_uniform (α := α) m₁).trans (evalSPMF_add_left_uniform (α := α) m₂).symm

/-- Right-translation analogue of `evalSPMF_add_left_uniform`: right-adding a constant to a
uniform sample in `AddGroup α` preserves the full evaluation distribution. -/
lemma evalSPMF_add_right_uniform [AddGroup α] (m : α) :
    𝒮[((· + m) : α → α) <$> ($ᵗ α)] = 𝒮[$ᵗ α] :=
  evalSPMF_ext (probOutput_add_right_uniform (α := α) m)

/-- Two right-translations of a uniform sample have the same evaluation distribution. -/
lemma evalSPMF_add_right_uniform_eq [AddGroup α] (m₁ m₂ : α) :
    𝒮[((· + m₁) : α → α) <$> ($ᵗ α)] =
      𝒮[((· + m₂) : α → α) <$> ($ᵗ α)] :=
  (evalSPMF_add_right_uniform (α := α) m₁).trans (evalSPMF_add_right_uniform (α := α) m₂).symm

/-- Pushing forward uniform sampling via a bijection preserves the full evaluation distribution. -/
lemma evalSPMF_map_bijective_uniform_cross
    {β : Type} [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) :
    𝒮[f <$> ($ᵗ α)] = 𝒮[$ᵗ β] :=
  evalSPMF_ext (probOutput_map_bijective_uniform_cross (α := α) (β := β) f hf)

/-- **Bijective uniform + right-translation gives uniform.** Sampling `x ← $ᵗ α`, transporting
through a bijection `f : α → β`, and right-adding any fixed `m : β` yields the same distribution
as sampling `y ← $ᵗ β` directly, as observed by any continuation `cont : β → ProbComp γ`.

This is the "one-time pad" fact underlying many cryptographic reductions: bijective transport
makes `f x` uniform on `β`, and in any `AddGroup β` right-translation `(· + m)` is a bijection
on the uniform measure, so the sum is again uniform. -/
lemma evalSPMF_bind_bijective_add_right_uniform {β γ : Type}
    [AddGroup β] [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (m : β) (cont : β → ProbComp γ) :
    𝒮[do let x ← ($ᵗ α); cont (f x + m)] =
      𝒮[do let y ← ($ᵗ β); cont y] := by
  rw [show (do let x ← ($ᵗ α); cont (f x + m)) = (f <$> ($ᵗ α)) >>= fun y => cont (y + m)
        from by simp [monad_norm], evalSPMF_bind,
      evalSPMF_map_bijective_uniform_cross (α := α) (β := β) f hf, ← evalSPMF_bind,
      show (do let y ← ($ᵗ β); cont (y + m)) = (((· + m) : β → β) <$> ($ᵗ β)) >>= cont
        from by simp [monad_norm], evalSPMF_bind, evalSPMF_add_right_uniform (α := β) m,
      ← evalSPMF_bind]

/-- Constant-irrelevance form of `evalSPMF_bind_bijective_add_right_uniform`: sampling through a
bijection and right-adding a constant has a distribution independent of the constant. Any two
offsets produce the same evaluation distribution. -/
lemma evalSPMF_bind_bijective_add_right_eq {β γ : Type}
    [AddGroup β] [SampleableType β] [Finite α]
    (f : α → β) (hf : Function.Bijective f) (m₁ m₂ : β) (cont : β → ProbComp γ) :
    𝒮[do let x ← ($ᵗ α); cont (f x + m₁)] =
      𝒮[do let x ← ($ᵗ α); cont (f x + m₂)] := by
  rw [evalSPMF_bind_bijective_add_right_uniform (α := α) (β := β) f hf m₁ cont,
      ← evalSPMF_bind_bijective_add_right_uniform (α := α) (β := β) f hf m₂ cont]

lemma probFailure_uniformSample : Pr[⊥ | $ᵗ α] = 0 := by aesop

@[simp] instance : NeverFail ($ᵗ α) := inferInstance

@[simp, grind =]
lemma evalSPMF_uniformSample [Fintype α] [Nonempty α] :
    𝒮[$ᵗ α] = liftM (PMF.uniformOfFintype α) := by aesop

@[simp, grind =]
lemma finSupport_uniformSample [Fintype α] [DecidableEq α] :
    finSupport ($ᵗ α) = Finset.univ := by aesop

@[simp, grind =]
lemma probEvent_uniformSample [Fintype α] (p : α → Prop) [DecidablePred p] :
    Pr[ p | $ᵗ α] = (Finset.univ.filter p).card / Fintype.card α := by
  simp only [probEvent_eq_sum_filter_univ, probOutput_uniformSample, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]



section Marginalization

/-- **Overwriting one coordinate of a uniform function table is measure-preserving.**

Drawing a value `u` uniformly from `R`, then a full function table `g : D → R` uniformly, and
returning `Function.update g t u` yields the same distribution as drawing the table directly.

This is the `t`-marginal independence of the uniform (product) distribution on `D → R`: the value
at coordinate `t` is uniform and independent of the others, so replacing it with a fresh
independent uniform draw leaves the joint distribution unchanged. It is the marginalization step
behind eager-sampling reformulations of oracle responses. -/
lemma evalSPMF_uniformSample_bind_update
    {D R : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) :
    𝒮[do let u ← $ᵗ R; let g ← $ᵗ (D → R); pure (Function.update g t u)] =
      𝒮[$ᵗ (D → R)] := by
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace (D → R) := MeasurableSpace.pi
  apply evalSPMF_ext
  intro h
  have hmeasure := evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample t pure
  simpa only [evalDist_apply_singleton, bind_pure] using
    congrArg (fun μ : Measure (D → R) => μ {h}) hmeasure

/-- **The first coordinate of a uniform pair is uniform.**

Mapping the uniform distribution on `α × β` through `Prod.fst` yields the uniform distribution on
`α`: the `Prod.fst`-marginal of a uniform (product) distribution is uniform. -/
lemma evalSPMF_map_fst_uniformSample_prod {α β : Type} [Finite α]
    [Finite β] [Nonempty β] [SampleableType α] [SampleableType β] [SampleableType (α × β)] :
    𝒮[Prod.fst <$> ($ᵗ (α × β))] = 𝒮[$ᵗ α] := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  let : MeasurableSpace (α × β) := MeasurableSpace.prod ‹MeasurableSpace α› ‹MeasurableSpace β›
  apply evalSPMF_ext
  intro x
  have hmeasure : 𝒟[Prod.fst <$> ($ᵗ (α × β))] = 𝒟[$ᵗ α] := by
    rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample,
      SampleableType.evalDist_uniformSample, uniformOn_univ_prod,
      Measure.map_fst_prod, measure_univ, one_smul]
  simpa only [evalDist_apply_singleton] using
    congrArg (fun μ : Measure α => μ {x}) hmeasure

/-- **Restricting a uniform function table to a subdomain along an injection is uniform.**

For an injection `e : A → B` between finite types, drawing a uniform table `g : B → R` and
restricting it along `e` (i.e. `g ∘ e`) yields the uniform distribution on `A → R`.

This is the marginalization of the uniform (product) distribution on `B → R` onto the block of
coordinates indexed by `Set.range e`: those coordinates are jointly uniform and independent of
the rest, and `e` reindexes the block by `A`. It underlies eager-sampling reformulations that
project a fine-grained random-oracle table onto a coarser one. -/
lemma evalSPMF_uniformSample_map_comp_injective
    {A B R : Type} [Finite A] [Finite B] [Finite R]
    [Nonempty R] [SampleableType (A → R)] [SampleableType (B → R)]
    {e : A → B} (he : Function.Injective e) :
    𝒮[do let g ← $ᵗ (B → R); pure (g ∘ e)] = 𝒮[$ᵗ (A → R)] := by
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace (A → R) := MeasurableSpace.pi
  let : MeasurableSpace (B → R) := MeasurableSpace.pi
  apply evalSPMF_ext
  intro h
  have hmeasure : 𝒟[do let g ← $ᵗ (B → R); pure (g ∘ e)] = 𝒟[$ᵗ (A → R)] := by
    simpa only [bind_pure_comp] using
      (evalDist_map_table_comp_injective ($ᵗ (A → R)) ($ᵗ (B → R))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample he)
  simpa only [evalDist_apply_singleton] using
    congrArg (fun μ : Measure (A → R) => μ {h}) hmeasure

/-- Patch a uniform function table at every point of a list `l`, drawing one fresh uniform value
per list entry. With `l = []` the table is returned unchanged; with `l = d :: ds` the tail is
patched first and the head point `d` is then overwritten with a fresh uniform draw.

This is the iterated form of `Function.update` used by `evalSPMF_uniformSample_patchList`: the
outermost update is at the head, so the list is consumed head-first. -/
def patchTable {D R : Type} [DecidableEq D] [SampleableType R] :
    List D → (D → R) → ProbComp (D → R)
  | [], g => pure g
  | d :: ds, g => do
      let g' ← patchTable ds g
      let u ← $ᵗ R
      pure (Function.update g' d u)

@[simp] lemma patchTable_nil {D R : Type} [DecidableEq D] [SampleableType R] (g : D → R) :
    patchTable [] g = pure g := rfl

lemma patchTable_cons {D R : Type} [DecidableEq D] [SampleableType R]
    (d : D) (ds : List D) (g : D → R) :
    patchTable (d :: ds) g =
      (do let g' ← patchTable ds g; let u ← $ᵗ R; pure (Function.update g' d u)) := rfl

/-- Patching a uniform table at a finite list of coordinates with independent uniform
draws preserves its output measure. Repeated coordinates are allowed. -/
theorem evalDist_uniformSample_patchList
    {D R : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [MeasurableSpace R] [MeasurableSingletonClass R]
    [SampleableType R] [SampleableType (D → R)] (l : List D) :
    𝒟[do let g ← $ᵗ (D → R); patchTable l g] = 𝒟[$ᵗ (D → R)] := by
  induction l with
  | nil => simp [patchTable]
  | cons d ds ih =>
      let table : ProbComp (D → R) := do let g ← $ᵗ (D → R); patchTable ds g
      have hstep :
          𝒟[do let g ← $ᵗ (D → R); patchTable (d :: ds) g] =
            𝒟[do let g ← table; let u ← $ᵗ R; pure (Function.update g d u)] := by
        simp [table, patchTable_cons, bind_assoc]
      rw [hstep, evalDist_bind_of_discrete table, ih]
      rw [← evalDist_bind_of_discrete]
      have hswap := evalDist_bind_bind_swap ($ᵗ (D → R)) ($ᵗ R)
        (fun g u => pure (Function.update g d u)) Measurable.of_discrete
      rw [hswap]
      simpa using evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R))
        SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample d pure

/-- **Patching a uniform function table at finitely many points preserves uniformity.**

Drawing a uniform table `g : D → R` and then `patchTable l g` — overwriting `g` at every point of
`l` with independent fresh uniform draws — yields the same distribution as drawing the table
directly. The points of `l` need not be distinct: each `Function.update` is the outermost
operation of its recursion step, so `evalSPMF_uniformSample_bind_update` applies regardless of
overlap. This is the marginalization step behind trace-conditioned eager-table reformulations,
where the patched points are determined only after the table is sampled. -/
lemma evalSPMF_uniformSample_patchList
    {D R : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (l : List D) :
    𝒮[do let g ← $ᵗ (D → R); patchTable l g] = 𝒮[$ᵗ (D → R)] := by
  let : MeasurableSpace R := ⊤
  apply evalSPMF_ext
  intro h
  simpa only [evalDist_apply_singleton] using
    congrArg (fun μ : Measure (D → R) => μ {h}) (evalDist_uniformSample_patchList l)

end Marginalization

-- TODO: generalize this lemma
/--
Given an independent probabilistic computation `ob : ProbComp Bool`, the probability that its
output `b'` differs from a uniformly chosen boolean `b` is the same as the probability that they
are equal. In other words, `P(b ≠ b') = P(b = b')` where `b` is uniform.
-/
lemma probOutput_uniformBool_not_decide_eq_decide {ob : ProbComp Bool} :
    Pr[= true | do let b ←$ᵗ Bool; let b' ← ob; return !decide (b = b')] =
      Pr[= true | do let b ←$ᵗ Bool; let b' ← ob; return decide (b = b')] := by
  simp [probOutput_bind_eq_tsum, add_comm]

/-- Conditioning on a uniform boolean averages the two branch probabilities. -/
lemma probOutput_bind_uniformBool {α : Type}
    (f : Bool → ProbComp α) (x : α) :
    Pr[= x | (do let b ← $ᵗ Bool; f b)] =
      (Pr[= x | f true] + Pr[= x | f false]) / 2 := by
  rw [probOutput_bind_eq_tsum, tsum_fintype (L := .unconditional _), Fintype.sum_bool]
  simp only [probOutput_uniformSample, Fintype.card_bool, Nat.cast_ofNat, add_comm, div_eq_mul_inv]
  rw [← left_distrib, mul_comm]

/-- Guessing a uniformly random bit after branching between `real` and `rand` decomposes into
the difference of the branch success probabilities. -/
lemma probOutput_uniformBool_branch_toReal_sub_half (real rand : ProbComp Bool) :
    (Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)]).toReal - 1 / 2 =
    ((Pr[= true | real]).toReal - (Pr[= true | rand]).toReal) / 2 := by
  have hformula : Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← if b then real else rand
      pure (b == z)] = (Pr[= true | real] + Pr[= false | rand]) / 2 := by
    rw [probOutput_bind_uniformBool]
    simp
  have hfalseAsSub : Pr[= false | rand] = 1 - Pr[= true | rand] := by
    rw [← (by simp : Pr[= true | rand] + Pr[= false | rand] = 1),
      ENNReal.add_sub_cancel_left probOutput_ne_top]
  rw [hformula, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top probOutput_ne_top,
    hfalseAsSub, ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

/-- If the distribution of `f b` is independent of `b`, then guessing a uniformly random
bit by running `f` has success probability exactly 1/2.
This is the core lemma behind "all-random hybrid has probability 1/2" arguments. -/
lemma probOutput_decide_eq_uniformBool_half
    (f : Bool → ProbComp Bool)
    (heq : 𝒮[f true] = 𝒮[f false]) :
    Pr[= true | do let b ← $ᵗ Bool; let b' ← f b; return decide (b = b')] = 1 / 2 := by
  rw [probOutput_bind_eq_tsum]
  simp only [tsum_fintype (L := .unconditional _), Fintype.sum_bool,
    probOutput_uniformSample, Fintype.card_bool]
  rw [show Pr[= true | f true >>= fun b' => pure (decide (true = b'))] = Pr[= true | f true] by
        simp,
    show Pr[= true | f false >>= fun b' => pure (decide (false = b'))] = Pr[= false | f false] by
        simp,
    evalSPMF_ext_iff.mp heq true, ← mul_add,
    show Pr[= true | f false] + Pr[= false | f false] = 1 by simp, mul_one]
  simp [one_div]

section UniformSampleImpl

open OracleSpec OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

/-- Uniformly sampling a response has the same distribution as issuing the
corresponding query to a uniform oracle specification. -/
lemma evalSPMF_uniformSample_eq_query [∀ i, SampleableType (spec.Range i)]
    [IsUniformSpec spec] (t : spec.Domain) :
    𝒮[$ᵗ spec.Range t] =
      𝒮[(spec.query t : OracleComp spec (spec.Range t))] := by
  rw [evalSPMF_uniformSample, OracleComp.evalSPMF_query]

/-- Uniformly sampling a response and issuing the corresponding uniform-oracle query
assign the same probability to every output. -/
lemma probOutput_uniformSample_eq_query [∀ i, SampleableType (spec.Range i)]
    [IsUniformSpec spec] (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | $ᵗ spec.Range t] =
      Pr[= u | (spec.query t : OracleComp spec (spec.Range t))] := by
  rw [probOutput_def, probOutput_def, evalSPMF_uniformSample_eq_query]

/-- Uniformly sampling a response and issuing the corresponding uniform-oracle query
assign the same probability to every event. -/
lemma probEvent_uniformSample_eq_query [∀ i, SampleableType (spec.Range i)]
    [IsUniformSpec spec] (t : spec.Domain) (p : spec.Range t → Prop) :
    Pr[p | $ᵗ spec.Range t] =
      Pr[p | (spec.query t : OracleComp spec (spec.Range t))] := by
  rw [probEvent_def, probEvent_def, evalSPMF_uniformSample_eq_query]

/-- Given that the output type of all oracles has a `SampleableType` instance, replace all queries
with uniformly random responses by calling the corresponding `uniformSample` at each query. -/
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t

/-- A uniformly sampled implementation answers each query with the uniform sampler for
that query's response type. -/
@[simp]
lemma uniformSampleImpl_apply [∀ i, SampleableType (spec.Range i)] (t : spec.Domain) :
    uniformSampleImpl (spec := spec) t = $ᵗ spec.Range t := rfl

namespace uniformSampleImpl

variable [∀ i, SampleableType (spec.Range i)]

@[simp]
lemma evalSPMF_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) :
    𝒮[simulateQ uniformSampleImpl oa] = 𝒮[oa] := by
  apply OracleComp.evalSPMF_simulateQ_eq_evalSPMF
  intro t
  simp [uniformSampleImpl]

@[simp]
lemma probOutput_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | simulateQ uniformSampleImpl oa] = Pr[= x | oa] := by
  rw [probOutput_def, probOutput_def, evalSPMF_simulateQ]

@[simp]
lemma probEvent_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[ p | simulateQ uniformSampleImpl oa] = Pr[ p | oa] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_simulateQ]

@[simp]
lemma support_simulateQ [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) :
    support (simulateQ uniformSampleImpl oa) = support oa :=
  Set.ext fun x => mem_support_iff_of_evalSPMF_eq (evalSPMF_simulateQ oa) x

@[simp]
lemma finSupport_simulateQ [IsUniformSpec spec] {α : Type}
    [DecidableEq α] (oa : OracleComp spec α) :
    finSupport (simulateQ uniformSampleImpl oa) = finSupport oa := by
  simp [finSupport_eq_iff_support_eq_coe]

end uniformSampleImpl

end UniformSampleImpl
