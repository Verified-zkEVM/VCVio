/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.ReachableWhen
public import VCVio.OracleComp.Support
public import VCVio.EvalDist.Defs.NeverFails
public import VCVio.EvalDist.Instances.OptionT
public import VCVio.EvalDist.PFunctor
public import PolyFun.PFunctor.Free.WP
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import ToMathlib.Data.Set.Functor

/-!
# Output Distribution of Computations

This file defines the `MonadLiftT`-based probability and support semantics for `OracleComp`.
-/

@[expose] public section

open OracleSpec Option ENNReal

universe u v w

open scoped OracleSpec.PrimitiveQuery

namespace OracleSpec

variable {ι} {spec : OracleSpec ι}

/-- A per-query distribution on an `OracleSpec`, definitionally the generic
probability specification on its underlying polynomial functor. -/
abbrev IsProbabilitySpec (spec : OracleSpec ι) :=
  PFunctor.IsProbabilitySpec spec.toPFunctor

namespace IsProbabilitySpec

/-- The distribution of responses to query `t`. -/
abbrev toPMF [IsProbabilitySpec spec] (t : spec.Domain) : PMF (spec.Range t) :=
  PFunctor.IsProbabilitySpec.toPMF (P := spec.toPFunctor) t

end IsProbabilitySpec

/-- An `OracleSpec` whose responses are uniformly sampled from finite, inhabited
ranges. Bundles finiteness and inhabitedness of every response type with
`IsProbabilitySpec spec` and a `Prop` witness that the per-query distribution
agrees with `PMF.uniformOfFintype`. Use this as the canonical input to lemmas
that mention `Fintype.card (spec.Range _)` or `PMF.uniformOfFintype` in their
statements. -/
class IsUniformSpec (spec : OracleSpec ι) extends IsProbabilitySpec spec where
  /-- Every response set is finite. -/
  fintype : ∀ t, Fintype (spec.Range t)
  /-- Every response set is inhabited. -/
  inhabited : ∀ t, Inhabited (spec.Range t)
  /-- The per-query distribution is the uniform distribution on the response set. -/
  toPMF_eq_uniform : ∀ t, toPMF t = PMF.uniformOfFintype (spec.Range t)

attribute [reducible, instance] IsUniformSpec.fintype IsUniformSpec.inhabited

/-- Bridge from finite, inhabited response types to `IsUniformSpec spec`.
Deliberately **not** an instance — `IsUniformSpec` must be opted into per
spec so that uniform-sampling semantics never attach silently to a spec
whose author didn't intend a probabilistic interpretation. Use this
helper when declaring `IsUniformSpec` for a concrete spec. -/
@[reducible] noncomputable def IsUniformSpec.ofFintypeInhabited
    {ι : Type u} (spec : OracleSpec ι)
    [hF : ∀ t, Fintype (spec.Range t)] [hI : ∀ t, Inhabited (spec.Range t)] :
    IsUniformSpec spec where
  toPMF t := PMF.uniformOfFintype (spec.Range t)
  fintype := hF
  inhabited := hI
  toPMF_eq_uniform _ := rfl

noncomputable instance : IsUniformSpec unifSpec := IsUniformSpec.ofFintypeInhabited _
noncomputable instance : IsUniformSpec coinSpec := IsUniformSpec.ofFintypeInhabited _

/-- Propagate `IsUniformSpec` through `+`: each summand's uniformity is
preserved on its branch. `IsProbabilitySpec (spec + spec')` is derived via
the `extends` chain. -/
noncomputable instance instIsUniformSpecAdd {ι ι'} (spec : OracleSpec ι)
    (spec' : OracleSpec ι') [IsUniformSpec spec] [IsUniformSpec spec'] :
    IsUniformSpec (spec + spec') := IsUniformSpec.ofFintypeInhabited _

/-- Package uniform oracle semantics as generic uniform semantics on the
underlying polynomial functor. This is an explicit conversion rather than an
instance so it cannot participate in overly broad `toPFunctor` unification. -/
@[reducible]
noncomputable def IsUniformSpec.toPFunctor [h : IsUniformSpec spec] :
    PFunctor.IsUniformSpec spec.toPFunctor where
  toPMF := h.toPMF
  fintype := h.fintype
  inhabited := h.inhabited
  toPMF_eq_uniform := h.toPMF_eq_uniform

end OracleSpec

export OracleSpec (IsProbabilitySpec IsUniformSpec)

namespace OracleComp

variable {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β γ : Type w}

/-! ## Oracle-facing semantics -/

section evalSPMF_main

lemma evalSPMF_eq_simulateQ [IsProbabilitySpec spec] (mx : OracleComp spec α) :
    𝒮[mx] = simulateQ IsProbabilitySpec.toPMF mx := rfl

/-- Abstract distribution of a single lifted query under `IsProbabilitySpec`:
the per-query distribution `toPMF` is pushed forward through the query's
continuation. Uniform-content sibling: `evalSPMF_liftM`. -/
lemma evalSPMF_liftM_toPMF [IsProbabilitySpec spec] (q : OracleQuery spec α) :
    𝒮[(liftM q : OracleComp spec α)] =
      (IsProbabilitySpec.toPMF q.input).map q.cont := by
  simp [evalSPMF_eq_simulateQ, SPMF.liftM_eq_map, PMF.map_comp, PMF.monad_map_eq_map]

/-- `liftM (query t) : OracleComp spec _` evaluates to the per-query distribution
`IsProbabilitySpec.toPMF t`, lifted to `SPMF`. -/
lemma evalSPMF_query_toPMF [IsProbabilitySpec spec] (t : spec.Domain) :
    𝒮[(query t : OracleComp spec _)] =
      (IsProbabilitySpec.toPMF t : SPMF (spec.Range t)) := by
  rw [evalSPMF_liftM_toPMF]; simp [PMF.map_id]


end evalSPMF_main


section evalSPMF

variable [IsUniformSpec spec]

@[simp low, grind =]
lemma evalSPMF_liftM (q : OracleQuery spec α) :
    𝒮[(liftM q : OracleComp spec α)] =
      (PMF.uniformOfFintype (spec.Range q.input)).map q.cont := by
  rw [evalSPMF_liftM_toPMF]
  exact congrArg (fun p : PMF (spec.Range q.input) =>
      ((PMF.map q.cont p : PMF α) : SPMF α))
    (IsUniformSpec.toPMF_eq_uniform q.input)

@[simp, grind =]
lemma evalSPMF_query (t : spec.Domain) :
    𝒮[(query t : OracleComp spec _)] = PMF.uniformOfFintype (spec.Range t) := by
  rw [evalSPMF_liftM]; simp [PMF.map_id]

@[simp low, grind =]
lemma probOutput_liftM_eq_div (q : OracleQuery spec α) (x : α) :
    Pr[= x | (liftM q : OracleComp spec α)] =
      (∑' u : spec.Range q.input, Pr[= x | (return q.cont u : OracleComp spec α)])
        / Fintype.card (spec.Range q.input) := by
  have : DecidableEq α := Classical.decEq α
  simp [probOutput_def, div_eq_mul_inv]

@[simp, grind =]
lemma probOutput_query (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | (query t : OracleComp spec _)] =
      (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  simp; rfl

@[grind =]
lemma probEvent_liftM_eq_div (q : OracleQuery spec α) (p : α → Prop) :
    Pr[ p | (liftM q : OracleComp spec α)] =
      (∑' u : spec.Range q.input, Pr[ p | (return q.cont u : OracleComp spec α)])
        / Fintype.card (spec.Range q.input) := by
  have : DecidablePred p := Classical.decPred p
  simp only [probEvent_eq_tsum_ite, probOutput_liftM_eq_div, tsum_fintype, div_eq_mul_inv]
  rw [sum_eq_tsum_indicator]
  simp only [Finset.coe_univ, Set.mem_univ, Set.indicator_of_mem]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun x => by aesop

@[grind =]
lemma probOutput_query_eq_div (t : spec.Domain) (u : spec.Range t) :
    Pr[= u | (query t : OracleComp spec _)] = 1 / Fintype.card (spec.Range t) := by
  simp

@[simp, grind =]
lemma probEvent_query (t : spec.Domain) (p : spec.Range t → Prop) [DecidablePred p] :
    Pr[ p | (query t : OracleComp spec _)] =
      Finset.card {x | p x} / Fintype.card (spec.Range t) := by
  simp [probEvent_liftM_eq_div]; rfl

/-- An event selecting at most one response to a uniform oracle query has
probability at most the inverse response-space cardinality. -/
lemma probEvent_query_le_inv_of_unique (t : spec.Domain) (p : spec.Range t → Prop)
    (hunique : ∀ x y, p x → p y → x = y) :
    Pr[ p | (query t : OracleComp spec _)] ≤
      (Fintype.card (spec.Range t) : ℝ≥0∞)⁻¹ := by
  classical
  rw [probEvent_query, div_eq_mul_inv]
  refine (mul_le_mul' ?_ le_rfl).trans_eq (one_mul _)
  exact_mod_cast Finset.card_le_one.mpr fun x hx y hy ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hunique x y hx hy

end evalSPMF

section supportEvalDist

variable [IsUniformSpec spec] (oa : OracleComp spec α) (x : α)

/-- `OracleComp spec` admits the bridge between its direct `support` semantics and the
`SPMF.support` of its `evalSPMF`. -/
instance instEvalDistCompatible : EvalDistCompatible (OracleComp spec) := by
  let : PFunctor.IsUniformSpec spec.toPFunctor := IsUniformSpec.toPFunctor
  exact PFunctor.FreeM.instEvalDistCompatible

/-- The reachable outputs of `oa` are exactly the outputs its distribution semantics gives
nonzero probability. This is `EvalDistCompatible.support_eq_SPMF_support` specialized to the
oracle façade, and it is the named bridge to reach for when a proof needs to move between the
two semantics without unfolding either into its `SetM` / `SPMF` interpreter. -/
lemma support_eq_evalSPMF_support :
    support oa = SPMF.support (𝒮[oa]) :=
  EvalDistCompatible.support_eq_SPMF_support oa

/-- An output has non-zero probability in `evalSPMF` iff it is in computation support. -/
lemma mem_support_evalSPMF_iff :
    some x ∈ (𝒮[oa]).run.support ↔ x ∈ support oa := by
  rw [support_eq_evalSPMF_support, SPMF.support_eq_preimage_some]
  rfl

alias ⟨mem_support_of_mem_support_evalSPMF, mem_support_evalSPMF⟩ := mem_support_evalSPMF_iff

/-- Finite-support variant of `mem_support_evalSPMF_iff`. -/
lemma mem_support_evalSPMF_iff' [DecidableEq α] :
    some x ∈ (𝒮[oa]).run.support ↔ x ∈ finSupport oa := by
  rw [mem_support_evalSPMF_iff (oa := oa) (x := x), mem_finSupport_iff_mem_support]

alias ⟨mem_finSupport_of_mem_support_evalSPMF, mem_support_evalSPMF'⟩ := mem_support_evalSPMF_iff'

end supportEvalDist

section NeverFail

variable [IsProbabilitySpec spec]

lemma probFailure_eq_zero_iff (oa : OracleComp spec α) : probFailure oa = 0 ↔ NeverFail oa := by
  simp [neverFail_iff]

lemma probFailure_pos_iff (oa : OracleComp spec α) : 0 < probFailure oa ↔ ¬ NeverFail oa := by
  simp [neverFail_iff]

lemma noFailure_of_probFailure_eq_zero {oa : OracleComp spec α} (h : probFailure oa = 0) :
    NeverFail oa := by rwa [← probFailure_eq_zero_iff]

lemma not_noFailure_of_probFailure_pos {oa : OracleComp spec α} (h : 0 < probFailure oa) :
    ¬ NeverFail oa := by rwa [← probFailure_pos_iff]

end NeverFail

section evalSPMFConvenience

variable [IsUniformSpec spec] [IsProbabilitySpec spec']

lemma evalSPMF_query_bind
    (t : spec.Domain) (ou : spec.Range t → OracleComp spec α) :
    𝒮[(query t : OracleComp spec _) >>= ou] =
      (PMF.uniformOfFintype (spec.Range t) : SPMF _) >>=
        fun u => evalSPMF (ou u) := by
  rw [evalSPMF_bind, evalSPMF_query]

lemma probOutput_congr {x y : α} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : x = y) (h2 : 𝒮[oa] = 𝒮[oa']) : Pr[= x | oa] = Pr[= y | oa'] := by
  simp_rw [probOutput_def, h1, h2]

/-- Two events have equal probabilities when their predicates agree on the support of the
first computation and the two computations share an evaluation distribution. -/
lemma probEvent_congr' {p q : α → Prop} {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h1 : ∀ x, x ∈ support oa → (p x ↔ q x))
    (h2 : 𝒮[oa] = 𝒮[oa']) : Pr[ p | oa] = Pr[ q | oa'] := by
  have hpr : (Pr[= · | oa]) = (Pr[= · | oa']) := funext fun x => probOutput_congr rfl h2
  rw [probEvent_eq_tsum_indicator, probEvent_eq_tsum_indicator, hpr]
  refine tsum_congr fun x => ?_
  by_cases hx : x ∈ support oa
  · have hs : x ∈ ({x | p x} : Set α) ↔ x ∈ ({x | q x} : Set α) := h1 x hx
    by_cases hp : x ∈ ({x | p x} : Set α)
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (hs.mp hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (hs.not.mp hp)]
  · have hz : Pr[= x | oa'] = 0 := congrFun hpr.symm x ▸ probOutput_eq_zero_of_not_mem_support hx
    rw [Set.indicator_apply_eq_zero.2 fun _ => hz, Set.indicator_apply_eq_zero.2 fun _ => hz]

lemma evalSPMF_ext_probEvent {oa : OracleComp spec α} {oa' : OracleComp spec' α}
    (h : ∀ x, Pr[= x | oa] = Pr[= x | oa']) : (𝒮[oa]).run = (𝒮[oa']).run := by
  have heval : 𝒮[oa] = 𝒮[oa'] := evalSPMF_ext h
  simp [heval]

lemma probFailure_eq_sub_probEvent' (oa : OracleComp spec α) :
    Pr[⊥ | oa] = 1 - Pr[ fun _ => True | oa] :=
  _root_.probFailure_eq_sub_probEvent oa

end evalSPMFConvenience

section guard

lemma support_guard {p : Prop} [Decidable p] :
    support (guard p : OptionT (OracleComp spec) Unit) = if p then {()} else ∅ := by
  by_cases hp : p
  · simp [OracleComp.guard_eq, hp]
  · simp only [OracleComp.guard_eq, hp, ↓reduceIte, OptionT.support_def]
    ext x
    simp

variable [IsProbabilitySpec spec]

lemma probOutput_guard {p : Prop} [Decidable p] :
    Pr[= () | (guard p : OptionT (OracleComp spec) Unit)] = if p then 1 else 0 := by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probOutput_pure_self ()
  · -- `probOutput_failure ()` would suit, but `LawfulFailure (OptionT (OracleComp spec))` does
    -- not resolve through `OptionT.instLawfulFailure` due to a universe-inference quirk in the
    -- post-refactor diamond. Compute directly.
    simp [OptionT.probOutput_eq, OptionT.run_failure, probOutput_pure]

lemma probFailure_guard {p : Prop} [Decidable p] :
    Pr[⊥ | (guard p : OptionT (OracleComp spec) Unit)] = if p then 0 else 1 := by
  rw [OracleComp.guard_eq]
  split_ifs with h
  · exact probFailure_pure ()
  · -- See note above.
    simp [OptionT.probFailure_eq, OptionT.run_failure]

/-- For any `PUnit`-valued computation in an arbitrary monad with an `SPMF` denotation, the
probability of returning `()` is the complementary mass of its failure probability. -/
lemma probOutput_punit_eq_sub_probFailure {m : Type → Type*} [Monad m] [MonadLiftT m SPMF]
    {oa : m PUnit} :
    Pr[= () | oa] = 1 - Pr[⊥ | oa] := by
  have h := tsum_probOutput_add_probFailure oa
  have hunit : ∑' x : PUnit, Pr[= x | oa] = Pr[= () | oa] :=
    tsum_eq_single () (fun x hx => absurd (Subsingleton.elim x ()) hx)
  rw [hunit] at h
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probFailure_le_one) h

/-- The `OracleComp` instance of `probOutput_punit_eq_sub_probFailure`: for a `PUnit`-valued
oracle computation, the probability of returning `()` is the complementary mass of its failure
probability. -/
lemma probOutput_eq_sub_probFailure_of_unit {oa : OracleComp spec PUnit} :
    Pr[= () | oa] = 1 - Pr[⊥ | oa] :=
  probOutput_punit_eq_sub_probFailure

/-- Guarding a computation `oa` by a decidable predicate `p` and asking for the probability of a
successful `()` output recovers exactly the event probability `Pr[p | oa]`: the failure mass of the
`guard` removes precisely the outputs falsifying `p`. Public guard-section API used by failure-based
security experiments. -/
lemma probOutput_bind_guard_eq_probEvent {α : Type} (oa : OracleComp spec α)
    (p : α → Prop) [DecidablePred p] :
    Pr[= () | (do let a ← oa; guard (p a) : OptionT (OracleComp spec) Unit)] = Pr[ p | oa] := by
  simp only [probOutput_bind_eq_tsum, OptionT.probOutput_liftM, probOutput_guard,
    probEvent_eq_tsum_ite]
  exact tsum_congr fun a => by split_ifs <;> simp

lemma probOutput_guard_eq_sub_probOutput_guard_not {α : Type} {oa : OracleComp spec α}
    [NeverFail oa] {p : α → Prop} [DecidablePred p] :
    Pr[= () | (do let a ← oa; guard (p a) : OptionT (OracleComp spec) Unit)] =
      1 - Pr[= () | (do let a ← oa; guard (¬ p a) : OptionT (OracleComp spec) Unit)] := by
  simp only [probOutput_bind_guard_eq_probEvent]
  exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top one_ne_top probEvent_le_one)
    (by simpa only [probFailure_of_liftM_PMF, tsub_zero] using probEvent_compl oa p)

end guard

/-! ## Probabilities of `orElse` (`<|>`)

`oa <|> oa'` runs `oa`, falling back to `oa'` only when `oa` returns `none`. The base `OracleComp`
never fails, so the two failure events are independent: `oa <|> oa'` fails exactly when both do, and
an output comes either from `oa` or — on `oa`'s failure mass — from `oa'`. (`support_orElse` is left
as a future addition; it follows from `probOutput_orElse` via the support↔probability bridge.) -/

section orElse

variable [IsProbabilitySpec spec] {α : Type}

@[simp]
lemma probFailure_orElse (oa oa' : OptionT (OracleComp spec) α) :
    Pr[⊥ | oa <|> oa'] = Pr[⊥ | oa] * Pr[⊥ | oa'] := by
  classical
  rw [OracleComp.orElse_def, OptionT.probFailure_eq, OptionT.probFailure_eq, OptionT.probFailure_eq,
    OptionT.run_mk, probFailure_of_liftM_PMF, probFailure_of_liftM_PMF, probFailure_of_liftM_PMF,
    zero_add, zero_add, zero_add, probOutput_bind_eq_tsum, tsum_option _ ENNReal.summable]
  simp [probOutput_pure]

@[simp]
lemma probOutput_orElse (oa oa' : OptionT (OracleComp spec) α) (x : α) :
    Pr[= x | oa <|> oa'] = Pr[= x | oa] + Pr[⊥ | oa] * Pr[= x | oa'] := by
  classical
  rw [OracleComp.orElse_def, OptionT.probOutput_eq, OptionT.probOutput_eq, OptionT.probFailure_eq,
    OptionT.probOutput_eq, OptionT.run_mk, probFailure_of_liftM_PMF, zero_add,
    probOutput_bind_eq_tsum, tsum_option _ ENNReal.summable,
    tsum_eq_single x (fun b hb => by simp [probOutput_pure, Ne.symm hb])]
  simp [probOutput_pure, add_comm]

@[simp]
lemma probEvent_orElse (oa oa' : OptionT (OracleComp spec) α) (p : α → Prop) :
    Pr[ p | oa <|> oa'] = Pr[ p | oa] + Pr[⊥ | oa] * Pr[ p | oa'] := by
  classical
  simp only [probEvent_eq_tsum_ite, probOutput_orElse]
  conv_rhs => rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun b => ?_; split_ifs <;> ring

end orElse

section simulateQ_evalSPMF

variable [IsProbabilitySpec spec] [IsProbabilitySpec spec']

/-- If an oracle implementation preserves the distribution of each source query, then
`simulateQ` preserves the distribution of every source computation. -/
lemma evalSPMF_simulateQ_eq_evalSPMF
    (so : QueryImpl spec' (OracleComp spec))
    (h : ∀ t : spec'.Domain, 𝒮[so t] =
      𝒮[(query t : OracleComp spec' (spec'.Range t))])
    (oa : OracleComp spec' α) :
    𝒮[simulateQ so oa] = 𝒮[oa] := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t mx ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
        OracleQuery.input_query, evalSPMF_bind, ih, h t]

end simulateQ_evalSPMF



section evalSPMFWhen

/-- The output distribution of `mx` when queries follow the specified distribution. -/
@[reducible, simp]
noncomputable def evalSPMFWhen (d : QueryImpl spec SPMF) (mx : OracleComp spec α) : SPMF α :=
  simulateQ (r := SPMF) d mx

end evalSPMFWhen

section supportPeel

/-- `obtain`-friendly bind support peeler at the bare `OracleComp` level. Unlike `rw
[mem_support_bind_iff]`, applying this lemma to a hypothesis uses *definitional* unification to
match `mx >>= f`, so it engages through the `Monad`/`MonadLift` instance-tree mismatches that block
the syntactic `rw` (the elaborated `OracleComp.instMonad`/`Bind.bind` spelling produced by
unfolding nested protocol definitions differs syntactically from the canonical `>>=`). -/
lemma mem_support_bind_peel (mx : OracleComp spec α) (f : α → OracleComp spec β) {y : β}
    (hy : y ∈ support (mx >>= f)) :
    ∃ a, a ∈ support mx ∧ y ∈ support (f a) := by
  rwa [mem_support_bind_iff] at hy

/-- `obtain`-friendly `pure` support resolver at the bare `OracleComp` level: `y ∈ support (pure
a)` forces `y = a`, matched by definitional unification (so it engages on the
`PFunctor.FreeM.pure` spelling that the syntactic `support_pure` `rw` rejects). -/
lemma eq_of_mem_support_pure (a : α) {y : α}
    (hy : y ∈ support (pure a : OracleComp spec α)) : y = a := by
  rwa [support_pure, Set.mem_singleton_iff] at hy

/-- `obtain`-friendly `<$>` (map) support peeler at the bare `OracleComp` level: `y ∈ support (g
<$> mx)` yields a preimage `a ∈ support mx` with `y = g a`, matched by definitional unification
(so it engages on the elaborated `Functor.map`/`OracleComp.instMonad` spelling that the syntactic
`support_map` `rw` rejects). -/
lemma mem_support_map_peel (g : α → β) (mx : OracleComp spec α) {y : β}
    (hy : y ∈ support (g <$> mx)) :
    ∃ a, a ∈ support mx ∧ y = g a := by
  rw [support_map, Set.mem_image] at hy
  obtain ⟨a, ha, hy⟩ := hy
  exact ⟨a, ha, hy.symm⟩

end supportPeel

section freeMProbability

variable [IsProbabilitySpec spec]

/-- Probability of an event after mapping a raw polynomial free program,
viewed through the `OracleComp` semantic bridge. -/
lemma probEvent_ofFreeM_map (mx : spec.toPFunctor.FreeM α) (f : α → β)
    (event : β → Prop) :
    Pr[event | OracleComp.ofFreeM (PFunctor.FreeM.map f mx)] =
      Pr[event ∘ f | OracleComp.ofFreeM mx] :=
  probEvent_map (OracleComp.ofFreeM mx) f event

/-- Probability of an event for a raw polynomial `pure`, viewed through
`OracleComp`. -/
lemma probEvent_ofFreeM_pure (x : α) (event : α → Prop) [DecidablePred event] :
    Pr[event | OracleComp.ofFreeM
      (pure x : spec.toPFunctor.FreeM α)] = if event x then 1 else 0 := by
  change Pr[event | (pure x : OracleComp spec α)] = _
  exact probEvent_pure x event

/-- Bind decomposition for a raw polynomial free program, viewed through
`OracleComp`. -/
lemma probEvent_ofFreeM_bind_eq_tsum (mx : spec.toPFunctor.FreeM α)
    (next : α → spec.toPFunctor.FreeM β) (event : β → Prop) :
    Pr[event | OracleComp.ofFreeM (PFunctor.FreeM.bind mx next)] =
      ∑' x, Pr[= x | OracleComp.ofFreeM mx] *
        Pr[event | OracleComp.ofFreeM (next x)] :=
  probEvent_bind_eq_tsum (OracleComp.ofFreeM mx)
    (fun x => OracleComp.ofFreeM (next x)) event

end freeMProbability

end OracleComp

namespace OptionT

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- Support-level peeler for an `OptionT`-monadic bind, stated at the underlying
`OracleComp`-level `.run`: every element `y` of the support of the *run* of `mx >>= f` factors
through an intermediate `some a` in `mx`'s run support and a `y` in the run support of `f a`,
unless `mx`'s run can produce `none` (in which case `y` may be that `none`). Companion to
`OptionT.mem_support_bind_mk` for the case where the `OptionT.run` has already been stripped to
the bare underlying computation.

Applies to a hypothesis `y ∈ support oa` whenever `oa` is *definitionally* `(mx >>= f).run`
(the `OptionT.run` is identity), so callers need not respell the full bind term. -/
lemma mem_support_run_bind
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((mx >>= f : OptionT (OracleComp spec) β).run)) :
    (none ∈ support mx.run ∧ y = none) ∨
      ∃ a, some a ∈ support mx.run ∧ y ∈ support ((f a).run) := by
  rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at hy
  obtain ⟨o, ho, hy⟩ := hy
  cases o with
  | none => exact Or.inl ⟨ho, by simpa using hy⟩
  | some a => exact Or.inr ⟨a, ho, hy⟩

/-- `OptionT.lift`-headed specialization of `mem_support_run_bind`: a `lift`ed (hence
never-failing) first computation `oa` peels cleanly, with the intermediate value living in
`support oa` directly (no `none` branch). -/
lemma mem_support_run_lift_bind
    (oa : OracleComp spec α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((OptionT.lift oa >>= f : OptionT (OracleComp spec) β).run)) :
    ∃ a, a ∈ support oa ∧ y ∈ support ((f a).run) := by
  rwa [OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_pure_comp, bind_map_left,
    mem_support_bind_iff] at hy

end OptionT
