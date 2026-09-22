/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Support
public import VCVio.OracleComp.Constructions.UniformFinMeasure
public import VCVio.EvalDist.Monad.Seq.Uniform
public import ToMathlib.Data.FinEnum
public import Init.Data.UInt.Lemmas
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Vector
import VCVio.OracleComp.EvalDist.Measure

/-!
# Canonical uniform samplers: the `$ᵗ` notation class

`SampleableType β` gives the notation `$ᵗ β` its meaning: an executable `ProbComp β` together
with the one law that makes it a *uniform* sampler, `𝒟[$ᵗ β] = uniformOn Set.univ` for every
measurable structure with measurable singletons. The law is part of the contract because no
consumer wants a canonical sampler that is not uniform; it is the only field besides the
program, and every construction below discharges it once.

Nonemptiness of `β` follows from having a sampler at all (`SampleableType.nonempty`), and
finiteness and full operational support follow from the law (`SampleableType.finite`,
`support_uniformSample`). The two `Prop`-valued facts are instances so that a hypothesis
`[SampleableType β]` supplies them wherever Mathlib asks, but at low priority: ordinary
instances such as `Finite.of_fintype` and `instNonemptyOfInhabited` are tried first, so a fact
about `Fin 3` never routes through sampler code and the sampler instances only answer for types
whose finiteness is known through nothing else (typically `spec.Range t` under
`[∀ t, SampleableType (spec.Range t)]`). Since the classes are propositions, which instance
answers is invisible to definitional equality (`docs/agents/gotchas.md` §8b).

Products, vectors, and equivalences transport the sampler together with its law.
-/

public section

universe u v w

open ENNReal MeasureTheory ProbabilityTheory

/-- A canonical uniform sampler for `β`, written `$ᵗ β`: an executable program whose output
measure is uniform for every measurable structure with measurable singletons. -/
class SampleableType (β : Type) where
  /-- The canonical sampler of `β`, written `$ᵗ β`. -/
  selectElem : ProbComp β
  /-- The canonical sampler denotes the uniform measure on `β`. -/
  evalDist_selectElem_eq_uniform :
    ∀ [MeasurableSpace β] [MeasurableSingletonClass β],
      𝒟[selectElem] = uniformOn Set.univ

/-- Select uniformly from the type `β` using a type-class provided definition. -/
@[expose]
def uniformSample (β : Type) [h : SampleableType β] : ProbComp β := h.selectElem

notation:90 "$ᵗ " α:91 => uniformSample α

/-- The canonical sample has uniform output measure under native oracle semantics. -/
theorem SampleableType.evalDist_uniformSample {β : Type} [SampleableType β]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    𝒟[$ᵗ β] = uniformOn Set.univ :=
  SampleableType.evalDist_selectElem_eq_uniform

/-- A sampler yields an element of its type: run it on default oracle answers. Low priority so
that ordinary nonemptiness instances answer first. -/
instance (priority := 100) SampleableType.nonempty (β : Type) [SampleableType β] :
    Nonempty β :=
  ⟨OracleComp.defaultResult ($ᵗ β)⟩

/-- A uniform sampler denotes a probability measure only on a finite type. Low priority so
that ordinary finiteness instances answer first. -/
instance (priority := 100) SampleableType.finite (β : Type) [SampleableType β] : Finite β := by
  let : MeasurableSpace β := ⊤
  have h : 𝒟[$ᵗ β] Set.univ ≠ 0 := by
    rw [measure_univ]
    exact one_ne_zero
  rw [SampleableType.evalDist_uniformSample] at h
  exact Set.finite_univ_iff.mp (finite_of_uniformOn_ne_zero h)

variable (α : Type) [SampleableType α]

/-- A uniform sampler can output every element: positive uniform mass on each singleton is
operational reachability. -/
@[simp, grind =]
lemma support_uniformSample : support ($ᵗ α) = Set.univ := by
  let : MeasurableSpace α := ⊤
  refine Set.eq_univ_of_forall fun x => ?_
  rw [OracleComp.mem_support_iff_evalDist_singleton_pos, SampleableType.evalDist_uniformSample]
  refine pos_iff_ne_zero.mpr fun h => ?_
  rw [uniformOn_eq_zero_iff Set.finite_univ] at h
  simp at h

lemma mem_support_uniformSample {x : α} : x ∈ support ($ᵗ α) := by grind

/-- The canonical sampler has a possible output. -/
@[grind .]
lemma support_uniformSample_nonempty : (support ($ᵗ α)).Nonempty :=
  OracleComp.support_nonempty _

section instances

/-- The uniform sampler of `Fin (n + 1)`. -/
@[expose, reducible] def SampleableType.Fin (n : ℕ) : SampleableType (Fin (n + 1)) where
  selectElem := $[0..n]
  evalDist_selectElem_eq_uniform := by
    intro _ _
    cases MeasurableSpace.eq_top_of_finite (α := _root_.Fin (n + 1))
    exact ProbComp.evalDist_uniformFin n

instance (n : ℕ) [hn : NeZero n] : SampleableType (Fin n) :=
  match n, hn with
  | _ + 1, _ => SampleableType.Fin _

instance (α : Type) [Unique α] : SampleableType α where
  selectElem := return default
  evalDist_selectElem_eq_uniform := by
    intro _ _
    apply Measure.ext_of_singleton
    intro x
    rw [evalDist_pure, Unique.eq_default x, uniformOn_univ_apply_singleton]
    simp

/-- A sum of oracle specs with sampleable ranges again has sampleable ranges. -/
instance {ι ι'} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    [h : ∀ t, SampleableType (spec.Range t)] [h' : ∀ t, SampleableType (spec'.Range t)] :
    ∀ t, SampleableType ((spec + spec').Range t)
  | .inl t => h t
  | .inr t => h' t

/-- Select a uniform element from `α × β` by independently selecting from `α` and `β`. -/
instance (α β : Type) [SampleableType α] [SampleableType β] : SampleableType (α × β) where
  selectElem := (·, ·) <$> ($ᵗ α) <*> ($ᵗ β)
  evalDist_selectElem_eq_uniform := by
    intro outputSpace _
    let : MeasurableSpace α := ⊤
    let : MeasurableSpace β := ⊤
    exact evalDist_seq_map_eq_uniformOn ($ᵗ α) ($ᵗ β) Prod.mk
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
      (@Measurable.of_discrete (α × β) (α × β) Prod.instMeasurableSpace outputSpace
        inferInstance _) ⟨Function.injective_id, Function.surjective_id⟩

/-- Transport a uniform sampler along an equivalence. -/
@[expose, reducible] def SampleableType.ofEquiv {α β : Type} [SampleableType α] (e : α ≃ β) :
    SampleableType β where
  selectElem := e <$> ($ᵗ α)
  evalDist_selectElem_eq_uniform := by
    intro _ _
    let : Finite β := Finite.of_injective e.symm e.symm.injective
    let : Nonempty β := Nonempty.map e inferInstance
    let : MeasurableSpace α := ⊤
    change 𝒟[e <$> ($ᵗ α)] = uniformOn Set.univ
    rw [evalDist_map_of_discrete, SampleableType.evalDist_uniformSample]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete e.bijective

/-- Any finitely enumerable type can be sampled uniformly using the underlying equivalence. -/
instance FinEnum.SampleableType (α : Type) [h : FinEnum α] [Nonempty α] : SampleableType α :=
  haveI : NeZero (FinEnum.card α) := NeZero.mk FinEnum.card_ne_zero
  SampleableType.ofEquiv h.equiv.symm

/-- Noncomputable bridge from a nonempty `Fintype` with decidable equality to `SampleableType`,
via `Fintype.equivFin`. Used by downstream instances (e.g. `Sym α n`, `Equiv.Perm α`, `β ↪ α`)
whose Mathlib `Fintype` instances are not paired with a `FinEnum`. Provided as a `def` rather
than an `instance` to avoid overlap with `FinEnum.SampleableType`. -/
@[reducible] noncomputable def SampleableType.ofFintype (α : Type)
    [Fintype α] [Nonempty α] : SampleableType α :=
  haveI : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  letI : SampleableType (_root_.Fin (Fintype.card α)) := inferInstance
  SampleableType.ofEquiv (α := _root_.Fin (Fintype.card α)) (Fintype.equivFin α).symm

/-- Explicit noncomputable uniform sampler for a dependent finite product. This constructor is a
definition rather than an instance so it cannot compete with executable samplers for particular
dependent function types. -/
@[reducible] noncomputable def SampleableType.piOfFintype
    {ι : Type} [Fintype ι] (α : ι → Type)
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] : SampleableType (∀ i, α i) := by
  classical
  exact SampleableType.ofFintype _

/-- Uniform sampling of a nonempty subtype of a finite type, by enumeration. Provided as a
definition so that it never competes with executable enumeration-based instances. -/
@[reducible] noncomputable def SampleableType.subtype (α : Type) [Fintype α] (p : α → Prop)
    [DecidablePred p] [Nonempty {x // p x}] : SampleableType {x // p x} :=
  SampleableType.ofFintype _

/-- Uniform sampling from a nonempty finite set, by enumeration. -/
@[reducible] noncomputable def SampleableType.finsetCoe {α : Type} (U : Finset α)
    (hU : U.Nonempty) : SampleableType ↥U :=
  haveI : Nonempty ↥U := hU.to_subtype
  SampleableType.ofFintype _

instance (n : ℕ) [NeZero n] : FinEnum (ZMod n) where
  card := n
  equiv := (ZMod.finEquiv n).symm.toEquiv

instance : FinEnum USize where
  card := 2 ^ System.Platform.numBits
  equiv := ⟨USize.toFin, USize.ofFin, fun x => by simp, fun x => by simp⟩

instance : FinEnum ISize where
  card := 2 ^ System.Platform.numBits
  equiv := ⟨BitVec.toFin ∘ ISize.toBitVec, ISize.ofBitVec ∘ BitVec.ofFin,
    fun x => by simp, fun x => by simp⟩

/-- The array-backed `Vector α n` is equivalent to an `n`-indexed function. -/
@[expose]
def arrayVectorEquivFin (α : Type u) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun v i := v[i.1]
  invFun := Vector.ofFn
  left_inv v := by
    change Vector.ofFn (fun i : Fin n => v[i.1]) = v
    exact Vector.ofFn_getElem
  right_inv f := funext fun i => by
    simp

/-- `Vector α n` is finite when `α` is finite, via the equivalence with `Fin n → α`. -/
instance instFintypeVector (α : Type u) (n : ℕ) [Fintype α] : Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α) (arrayVectorEquivFin α n).symm

/-- Finite entries give a finite array-backed vector type. -/
instance instFiniteVector (α : Type u) (n : ℕ) [Finite α] : Finite (Vector α n) :=
  Finite.of_equiv (Fin n → α) (arrayVectorEquivFin α n).symm

/-- Sample a `Vector α n` by independently sampling `α` at each index. -/
def SampleableType.vector (α : Type) [SampleableType α] : (n : ℕ) → ProbComp (Vector α n)
  | 0 => pure #v[]
  | m + 1 => Vector.push <$> SampleableType.vector α m <*> ($ᵗ α)

/-- Independent uniform samples at each index give the uniform measure on `Vector α n`. -/
theorem SampleableType.evalDist_vector (α : Type) [SampleableType α] :
    ∀ (n : ℕ) [MeasurableSpace (Vector α n)] [MeasurableSingletonClass (Vector α n)],
      𝒟[SampleableType.vector α n] = uniformOn Set.univ := by
  intro n
  induction n with
  | zero =>
    intro _ _
    let : Unique (Vector α 0) := ⟨⟨#v[]⟩, fun x ↦ by ext i; omega⟩
    let : Fintype (Vector α 0) := Fintype.ofFinite _
    apply Measure.ext_of_singleton
    intro x
    simp [SampleableType.vector, Subsingleton.elim x #v[], uniformOn_univ_apply_singleton]
  | succ m ih =>
    intro _ _
    let : MeasurableSpace (Vector α m) := ⊤
    let : MeasurableSpace α := ⊤
    exact evalDist_seq_map_eq_uniformOn _ ($ᵗ α) Vector.push ih
      SampleableType.evalDist_uniformSample Measurable.of_discrete
      ⟨fun x y h ↦ Prod.ext (Vector.push_eq_push.mp h).2 (Vector.push_eq_push.mp h).1,
        fun x ↦ ⟨(x.pop, x.back), Vector.push_pop_back x⟩⟩

instance (α : Type) (n : ℕ) [SampleableType α] : SampleableType (Vector α n) where
  selectElem := SampleableType.vector α n
  evalDist_selectElem_eq_uniform := SampleableType.evalDist_vector α n

/-- A function from `Fin n` to a `SampleableType` is also `SampleableType`. This is the base
case used by the general `FinEnum`-indexed `instSampleableTypeFunc` below. -/
instance instSampleableTypeFinFunc {n : ℕ} {α : Type} [SampleableType α] :
    SampleableType (Fin n → α) :=
  SampleableType.ofEquiv (arrayVectorEquivFin α n)

/-- A function `β → α` for `β` finitely enumerable and `α` sampleable is itself sampleable.
This generalizes the `Fin n → α` instance above: the `FinEnum.fin` instance recovers it. -/
instance instSampleableTypeFunc {β α : Type} [FinEnum β] [SampleableType α] :
    SampleableType (β → α) :=
  SampleableType.ofEquiv (α := Fin (FinEnum.card β) → α)
    (Equiv.arrowCongr FinEnum.equiv.symm (Equiv.refl α))

/-- Select a uniform element from `List.Vector α n` by independently selecting `α` at each
index. The construction goes through the equivalence with `Fin n → α`. -/
instance instSampleableTypeListVector {α : Type} {n : ℕ} [SampleableType α] :
    SampleableType (List.Vector α n) :=
  SampleableType.ofEquiv (Equiv.vectorEquivFin α n).symm

/-- Select a uniform element from `Matrix ι κ α` by independently selecting an entry for each
`(i, j)`. Both index types only need to be `FinEnum`. -/
instance instSampleableTypeMatrix {α ι κ : Type} [FinEnum ι] [FinEnum κ] [SampleableType α] :
    SampleableType (Matrix ι κ α) :=
  inferInstanceAs (SampleableType (ι → κ → α))

/-- Discoverability wrapper: `SampleableType (α ⊕ β)` follows from `FinEnum` on each side
plus nonemptiness of the sum, via Mathlib's `FinEnum.sum` instance and
`FinEnum.SampleableType`. Listed explicitly so users can see it in the instance set rather
than relying on a multi-step search. -/
instance instSampleableTypeSum {α β : Type} [FinEnum α] [FinEnum β]
    [Nonempty (α ⊕ β)] : SampleableType (α ⊕ β) :=
  inferInstance

/-- Discoverability wrapper: `SampleableType (Finset α)` for `FinEnum α`. Uniform sampling
draws every subset of `α` with the same probability (`2^|α|` outcomes). `Finset α` is always
inhabited by `∅`, so no `Nonempty` hypothesis is needed. -/
instance instSampleableTypeFinset {α : Type} [FinEnum α] : SampleableType (Finset α) :=
  inferInstance

/-- Uniform sampling of size-`n` multisets over a `FinEnum` type. `Sym α n` is the correct finite
analogue of `Multiset α`: a plain `Multiset α` is unbounded in multiplicity and thus not finite,
while `Sym α n` is finite whenever `α` is. We obtain a *computable* uniform sampler from the
canonical enumeration `Sym.finEnum`; for a base type with only a `Fintype` instance use
`SampleableType.ofFintype` instead.

Note this is genuinely uniform on multisets: mapping a uniform `List.Vector α n` through
`Sym.ofVector` is *not* (it weights each multiset by its number of orderings), so we enumerate
`Sym α n` canonically rather than pushing forward from vectors. -/
instance instSampleableTypeSym {α : Type} {n : ℕ} [FinEnum α] [Nonempty α] :
    SampleableType (Sym α n) :=
  letI : FinEnum (Sym α n) := Sym.finEnum n
  haveI : Nonempty (Sym α n) := ⟨Sym.replicate n (Classical.arbitrary α)⟩
  FinEnum.SampleableType _

/-- Uniform sampling of permutations of a `FinEnum` type. `Equiv.Perm α` has `n!` elements when
`Fintype.card α = n`. We obtain a *computable* uniform sampler from the canonical enumeration
`Equiv.Perm.finEnum`. Useful for shuffle-based protocols and oblivious-permutation games. -/
instance instSampleableTypePerm {α : Type} [FinEnum α] :
    SampleableType (Equiv.Perm α) :=
  letI : FinEnum (Equiv.Perm α) := Equiv.Perm.finEnum
  haveI : Nonempty (Equiv.Perm α) := ⟨Equiv.refl α⟩
  FinEnum.SampleableType _

/-- Uniform sampling of injections `β ↪ α` for `FinEnum` types. The number of such embeddings is
`α.card! / (α.card - β.card)!` when `β.card ≤ α.card`, else `0`; the `Nonempty (β ↪ α)`
hypothesis rules out the latter case. We obtain a *computable* uniform sampler from the canonical
enumeration `Function.Embedding.finEnum` (itself computable, unlike Mathlib's `Fintype (β ↪ α)`). -/
instance instSampleableTypeEmbedding {β α : Type}
    [FinEnum β] [FinEnum α] [Nonempty (β ↪ α)] :
    SampleableType (β ↪ α) :=
  letI : FinEnum (β ↪ α) := Function.Embedding.finEnum
  FinEnum.SampleableType _

/-- A function from a finite type `D` with `Fintype` + `DecidableEq` (not necessarily `FinEnum`)
to a `SampleableType` is itself `SampleableType`, transporting the `Fin (Fintype.card D) → α`
sampler across the canonical equivalence `(D → α) ≃ (Fin (Fintype.card D) → α)`.

This is the *noncomputable* counterpart to the computable `FinEnum`-domain instance
`instSampleableTypeFunc`, and is given **lower priority** so that for a `FinEnum` domain the
computable instance is preferred; it is the fallback for `Fintype` + `DecidableEq`-only domains. -/
noncomputable instance (priority := 100) instSampleableTypePiFintype {D : Type}
    [Fintype D] [DecidableEq D] {α : Type} [SampleableType α] : SampleableType (D → α) :=
  -- Provide the `Fin (card D) → α` sampler explicitly: synthesizing it could loop, since for the
  -- abstract `Fintype.card D` the overlapping `instSampleableTypeFunc` descends without converging.
  letI : SampleableType (Fin (Fintype.card D) → α) := instSampleableTypeFinFunc
  SampleableType.ofEquiv
    (α := Fin (Fintype.card D) → α)
    (Equiv.arrowCongr (Fintype.equivFin D).symm (Equiv.refl α))

end instances

section UniformSampleImpl

open OracleSpec OracleComp

variable {ι : Type*} {spec : OracleSpec ι}

/-- Given that the output type of all oracles has a `SampleableType` instance, replace all queries
with uniformly random responses by calling the corresponding `uniformSample` at each query. -/
@[expose] def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t

/-- A uniformly sampled implementation answers each query with the uniform sampler for
that query's response type. -/
@[simp]
lemma uniformSampleImpl_apply [∀ i, SampleableType (spec.Range i)] (t : spec.Domain) :
    uniformSampleImpl (spec := spec) t = $ᵗ spec.Range t := rfl

namespace uniformSampleImpl

variable [∀ i, SampleableType (spec.Range i)]

/-- Interpreting queries by full-support samplers preserves operational reachability. -/
@[simp]
lemma support_simulateQ {α : Type} (oa : OracleComp spec α) :
    support (simulateQ uniformSampleImpl oa) = support oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih => simp [ih]

/-- Full-support query sampling also preserves the finite support when answers are enumerable. -/
@[simp]
lemma finSupport_simulateQ [∀ t, Fintype (spec.Range t)] {α : Type} [DecidableEq α]
    (oa : OracleComp spec α) :
    finSupport (simulateQ uniformSampleImpl oa) = finSupport oa := by
  simp [finSupport_eq_iff_support_eq_coe]

end uniformSampleImpl

end UniformSampleImpl
