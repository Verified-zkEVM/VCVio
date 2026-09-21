/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.PFunctor.Basic

/-!
# Specifications of Available Oracles

An `OracleSpec ι` specifies a collection of oracles indexed by `ι`, given as the map sending
each index to the output type of that oracle. It is the same data as a `PFunctor`, and the
bridge `toPFunctor` / `ofPFunctor` exposes that algebra: oracle specifications can be combined
with `+` (a disjoint sum of oracle sets), `*`, `OracleSpec.sigma`, and `OracleSpec.pi`. The
empty specification `[]ₒ` provides no oracles.

This file also defines the standard sampling specifications `coinSpec`, `unifSpec`, and
`probSpec`.
-/

@[expose] public section

universe u u' v w

/-- An `OracleSpec ι` specifies a set of oracles indexed by `ι`.
Defined as a map from each input to the type of the oracle's output. -/
def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  ι → Type v

/- `OracleSpec ι` is a one-field wrapper around `ι → Type v`. Lean checks the types of implicit
and instance-implicit arguments, and of metavariable assignments, at `.implicit` transparency,
where an ordinary `def` does not unfold. Proofs that unfold the reducible layers above the wrapper
(`toPFunctor`, `ofFn`, `unifSpec`, `OracleComp`, `ProbComp`) then hold terms of type `ι → Type v`
where an `OracleSpec ι` is expected, and instance searches whose argument types need the wrapper
to unfold. Without this attribute the former fail with "the target expression is not type-correct
under the `implicit` transparency level" (the eager random-oracle table lemmas in
`QueryTracking/RandomOracle/EagerTable.lean`) and the latter time out (the `Decidable` searches in
`MerkleTree/Inductive/Batch/Disagreement.lean`). Making the wrapper implicit-reducible closes that
gap once, for every such site. Instance synthesis at the erased `PFunctor` literal does not need
it (`VCVioTest/PFunctorFacade.lean` checks that), and the abstract API above the wrapper
(`Domain`, `Range`, `query`, and the spec combinators) is unaffected. -/
attribute [implicit_reducible] OracleSpec

namespace OracleSpec

variable {ι : Type u}

@[reducible]
def toPFunctor (spec : OracleSpec ι) : PFunctor := PFunctor.mk ι spec

@[reducible, inline]
def ofPFunctor (P : PFunctor) : OracleSpec P.A := P.B

@[simp] lemma toPFunctor_ofPFunctor (P : PFunctor) :
    OracleSpec.toPFunctor (OracleSpec.ofPFunctor P) = P := rfl

@[simp] lemma ofPFunctor_toPFunctor (spec : OracleSpec ι) :
    OracleSpec.ofPFunctor (OracleSpec.toPFunctor spec) = spec := rfl

abbrev Domain (_spec : OracleSpec ι) : Type _ := ι
abbrev Range (spec : OracleSpec ι) (t : ι) : Type _ := spec t

/-! ## Typeclass data on indices and answer types

`Domain` and `Range` are reducible, so a global instance concluding `C spec.Domain` or
`C (spec.Range t)` for a generic `spec` is indexed as `C ι`, respectively `C (?spec ?t)`: a
candidate for every `C _` goal, with `spec` undetermined. Instance search then invents a
specification through `ofFn`, and either times out (VCVio#772) or answers an ordinary
`DecidableEq`, `Fintype`, or `Inhabited` goal through oracle-specification data. No such
instance exists. Index equality is an ordinary `[DecidableEq ι]` hypothesis, and data on answer
types are ordinary `[DecidableEq (spec.Range t)]`, `[Fintype (spec.Range t)]`, or
`[Inhabited (spec.Range t)]` hypotheses, quantified over `t` when a statement ranges over
arbitrary queries. Specifications built with `ofFn` reduce to their answer types, so
`unifSpec`, `coinSpec`, and `A →ₒ B` need no instances of their own; `+` combines the
per-branch instances of its summands. -/

section ofFn

@[reducible, always_inline] def ofFn {ι : Type u} (F : ι → Type v) : OracleSpec ι := F
notation:25 (name := singletonSpec) A:25 " →ₒ " B:26 =>
  OracleSpec.ofFn (ι := A) (fun _ => B)

end ofFn

section add

/-- `spec₁ + spec₂` specifies access to oracles in both `spec₁` and `spec₂`.
The input is split as a sum type of the two original input sets.
This corresponds exactly to addition of the corresponding `PFunctor`.

The ordinary instance reducibility assigned by the `instance` command lets its `HAdd.hAdd`
projection reduce while checking dependent implicit types such as
`(spec₁ + spec₂).Range (.inl t)`, without unfolding combined specifications during ordinary
reducible-transparency tactic matching. -/
instance {ι ι'} :
    HAdd (OracleSpec ι) (OracleSpec ι') (OracleSpec (ι ⊕ ι')) where
  hAdd spec spec' :=
    OracleSpec.ofPFunctor (PFunctor.sum spec.toPFunctor spec'.toPFunctor)

lemma add_def {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι') :
    spec + spec' = Sum.elim spec spec' := rfl

@[simp] lemma add_apply_inl {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    (t : ι) : (spec + spec') (.inl t) = spec t := rfl

@[simp] lemma add_apply_inr {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    (t : ι') : (spec + spec') (.inr t) = spec' t := rfl

/-- Deliberately not `@[simp]`: `toPFunctor` occurs inside the (instance-carrying)
type of an `OracleComp`, so rewriting with this under a `simulateQ`/`liftM` strands
the goal in a form the `simulateQ_query` family can no longer match. -/
lemma toPFunctor_add {ι : Type u} {ι' : Type u'}
    (spec : OracleSpec ι) (spec' : OracleSpec ι') :
    (spec + spec').toPFunctor = spec.toPFunctor + spec'.toPFunctor := rfl

@[simp] lemma ofPFunctor_add (P P' : PFunctor) :
    OracleSpec.ofPFunctor (P + P') = OracleSpec.ofPFunctor P + OracleSpec.ofPFunctor P' := rfl

/-! The answer types of a sum specification inherit the per-branch instances of its summands.
These are indexed on the `HAdd.hAdd` head of the combined specification, so they apply only to
goals about a sum. -/

instance {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    [h : ∀ t, Fintype (spec.Range t)] [h' : ∀ t, Fintype (spec'.Range t)] :
    ∀ t, Fintype ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

instance {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    [h : ∀ t, DecidableEq (spec.Range t)] [h' : ∀ t, DecidableEq (spec'.Range t)] :
    ∀ t, DecidableEq ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

instance {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    [h : ∀ t, Inhabited (spec.Range t)] [h' : ∀ t, Inhabited (spec'.Range t)] :
    ∀ t, Inhabited ((spec + spec').Range t)
  | .inl i => h i
  | .inr i => h' i

end add

section sigma

/-- Given an indexed set of `OracleSpec`, specify access to all of the oracles,
by requiring an index into the corresponding oracle in the input. -/
protected def sigma {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec ((i : ι) × (specs i).Domain) :=
  fun t => specs t.1 t.2

@[simp] lemma sigma_apply {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i))
    (t : (i : ι) × (specs i).Domain) : OracleSpec.sigma specs t = specs t.1 t.2 := rfl

@[simp] lemma toPFunctor_sigma {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec.toPFunctor (OracleSpec.sigma specs) =
      PFunctor.sigma fun i => (OracleSpec.toPFunctor (specs i)) := rfl

@[simp] lemma ofPFunctor_sigma {ι} (P : ι → PFunctor) :
    OracleSpec.ofPFunctor (PFunctor.sigma P) =
      OracleSpec.sigma fun i => OracleSpec.ofPFunctor (P i) := rfl

end sigma

section mul

/-- `spec₁ * spec₂` represents an oracle that takes in a pair of inputs for each set,
and returns an element in the output of one oracle or the other.
The corresponds exactly to multiplication in `PFunctor`. -/
instance {ι ι'} : HMul (OracleSpec ι) (OracleSpec ι') (OracleSpec (ι × ι'))
  where hMul spec spec' := fun t => spec.Range t.1 ⊕ spec'.Range t.2

@[simp] lemma mul_apply {ι ι'} (spec : OracleSpec ι) (spec' : OracleSpec ι')
    (t : ι × ι') : (spec * spec').Range t = (spec.Range t.1 ⊕ spec'.Range t.2) := rfl

@[simp] lemma toPFunctor_mul {ι : Type u} {ι' : Type u'}
    (spec : OracleSpec ι) (spec' : OracleSpec ι') :
    (spec * spec').toPFunctor = spec.toPFunctor * spec'.toPFunctor := rfl

@[simp] lemma ofPFunctor_mul (P P' : PFunctor) :
    OracleSpec.ofPFunctor (P * P') = OracleSpec.ofPFunctor P * OracleSpec.ofPFunctor P' := rfl

end mul

section pi

/-- Given an indexed set of `OracleSpec`, specify access to an oracle that given an input to
the oracle for each index returns an index and an output for that index. -/
protected def pi {ι : Type _} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec ((i : ι) → (specs i).Domain) :=
  fun t => (i : ι) × specs i (t i)

@[simp] lemma pi_apply {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i))
    (t : (i : ι) → (specs i).Domain) : OracleSpec.pi specs t = ((i : ι) × specs i (t i)) := rfl

@[simp] lemma toPFunctor_pi {ι} {τ : ι → Type _} (specs : (i : ι) → OracleSpec (τ i)) :
    OracleSpec.toPFunctor (OracleSpec.pi specs) =
      PFunctor.pi fun i => (OracleSpec.toPFunctor (specs i)) := rfl

@[simp] lemma ofPFunctor_pi {ι} (P : ι → PFunctor) :
    OracleSpec.ofPFunctor (PFunctor.pi P) =
      OracleSpec.pi fun i => OracleSpec.ofPFunctor (P i) := rfl

end pi

section emptySpec

/-- Specifies access to no oracles, using the empty type as the indexing type. -/
@[reducible] def emptySpec : OracleSpec PEmpty := PEmpty →ₒ PEmpty
notation "[]ₒ" => emptySpec

@[simp] lemma toPFunctor_emptySpec : []ₒ.toPFunctor = 0 := rfl

@[simp] lemma ofPFunctor_zero : OracleSpec.ofPFunctor 0 = []ₒ := rfl

end emptySpec

end OracleSpec

/-- Access to a coin flipping oracle. Because of termination rules in Lean this is slightly
weaker than `unifSpec`, as we have only finitely many coin flips. -/
@[reducible] def coinSpec : OracleSpec.{0, 0} Unit := Unit →ₒ Bool

section unifSpec

/-- Access to oracles for uniformly selecting from `Fin (n + 1)` for arbitrary `n : ℕ`.
By adding `1` to the index we avoid selection from the empty type `Fin 0 ≃ empty`. -/
@[inline, reducible] def unifSpec : OracleSpec ℕ :=
  OracleSpec.ofFn fun n => Fin (n + 1)

end unifSpec

section probSpec
/-- Select uniformly from `Fin (m + 1)` for a pair `(n, m) : ℕ × ℕ`, where the first
component is unused. -/
@[inline, reducible] def probSpec : OracleSpec (ℕ × ℕ) :=
  OracleSpec.ofFn fun (_n, m) => Fin (m + 1)

end probSpec
