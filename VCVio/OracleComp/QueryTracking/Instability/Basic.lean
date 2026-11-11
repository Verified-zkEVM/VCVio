/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.Structures
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Instability of database properties

A *database* is a partial oracle table `D : QueryCache spec`, and a *database property* is a set
of databases. Extend `D` at a fresh input `x` (one with `D x = none`) by an answer `u` drawn from
the answer measure `μₓ`, giving `D[x ↦ u]`. This file defines the worst-case probability that such
an extension moves a database from one property into another, and proves the rules for combining
these bounds. Nothing in this file is quantum.

## Why these quantities

In the finite bitstring random-oracle model, sample a uniformly random function `H` once.
A quantum algorithm queries it through `|x,y⟩ ↦ |x,y ⊕ H(x)⟩`, where `⊕` is bitwise XOR;
linearity specifies the action on superpositions.
The compressed standard oracle of Zhandry (ePrint 2018/276, Section 3, "Oracle Variations")
represents `H` by a private quantum register with database basis states `|D⟩`, in which a query
adds, changes or removes one entry. This register is not a record of queries obtained by measuring
the algorithm. A database property `P` gives the projector `Π_P` onto the databases in `P`.

The classical instability `I(P,t)` bounds amplitude transfer in the finite uniform oracle model.
Let `C_t = Π_{≤t} C Π_{≤t}`, where `C` is one compressed-oracle query and `Π_{≤t}` keeps databases
with at most `t` entries. The property projector `Π_P` keeps database basis states in `P` and acts
as the identity on the algorithm's other registers. Here `‖·‖` is the operator norm.
Chiesa–Manohar–Spooner, Lemma 5.10 (ePrint 2019/834, PDF p. 24), proves
`‖Π_P C_t Π_{Pᶜ}‖² ≤ 6 I(P,t)`. Thus one query transfers at most `√(6 I(P,t))` amplitude from
the complement subspace into `P` for a unit input vector. The classical definition uses `< t`;
the quantum cutoff uses `≤ t`.

For a partition with projectors `Π_i`, Chiesa–Di–Hu–Zheng, Theorem 5.4 (ePrint 2025/2166,
PDF p. 31), proves `‖[V,C_t]‖² ≤ 80 I(P,t)`, where `[A,B] = AB - BA` and
`V = Σ_i Π_i ⊗ V_i`. Each `V_i` is a unitary on the other registers whose extension commutes
with `C_t`, as required in that theorem.

These are paper statements motivating the API. This file proves the classical calculus for
arbitrary chosen answer probability measures. It does not construct the compressed oracle,
prove either quantum norm bound, or iterate them over an adversary.

## Main definitions

* `OracleSpec.QueryCache.updateProb D x T`: the probability `μₓ {u | D[x ↦ u] ∈ T}`.
* `OracleSpec.QueryCache.flip S T t`: the supremum of `updateProb D x T` over databases `D ∈ S`
  with fewer than `t` entries and fresh inputs `x`; `0` when there is no such pair.
* `OracleSpec.QueryCache.instability P t`: the larger of `flip Pᶜ P t` and `flip P Pᶜ t`.
* `OracleSpec.QueryCache.condFlip P Q t` and `OracleSpec.QueryCache.condInstability P Q t`: the
  same two quantities with source and target both restricted to `Q`.
* `OracleSpec.QueryCache.partitionInstability P t`: for an indexed family `P`, the supremum over
  `i` of the flip probability from `P i` to the union of the other members.

## Main statements

* `updateProb_eq_prEvent`: for `Type` answers, the update measure equals the event probability of
  one classical oracle query.
* `flip_mono`, `flip_union_left`, `flip_iUnion_left`, `flip_union_right_le`, `flip_empty_left`:
  the closure rules of the flip probability.
* `condInstability_le_instability` and `instability_union_le`: restricting to `Q` lowers
  instability, and `instability (P ∪ Q) t ≤ condInstability P Qᶜ t + instability Q t`.
* `partitionInstability_eq_iSup_flip_compl` and `partitionInstability_cond`: on a partition the
  target of each flip is the complement of its source, and the two-class partition `{P, Pᶜ}`
  has partition instability `instability P t`.

## Conventions

* A cache is a dependent partial function `x ↦ Option (spec.Range x)`, without the chronology or
  multiplicity of a log. Its size `D.toSet.encard` counts graph entries, equivalently populated
  keys. A cache may be infinite; then it fails every finite bound `D.toSet.encard < t`.
  The strict bound follows Chiesa–Manohar–Spooner, Definition 5.4; `t` does not itself certify an
  adversary's number of oracle calls.
* The answer at the fresh input is drawn from `[AnswerMeasure spec]`. The cited papers take
  uniform answers, which is `[UniformAnswerMeasure spec]`, and `updateProb_eq_card_div` gives the
  counting form in that case. Answer measures are normalized probability measures on the discrete
  sigma algebra; they may be nonuniform and query-dependent. No measurable space on caches is
  required. A cached oracle call at an occupied input reuses its answer; `updateProb` resamples it.
* Index and answer types may live in any universes.
* `partitionInstability` accepts any indexed family. A statement that reads it as the instability
  of a partition must assume that the members are pairwise disjoint and cover all databases, as
  `partitionInstability_eq_iSup_flip_compl` does.

## References

* M. Zhandry, *How to Record Quantum Queries, and Applications to Quantum Indifferentiability*,
  CRYPTO 2019, [ePrint 2018/276](https://eprint.iacr.org/2018/276), March 1, 2019 revision:
  Section 3, "Compressed Standard Oracles" (PDF pp. 12–14); Lemma 4 (PDF p. 15) proves
  equivalence with the standard oracle.
* A. Chiesa, P. Manohar, N. Spooner, *Succinct Arguments in the Quantum Random Oracle Model*,
  TCC 2019, ePrint 2019/834: Definition 5.4 (PDF p. 23), Proposition 5.5, Definition 5.6
  (PDF p. 24), Lemma 5.10 (PDF p. 24), Definition 5.11 and Proposition 5.12 (PDF p. 26).
* A. Chiesa, Z. Di, Z. Hu, Y. Zheng, *How to Prove Post-Quantum Security for Succinct
  Non-Interactive Reductions*, ePrint 2025/2166: Definitions 5.2 and 5.3 and Theorem 5.4
  (PDF p. 31).
-/

public section

open ENNReal OracleComp Set

universe u v

namespace OracleSpec.QueryCache

/-- A database with fewer than `t` entries has its populated keys inside a finite set of fewer
than `t` points. -/
lemma exists_finset_card_lt_of_encard_lt {ι : Type u} {spec : OracleSpec.{u, v} ι}
    {D : QueryCache spec} {t : ℕ} (h : D.toSet.encard < t) :
    ∃ S : Finset spec.Domain, S.card < t ∧ ∀ x, D x ≠ none → x ∈ S := by
  classical
  have hfin : D.toSet.Finite := Set.encard_lt_top_iff.mp (h.trans (ENat.natCast_lt_top t))
  refine ⟨hfin.toFinset.image Sigma.fst, ?_, fun x hx => ?_⟩
  · rw [hfin.encard_eq_coe_toFinset_card] at h
    exact lt_of_le_of_lt Finset.card_image_le (by exact_mod_cast h)
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hx
    exact Finset.mem_image.mpr ⟨⟨x, u⟩, hfin.mem_toFinset.mpr hu, rfl⟩

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} [DecidableEq ι] [AnswerMeasure spec]
  {S S' T T' P Q : Set (QueryCache spec)} {D : QueryCache spec} {x : spec.Domain} {t t' : ℕ}

/-! ## One-step update probability -/

/-- The probability `μₓ {u | D[x ↦ u] ∈ T}` that updating `D` at `x` with an answer drawn from
the answer measure `μₓ` of `x` gives a database in `T`. No uniformity is assumed.

The update overwrites any answer already stored at `x`. When `D x = none` it is a fresh
one-entry extension, which is the case `flip` uses. -/
@[expose] noncomputable def updateProb (D : QueryCache spec) (x : spec.Domain)
    (T : Set (QueryCache spec)) : ℝ≥0∞ :=
  AnswerMeasure.toMeasure x {u | D.cacheQuery x u ∈ T}

/-- For answers in `Type`, the update measure equals the event probability of a single query. -/
lemma updateProb_eq_prEvent {ι : Type u} {spec : OracleSpec.{u, 0} ι} [DecidableEq ι]
    [AnswerMeasure spec] (D : QueryCache spec) (x : spec.Domain)
    (T : Set (QueryCache spec)) :
    D.updateProb x T =
      Pr{let u ← (query x : OracleComp spec (spec.Range x))}[D.cacheQuery x u ∈ T] := by
  let : MeasurableSpace (spec.Range x) := ⊤
  rw [prEvent_eq_evalDist_of_discrete, evalDist_query,
    MeasureTheory.trim_measurableSet_eq _ MeasurableSpace.measurableSet_top]
  rfl

/-- The update probability is monotone in the target property. -/
lemma updateProb_mono (D : QueryCache spec) (x : spec.Domain) (h : T ⊆ T') :
    D.updateProb x T ≤ D.updateProb x T' :=
  MeasureTheory.measure_mono fun _ hu => h hu

/-- Union bound for the update probability. -/
lemma updateProb_union_le (D : QueryCache spec) (x : spec.Domain) (T T' : Set (QueryCache spec)) :
    D.updateProb x (T ∪ T') ≤ D.updateProb x T + D.updateProb x T' :=
  MeasureTheory.measure_union_le _ _

/-- Updating a database lands in the empty property with probability zero. -/
@[simp]
lemma updateProb_empty (D : QueryCache spec) (x : spec.Domain) : D.updateProb x ∅ = 0 :=
  MeasureTheory.measure_empty

/-- The probability of an update landing in any property is at most one. -/
lemma updateProb_le_one (D : QueryCache spec) (x : spec.Domain) (T : Set (QueryCache spec)) :
    D.updateProb x T ≤ 1 :=
  MeasureTheory.prob_le_one

/-- Under uniform answers, the update probability is the proportion of answers that land in
the target property. -/
lemma updateProb_eq_card_div {ι : Type u} {spec : OracleSpec.{u, v} ι} [DecidableEq ι]
    [UniformAnswerMeasure spec] (D : QueryCache spec) (x : spec.Domain)
    [Fintype (spec.Range x)] (T : Set (QueryCache spec))
    [DecidablePred fun u : spec.Range x => D.cacheQuery x u ∈ T] :
    D.updateProb x T =
      ((Finset.univ.filter fun u : spec.Range x => D.cacheQuery x u ∈ T).card : ℝ≥0∞) /
        Fintype.card (spec.Range x) := by
  let : MeasurableSpace (spec.Range x) := ⊤
  rw [updateProb, AnswerMeasure.toMeasure_eq_uniformOn,
    ProbabilityTheory.uniformOn_univ_apply_setOf]

/-! ## Flip probability -/

/-- The flip probability from `S` to `T` with query bound `t`:
`flip S T t = sup {μₓ {u | D[x ↦ u] ∈ T} | D ∈ S, |D| < t, D x = none}`,
where `|D| = D.toSet.encard` and `μₓ` is the answer measure of `x`. It is `0` when there is no
such pair, in particular when `t = 0`. The supremum need not be attained.

"Flip" is the literature's name for this directed quantity; `S` and `T` need not be disjoint.
For uniform answers this is Chiesa–Manohar–Spooner, Definition 5.4 (ePrint 2019/834, PDF p. 23),
and Chiesa–Di–Hu–Zheng, Definition 5.2 (ePrint 2025/2166, PDF p. 31). -/
@[expose] noncomputable def flip (S T : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  ⨆ (D : QueryCache spec) (_ : D ∈ S) (_ : D.toSet.encard < t) (x : spec.Domain)
    (_ : D x = none), D.updateProb x T

/-- A bound on the flip probability is a bound on every admissible one-step extension. -/
lemma flip_le_iff {c : ℝ≥0∞} :
    flip S T t ≤ c ↔
      ∀ D ∈ S, D.toSet.encard < t → ∀ x, D x = none → D.updateProb x T ≤ c := by
  simp only [flip, iSup_le_iff]

/-- Every admissible one-step extension is bounded by the flip probability. -/
lemma updateProb_le_flip (hD : D ∈ S) (ht : D.toSet.encard < t) (hx : D x = none) :
    D.updateProb x T ≤ flip S T t :=
  flip_le_iff.mp le_rfl D hD ht x hx

/-- The flip probability is monotone in the source property, the target property and the query
bound. -/
theorem flip_mono (hS : S ⊆ S') (hT : T ⊆ T') (ht : t ≤ t') : flip S T t ≤ flip S' T' t' :=
  flip_le_iff.mpr fun D hD hlt x hx => (updateProb_mono D x hT).trans
    (updateProb_le_flip (hS hD) (hlt.trans_le (by exact_mod_cast ht)) hx)

/-- The flip probability out of a union of an indexed family is the supremum of the flip
probabilities out of its members. -/
theorem flip_iUnion_left {κ : Sort*} (S : κ → Set (QueryCache spec)) (T : Set (QueryCache spec))
    (t : ℕ) : flip (⋃ i, S i) T t = ⨆ i, flip (S i) T t := by
  refine le_antisymm (flip_le_iff.mpr fun D hD hlt x hx => ?_)
    (iSup_le fun i => flip_mono (subset_iUnion S i) le_rfl le_rfl)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hD
  exact (updateProb_le_flip hi hlt hx).trans (le_iSup (fun i => flip (S i) T t) i)

/-- The flip probability out of a union is the larger of the two flip probabilities. -/
theorem flip_union_left (S S' T : Set (QueryCache spec)) (t : ℕ) :
    flip (S ∪ S') T t = max (flip S T t) (flip S' T t) := by
  refine le_antisymm (flip_le_iff.mpr ?_)
    (max_le (flip_mono subset_union_left le_rfl le_rfl)
      (flip_mono subset_union_right le_rfl le_rfl))
  rintro D (hD | hD) hlt x hx
  · exact (updateProb_le_flip hD hlt hx).trans (le_max_left _ _)
  · exact (updateProb_le_flip hD hlt hx).trans (le_max_right _ _)

/-- Union bound for the flip probability into a union. -/
theorem flip_union_right_le (S T T' : Set (QueryCache spec)) (t : ℕ) :
    flip S (T ∪ T') t ≤ flip S T t + flip S T' t :=
  flip_le_iff.mpr fun D hD hlt x hx => (updateProb_union_le D x T T').trans
    (add_le_add (updateProb_le_flip hD hlt hx) (updateProb_le_flip hD hlt hx))

/-- There is no transition out of the empty source property. -/
@[simp]
theorem flip_empty_left (T : Set (QueryCache spec)) (t : ℕ) : flip ∅ T t = 0 :=
  nonpos_iff_eq_zero.mp (flip_le_iff.mpr fun _ hD => (notMem_empty _ hD).elim)

/-- The flip probability into the empty target property is zero. -/
@[simp]
theorem flip_empty_right (S : Set (QueryCache spec)) (t : ℕ) : flip S ∅ t = 0 :=
  nonpos_iff_eq_zero.mp (flip_le_iff.mpr fun D _ _ x _ => (updateProb_empty D x).le)

/-- With query bound `0` there is no admissible database, so the flip probability is `0`. -/
@[simp]
theorem flip_zero (S T : Set (QueryCache spec)) : flip S T 0 = 0 :=
  nonpos_iff_eq_zero.mp (flip_le_iff.mpr fun _ _ hlt => by simp at hlt)

/-- Every flip probability is at most one. -/
theorem flip_le_one (S T : Set (QueryCache spec)) (t : ℕ) : flip S T t ≤ 1 :=
  flip_le_iff.mpr fun D _ _ x _ => updateProb_le_one D x T

/-! ## Instability -/

/-- The instability of `P` with query bound `t`: the worst-case probability that one fresh
answer changes whether a database with fewer than `t` entries lies in `P`,
`I(P, t) = max (flip Pᶜ P t) (flip P Pᶜ t)`. It is `0` at `t = 0`.

This is Chiesa–Manohar–Spooner, Definition 5.6 (ePrint 2019/834, PDF p. 24), for an arbitrary
answer measure in place of uniform answers. It is a classical quantity; its use in quantum proofs
is through their Lemma 5.10. -/
@[expose] noncomputable def instability (P : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  max (flip Pᶜ P t) (flip P Pᶜ t)

/-- Instability is symmetric under complement. -/
@[simp]
theorem instability_compl (P : Set (QueryCache spec)) (t : ℕ) :
    instability Pᶜ t = instability P t := by
  rw [instability, instability, compl_compl, max_comm]

/-- Instability is monotone in the query bound. -/
theorem instability_mono_query (P : Set (QueryCache spec)) (h : t ≤ t') :
    instability P t ≤ instability P t' :=
  max_le_max (flip_mono le_rfl le_rfl h) (flip_mono le_rfl le_rfl h)

/-- A zero query bound gives zero instability. -/
@[simp]
theorem instability_zero (P : Set (QueryCache spec)) : instability P 0 = 0 := by
  simp [instability]

/-- The empty database property has zero instability. -/
@[simp]
theorem instability_empty (t : ℕ) : instability (∅ : Set (QueryCache spec)) t = 0 := by
  simp [instability]

/-- The property of all databases has zero instability. -/
@[simp]
theorem instability_univ (t : ℕ) : instability (univ : Set (QueryCache spec)) t = 0 := by
  simp [instability]

/-- The instability of any database property is at most one. -/
theorem instability_le_one (P : Set (QueryCache spec)) (t : ℕ) : instability P t ≤ 1 :=
  max_le (flip_le_one _ _ t) (flip_le_one _ _ t)

/-! ## Conditional instability -/

/-- The flip probability into `P` within `Q`: `flip (Pᶜ ∩ Q) (P ∩ Q) t`. Both the database before
the extension and the one after it must lie in `Q`.

This restricts the transitions counted, without renormalizing: it is not the conditional
probability `Pr[D' ∈ P | D' ∈ Q]`. It is Chiesa–Manohar–Spooner's conditional flip probability,
Definition 5.11 (ePrint 2019/834, PDF p. 26). -/
@[expose] noncomputable def condFlip (P Q : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  flip (Pᶜ ∩ Q) (P ∩ Q) t

/-- The instability of `P` within `Q`: `max (condFlip P Q t) (condFlip Pᶜ Q t)`, the worst-case
probability that one fresh answer changes membership in `P` while staying in `Q`. As in
`condFlip`, "conditional" means restricting the transitions, not dividing by a probability
(Chiesa–Manohar–Spooner, Definition 5.11, ePrint 2019/834, PDF p. 26). -/
@[expose] noncomputable def condInstability (P Q : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  max (condFlip P Q t) (condFlip Pᶜ Q t)

/-- Restricting both endpoints to `Q` cannot increase the entering flip probability. -/
theorem condFlip_le_flip (P Q : Set (QueryCache spec)) (t : ℕ) :
    condFlip P Q t ≤ flip Pᶜ P t :=
  flip_mono inter_subset_left inter_subset_left le_rfl

/-- Restricting both endpoints to `Q` cannot increase instability. -/
theorem condInstability_le_instability (P Q : Set (QueryCache spec)) (t : ℕ) :
    condInstability P Q t ≤ instability P t :=
  max_le_max (condFlip_le_flip P Q t) (by simpa using condFlip_le_flip Pᶜ Q t)

/-- Restricting both endpoints to all databases leaves the entering flip unchanged. -/
@[simp]
theorem condFlip_univ (P : Set (QueryCache spec)) (t : ℕ) :
    condFlip P univ t = flip Pᶜ P t := by
  simp [condFlip]

/-- Restricting both endpoints to all databases leaves instability unchanged. -/
@[simp]
theorem condInstability_univ (P : Set (QueryCache spec)) (t : ℕ) :
    condInstability P univ t = instability P t := by
  simp [condInstability, instability]

/-- Complementing `P` with the endpoint restriction `Q` held fixed leaves instability unchanged. -/
@[simp]
theorem condInstability_compl (P Q : Set (QueryCache spec)) (t : ℕ) :
    condInstability Pᶜ Q t = condInstability P Q t := by
  rw [condInstability, condInstability, compl_compl, max_comm]

/-- The instability of a union is at most the instability of the first property conditioned on
the complement of the second, plus the instability of the second. -/
theorem instability_union_le (P Q : Set (QueryCache spec)) (t : ℕ) :
    instability (P ∪ Q) t ≤ condInstability P Qᶜ t + instability Q t := by
  have hunion : P ∪ Q = P ∩ Qᶜ ∪ Q := by rw [inter_union_distrib_right, compl_union_self,
    inter_univ]
  have hcompl : (P ∪ Q)ᶜ = Pᶜ ∩ Qᶜ := compl_union P Q
  refine max_le ?_ ?_
  · calc flip (P ∪ Q)ᶜ (P ∪ Q) t
        = flip (Pᶜ ∩ Qᶜ) (P ∩ Qᶜ ∪ Q) t := by rw [hcompl, ← hunion]
      _ ≤ flip (Pᶜ ∩ Qᶜ) (P ∩ Qᶜ) t + flip (Pᶜ ∩ Qᶜ) Q t := flip_union_right_le _ _ _ t
      _ ≤ condInstability P Qᶜ t + instability Q t :=
          add_le_add (le_max_left _ _)
            ((flip_mono inter_subset_right le_rfl le_rfl).trans (le_max_left _ _))
  · calc flip (P ∪ Q) (P ∪ Q)ᶜ t
        = max (flip (P ∩ Qᶜ) (Pᶜ ∩ Qᶜ) t) (flip Q (Pᶜ ∩ Qᶜ) t) := by
          rw [hcompl, hunion, flip_union_left]
      _ ≤ max (condInstability P Qᶜ t) (instability Q t) :=
          max_le_max
            ((le_of_eq (by rw [condFlip, compl_compl])).trans
              (le_max_right (condFlip P Qᶜ t) (condFlip Pᶜ Qᶜ t)))
            ((flip_mono le_rfl inter_subset_right le_rfl).trans (le_max_right _ _))
      _ ≤ condInstability P Qᶜ t + instability Q t := max_le_add_of_nonneg zero_le zero_le

/-! ## Instability of an indexed family -/

/-- The instability of an indexed family of properties: `sup_i flip (P i) (⋃ j ≠ i, P j) t`, the
worst-case probability that one fresh answer moves a database from one member into another.

When the members are pairwise disjoint and cover all databases, this is the probability of
changing class (Chiesa–Di–Hu–Zheng, Definition 5.3, ePrint 2025/2166, PDF p. 31), and
`partitionInstability_eq_iSup_flip_compl` rewrites it with complements. For overlapping members
the target may contain the source database, and the quantity is not a change of class. -/
@[expose] noncomputable def partitionInstability {κ : Type*} (P : κ → Set (QueryCache spec))
    (t : ℕ) : ℝ≥0∞ :=
  ⨆ i, flip (P i) (⋃ j, ⋃ (_ : j ≠ i), P j) t

/-- Partition instability is monotone in the query bound. -/
theorem partitionInstability_mono_query {κ : Type*} (P : κ → Set (QueryCache spec))
    (h : t ≤ t') : partitionInstability P t ≤ partitionInstability P t' :=
  iSup_mono fun _ => flip_mono le_rfl le_rfl h

/-- The instability of any indexed family of properties is at most one. -/
theorem partitionInstability_le_one {κ : Type*} (P : κ → Set (QueryCache spec)) (t : ℕ) :
    partitionInstability P t ≤ 1 :=
  iSup_le fun _ => flip_le_one _ _ t

/-- In a partition, the other members together are the complement of a member, so the partition
instability is the supremum of the flip probabilities from members to their complements. -/
theorem partitionInstability_eq_iSup_flip_compl {κ : Type*} {P : κ → Set (QueryCache spec)}
    (hdisj : Pairwise (Function.onFun Disjoint P)) (hcover : ⋃ i, P i = univ) (t : ℕ) :
    partitionInstability P t = ⨆ i, flip (P i) (P i)ᶜ t := by
  have hothers : ∀ i, (⋃ j, ⋃ (_ : j ≠ i), P j) = (P i)ᶜ := by
    intro i
    ext D
    simp only [mem_iUnion, mem_compl_iff, exists_prop]
    refine ⟨fun ⟨j, hj, hD⟩ hi => disjoint_left.mp (hdisj hj) hD hi, fun hi => ?_⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ▸ mem_univ D)
    exact ⟨j, fun hji => hi (hji ▸ hj), hj⟩
  simp only [partitionInstability, hothers]

/-- The two-class partition `{P, Pᶜ}` defined by `Bool.cond` has instability `instability P t`. -/
theorem partitionInstability_cond (P : Set (QueryCache spec)) (t : ℕ) :
    partitionInstability (fun b : Bool => cond b P Pᶜ) t = instability P t := by
  rw [partitionInstability_eq_iSup_flip_compl _
    ((union_eq_iUnion (s₁ := P) (s₂ := Pᶜ)).symm.trans (union_compl_self P)), iSup_bool_eq]
  · simp only [Bool.cond_true, Bool.cond_false, compl_compl]
    exact max_comm _ _
  · rintro (_ | _) (_ | _) h
    · exact (h rfl).elim
    · exact disjoint_compl_left
    · exact disjoint_compl_right
    · exact (h rfl).elim

end OracleSpec.QueryCache
