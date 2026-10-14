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

A *database* is a partial oracle table, here a `QueryCache`. A *database property* is a set of
databases. This file defines the classical quantities that measure how likely one fresh oracle
answer is to move a database from one property into another, and proves their closure rules.

Compressed-oracle arguments in the quantum random-oracle model bound the effect of one quantum
query by these quantities, so each application reduces to a statement about extending a partial
table at one fresh point with one sampled answer. Nothing in this file is quantum.

## Main definitions

* `OracleSpec.QueryCache.extendProb D x T`: the probability that `D` extended at `x` by a sampled
  answer lies in `T`.
* `OracleSpec.QueryCache.flip S T t`: the supremum of `extendProb D x T` over databases `D ∈ S`
  with fewer than `t` entries and points `x` not in `D`. It is `0` when no such pair exists.
* `OracleSpec.QueryCache.instability P t`: the larger of `flip Pᶜ P t` and `flip P Pᶜ t`.
* `OracleSpec.QueryCache.condFlip P Q t` and `OracleSpec.QueryCache.condInstability P Q t`: the
  same two quantities with source and target restricted to `Q`.
* `OracleSpec.QueryCache.partitionInstability P t`: for an indexed family `P`, the supremum over
  `i` of the flip probability from `P i` to the union of the other members.

## Main statements

* `flip_mono`, `flip_union_left`, `flip_iUnion_left`, `flip_union_right_le`, `flip_empty_left`:
  the closure rules of the flip probability.
* `condInstability_le_instability` and `instability_union_le`: conditioning lowers instability,
  and `instability (P ∪ Q) t ≤ condInstability P Qᶜ t + instability Q t`.
* `partitionInstability_eq_iSup_flip_compl` and `partitionInstability_cond`: on a partition the
  target of each flip is the complement of its source, and the two-class partition `{P, Pᶜ}`
  has partition instability `instability P t`.

## Implementation notes

The number of entries of a database `D` is `D.toSet.encard`, and a query bound is a natural
number `t`, so "fewer than `t` entries" is `D.toSet.encard < t`. The answer at the fresh point is
drawn from the answer measure of the specification. The definitions and closure rules therefore
hold for any `[AnswerMeasure spec]`; the cited papers take uniform answers, which is
`[UniformAnswerMeasure spec]`, and `extendProb_eq_card_div` gives the counting form in that case.

Answer types live in `Type`: `extendProb` is stated with `Pr{…}[…]`, whose computations return
values in `Type`. The index type of the specification may live in any universe.

`partitionInstability` accepts any indexed family. A statement that uses it as the instability of
a partition must assume pairwise disjointness and covering, as
`partitionInstability_eq_iSup_flip_compl` does.

## References

* Alessandro Chiesa, Peter Manohar, Nicholas Spooner, *Succinct Arguments in the Quantum Random
  Oracle Model*, TCC 2019: Definitions 5.4, 5.6 and 5.11, Propositions 5.5 and 5.12.
* Alessandro Chiesa, Zijing Di, Zihan Hu, Yuxi Zheng, *How to Prove Post-Quantum Security for
  Succinct Non-Interactive Reductions*, 2026: Definitions 5.2 and 5.3.
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

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} [DecidableEq ι] [AnswerMeasure spec]
  {S S' T T' P Q : Set (QueryCache spec)} {D : QueryCache spec} {x : spec.Domain} {t t' : ℕ}

/-! ## One-step extension probability -/

/-- The probability that the database `D`, extended at the point `x` by an answer drawn from the
answer measure of `x`, lies in the property `T`. -/
@[expose] noncomputable def extendProb (D : QueryCache spec) (x : spec.Domain)
    (T : Set (QueryCache spec)) : ℝ≥0∞ :=
  Pr{let u ← (query x : OracleComp spec (spec.Range x))}[D.cacheQuery x u ∈ T]

/-- The extension probability is monotone in the target property. -/
lemma extendProb_mono (D : QueryCache spec) (x : spec.Domain) (h : T ⊆ T') :
    D.extendProb x T ≤ D.extendProb x T' :=
  prEvent_mono _ _ _ fun _ hu => h hu

/-- Union bound for the extension probability. -/
lemma extendProb_union_le (D : QueryCache spec) (x : spec.Domain) (T T' : Set (QueryCache spec)) :
    D.extendProb x (T ∪ T') ≤ D.extendProb x T + D.extendProb x T' :=
  prEvent_or_le _ _ _

@[simp]
lemma extendProb_empty (D : QueryCache spec) (x : spec.Domain) : D.extendProb x ∅ = 0 :=
  prEvent_eq_zero_of_forall_not _ _ fun _ h => h

lemma extendProb_le_one (D : QueryCache spec) (x : spec.Domain) (T : Set (QueryCache spec)) :
    D.extendProb x T ≤ 1 :=
  prEvent_le_one _

/-- Under uniform answers, the extension probability is the proportion of answers that land in
the target property. -/
lemma extendProb_eq_card_div {ι : Type u} {spec : OracleSpec.{u, 0} ι} [DecidableEq ι]
    [UniformAnswerMeasure spec] (D : QueryCache spec) (x : spec.Domain)
    [Fintype (spec.Range x)] (T : Set (QueryCache spec))
    [DecidablePred fun u : spec.Range x => D.cacheQuery x u ∈ T] :
    D.extendProb x T =
      ((Finset.univ.filter fun u : spec.Range x => D.cacheQuery x u ∈ T).card : ℝ≥0∞) /
        Fintype.card (spec.Range x) :=
  prEvent_query_eq_card_div x _

/-! ## Flip probability -/

/-- The flip probability from the property `S` to the property `T` with query bound `t`: the
supremum, over databases `D ∈ S` with fewer than `t` entries and points `x` not in `D`, of the
probability that `D` extended at `x` by a sampled answer lies in `T`. It is `0` when there is no
such pair `(D, x)`. -/
@[expose] noncomputable def flip (S T : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  ⨆ (D : QueryCache spec) (_ : D ∈ S) (_ : D.toSet.encard < t) (x : spec.Domain)
    (_ : D x = none), D.extendProb x T

/-- A bound on the flip probability is a bound on every admissible one-step extension. -/
lemma flip_le_iff {c : ℝ≥0∞} :
    flip S T t ≤ c ↔
      ∀ D ∈ S, D.toSet.encard < t → ∀ x, D x = none → D.extendProb x T ≤ c := by
  simp only [flip, iSup_le_iff]

/-- Every admissible one-step extension is bounded by the flip probability. -/
lemma extendProb_le_flip (hD : D ∈ S) (ht : D.toSet.encard < t) (hx : D x = none) :
    D.extendProb x T ≤ flip S T t :=
  flip_le_iff.mp le_rfl D hD ht x hx

/-- The flip probability is monotone in the source property, the target property and the query
bound. -/
theorem flip_mono (hS : S ⊆ S') (hT : T ⊆ T') (ht : t ≤ t') : flip S T t ≤ flip S' T' t' :=
  flip_le_iff.mpr fun D hD hlt x hx => (extendProb_mono D x hT).trans
    (extendProb_le_flip (hS hD) (hlt.trans_le (by exact_mod_cast ht)) hx)

/-- The flip probability out of a union of an indexed family is the supremum of the flip
probabilities out of its members. -/
theorem flip_iUnion_left {κ : Sort*} (S : κ → Set (QueryCache spec)) (T : Set (QueryCache spec))
    (t : ℕ) : flip (⋃ i, S i) T t = ⨆ i, flip (S i) T t := by
  refine le_antisymm (flip_le_iff.mpr fun D hD hlt x hx => ?_)
    (iSup_le fun i => flip_mono (subset_iUnion S i) le_rfl le_rfl)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hD
  exact (extendProb_le_flip hi hlt hx).trans (le_iSup (fun i => flip (S i) T t) i)

/-- The flip probability out of a union is the larger of the two flip probabilities. -/
theorem flip_union_left (S S' T : Set (QueryCache spec)) (t : ℕ) :
    flip (S ∪ S') T t = max (flip S T t) (flip S' T t) := by
  refine le_antisymm (flip_le_iff.mpr ?_)
    (max_le (flip_mono subset_union_left le_rfl le_rfl)
      (flip_mono subset_union_right le_rfl le_rfl))
  rintro D (hD | hD) hlt x hx
  · exact (extendProb_le_flip hD hlt hx).trans (le_max_left _ _)
  · exact (extendProb_le_flip hD hlt hx).trans (le_max_right _ _)

/-- Union bound for the flip probability into a union. -/
theorem flip_union_right_le (S T T' : Set (QueryCache spec)) (t : ℕ) :
    flip S (T ∪ T') t ≤ flip S T t + flip S T' t :=
  flip_le_iff.mpr fun D hD hlt x hx => (extendProb_union_le D x T T').trans
    (add_le_add (extendProb_le_flip hD hlt hx) (extendProb_le_flip hD hlt hx))

@[simp]
theorem flip_empty_left (T : Set (QueryCache spec)) (t : ℕ) : flip ∅ T t = 0 :=
  nonpos_iff_eq_zero.mp (flip_le_iff.mpr fun _ hD => (notMem_empty _ hD).elim)

@[simp]
theorem flip_empty_right (S : Set (QueryCache spec)) (t : ℕ) : flip S ∅ t = 0 :=
  nonpos_iff_eq_zero.mp (flip_le_iff.mpr fun D _ _ x _ => (extendProb_empty D x).le)

/-- With query bound `0` there is no admissible database, so the flip probability is `0`. -/
@[simp]
theorem flip_zero (S T : Set (QueryCache spec)) : flip S T 0 = 0 :=
  nonpos_iff_eq_zero.mp (flip_le_iff.mpr fun _ _ hlt => by simp at hlt)

theorem flip_le_one (S T : Set (QueryCache spec)) (t : ℕ) : flip S T t ≤ 1 :=
  flip_le_iff.mpr fun D _ _ x _ => extendProb_le_one D x T

/-! ## Instability -/

/-- The instability of the property `P` with query bound `t`: the largest probability that one
fresh answer changes whether a database with fewer than `t` entries has the property. -/
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

@[simp]
theorem instability_zero (P : Set (QueryCache spec)) : instability P 0 = 0 := by
  simp [instability]

@[simp]
theorem instability_empty (t : ℕ) : instability (∅ : Set (QueryCache spec)) t = 0 := by
  simp [instability]

@[simp]
theorem instability_univ (t : ℕ) : instability (univ : Set (QueryCache spec)) t = 0 := by
  simp [instability]

theorem instability_le_one (P : Set (QueryCache spec)) (t : ℕ) : instability P t ≤ 1 :=
  max_le (flip_le_one _ _ t) (flip_le_one _ _ t)

/-! ## Conditional instability -/

/-- The flip probability into `P` conditioned on `Q`: source and target are both restricted to
databases in `Q`. -/
@[expose] noncomputable def condFlip (P Q : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  flip (Pᶜ ∩ Q) (P ∩ Q) t

/-- The instability of `P` conditioned on `Q`. -/
@[expose] noncomputable def condInstability (P Q : Set (QueryCache spec)) (t : ℕ) : ℝ≥0∞ :=
  max (condFlip P Q t) (condFlip Pᶜ Q t)

/-- Conditioning lowers the flip probability. -/
theorem condFlip_le_flip (P Q : Set (QueryCache spec)) (t : ℕ) :
    condFlip P Q t ≤ flip Pᶜ P t :=
  flip_mono inter_subset_left inter_subset_left le_rfl

/-- Conditioning lowers instability. -/
theorem condInstability_le_instability (P Q : Set (QueryCache spec)) (t : ℕ) :
    condInstability P Q t ≤ instability P t :=
  max_le_max (condFlip_le_flip P Q t) (by simpa using condFlip_le_flip Pᶜ Q t)

@[simp]
theorem condFlip_univ (P : Set (QueryCache spec)) (t : ℕ) :
    condFlip P univ t = flip Pᶜ P t := by
  simp [condFlip]

/-- Conditioning on the property of all databases gives back the instability. -/
@[simp]
theorem condInstability_univ (P : Set (QueryCache spec)) (t : ℕ) :
    condInstability P univ t = instability P t := by
  simp [condInstability, instability]

/-- Conditional instability is symmetric under complement of the conditioned property. -/
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

/-- The instability of an indexed family of properties with query bound `t`: the largest
probability that one fresh answer moves a database with fewer than `t` entries from one member
of the family into another. The family is a partition in the intended use;
`partitionInstability_eq_iSup_flip_compl` gives the form the definition takes there. -/
@[expose] noncomputable def partitionInstability {κ : Type*} (P : κ → Set (QueryCache spec))
    (t : ℕ) : ℝ≥0∞ :=
  ⨆ i, flip (P i) (⋃ j, ⋃ (_ : j ≠ i), P j) t

/-- Partition instability is monotone in the query bound. -/
theorem partitionInstability_mono_query {κ : Type*} (P : κ → Set (QueryCache spec))
    (h : t ≤ t') : partitionInstability P t ≤ partitionInstability P t' :=
  iSup_mono fun _ => flip_mono le_rfl le_rfl h

theorem partitionInstability_le_one {κ : Type*} (P : κ → Set (QueryCache spec)) (t : ℕ) :
    partitionInstability P t ≤ 1 :=
  iSup_le fun _ => flip_le_one _ _ t

/-- In a partition, the other members together are the complement of a member, so the partition
instability is the largest flip probability from a member to its complement. -/
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

/-- The two-class partition `{P, Pᶜ}` has partition instability `instability P t`. -/
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
