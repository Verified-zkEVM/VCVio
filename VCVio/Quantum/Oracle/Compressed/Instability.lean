/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.OracleComp.QueryTracking.Instability.Basic
public import VCVio.Quantum.Oracle.Compressed.Basic

/-!
# Instability of a labelling of databases

Chiesa, Di, Hu and Zheng (*How to Prove Post-Quantum Security for Succinct Non-Interactive
Reductions*, ePrint 2025/2166, Definition 5.3) measure how far one fresh answer can move a
database across a partition `P = {P^(i)}` of the databases:
`I(P, t) = max_i max_{D ∈ P^(i), |D| < t, x ∉ supp D} Pr_u [D[x ↦ u] ∉ P^(i)]`, with `u`
uniform in `Y`.

A partition of the databases is given here by a labelling `π : Database X Y → ι`, the class of
`D` being `π D`. `Quantum.Database.instability π t` is VCVio's partition instability
`OracleSpec.QueryCache.partitionInstability` of the classical lazy random oracle, transported
along `Quantum.Database.equivQueryCache`; the flip probability is not redefined. Its conventions
are those of Definition 5.3: the database has fewer than `t` entries, the point `x` is outside its
support, and the value is `0` when no such pair `(D, x)` exists (an empty supremum in `ℝ≥0∞`).
`Quantum.Database.instability_eq_iSup` spells the definition out for uniform answers, and
`Quantum.Database.card_div_le_instability` is the form in which the commutator bounds use it.

The partition instability is stated for `X Y : Type` because VCVio's query caches are.

## Main definitions

* `Quantum.Database.labelPartition π`: the family of sets of query caches cut out by `π`.
* `Quantum.Database.instability π t`: Definition 5.3 of ePrint 2025/2166.

## Main results

* `Quantum.Database.encard_toSet_equivQueryCache`: the number of entries of a query cache is the
  size of the database.
* `Quantum.Database.instability_eq_iSup`: the instability as a supremum of proportions of answers.
* `Quantum.Database.card_div_le_instability`: every admissible extension is bounded by the
  instability.
* `Quantum.Database.instability_const`, `Quantum.Database.instability_zero`: a constant labelling
  and the query bound `0` give instability `0`.
-/

public section

open OracleSpec ENNReal

namespace Quantum.Database

variable {X Y : Type} {ι : Type*}

/-! ## Databases and query caches -/

/-- The family of sets of query caches cut out by a labelling of databases: the member at `i` is
the set of caches whose database has label `i`. -/
@[expose]
def labelPartition (π : Database X Y → ι) (i : ι) : Set (QueryCache (X →ₒ Y)) :=
  equivQueryCache.symm ⁻¹' (π ⁻¹' {i})

@[simp]
theorem mem_labelPartition {π : Database X Y → ι} {i : ι} {c : QueryCache (X →ₒ Y)} :
    c ∈ labelPartition π i ↔ π (equivQueryCache.symm c) = i :=
  Iff.rfl

/-- The members of the family cut out by a labelling are pairwise disjoint. -/
theorem pairwise_disjoint_labelPartition (π : Database X Y → ι) :
    Pairwise (Function.onFun Disjoint (labelPartition π)) :=
  fun _ _ hij ↦ Set.disjoint_left.mpr fun _ hi hj ↦ hij (hi.symm.trans hj)

/-- The family cut out by a labelling covers every query cache. -/
theorem iUnion_labelPartition (π : Database X Y → ι) : ⋃ i, labelPartition π i = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ Set.mem_iUnion.mpr ⟨_, rfl⟩

/-- The query cache of a database has as many entries as the database has nonempty cells. -/
theorem encard_toSet_equivQueryCache [Fintype X] (D : Database X Y) :
    (equivQueryCache D).toSet.encard = D.size := by
  have hinj : Set.InjOn Sigma.fst (equivQueryCache D).toSet := by
    rintro ⟨x, u⟩ hu ⟨x', u'⟩ hu' (h : x = x')
    subst h
    rw [QueryCache.mem_toSet, equivQueryCache_apply] at hu hu'
    rw [hu] at hu'
    cases Option.some_injective _ hu'
    rfl
  have himage : Sigma.fst '' (equivQueryCache D).toSet =
      ↑(Finset.univ.filter fun x ↦ (D x).isSome) := by
    ext x
    simp only [Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨x', u⟩, hu, rfl⟩
      rw [QueryCache.mem_toSet, equivQueryCache_apply] at hu
      simp [hu]
    · intro hx
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨⟨x, u⟩, by rw [QueryCache.mem_toSet, equivQueryCache_apply]; exact hu, rfl⟩
  rw [← hinj.encard_image, himage, Set.encard_coe_eq_coe_finsetCard]
  rfl

variable [DecidableEq X]

/-- Recording the answer `u` at `x` in the query cache of `D` gives the query cache of
`D[x ↦ u]`. -/
@[simp]
theorem equivQueryCache_symm_cacheQuery (D : Database X Y) (x : X) (u : Y) :
    equivQueryCache.symm ((equivQueryCache D).cacheQuery x u) = Function.update D x (some u) :=
  rfl

/-! ## Instability -/

/-- **Definition 5.3 of ePrint 2025/2166.** The instability of the labelling `π` of databases with
query bound `t`: the largest probability that recording one fresh answer moves a database with
fewer than `t` entries out of its class. It is the partition instability of the classical lazy
random oracle, for the family cut out by `π`. -/
@[expose]
noncomputable def instability [AnswerMeasure (X →ₒ Y)] (π : Database X Y → ι) (t : ℕ) : ℝ≥0∞ :=
  QueryCache.partitionInstability (labelPartition π) t

section instability

variable [AnswerMeasure (X →ₒ Y)]

theorem instability_le_one (π : Database X Y → ι) (t : ℕ) : instability π t ≤ 1 :=
  QueryCache.partitionInstability_le_one _ t

theorem instability_ne_top (π : Database X Y → ι) (t : ℕ) : instability π t ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (instability_le_one π t)

/-- The instability is the largest flip probability from a class to its complement. -/
theorem instability_eq_iSup_flip_compl (π : Database X Y → ι) (t : ℕ) :
    instability π t = ⨆ i, QueryCache.flip (labelPartition π i) (labelPartition π i)ᶜ t :=
  QueryCache.partitionInstability_eq_iSup_flip_compl (pairwise_disjoint_labelPartition π)
    (iUnion_labelPartition π) t

/-- The instability is monotone in the query bound. -/
theorem instability_mono {π : Database X Y → ι} {t t' : ℕ} (h : t ≤ t') :
    instability π t ≤ instability π t' :=
  QueryCache.partitionInstability_mono_query _ h

/-- With query bound `0` there is no admissible database, and the instability is `0`. -/
@[simp]
theorem instability_zero (π : Database X Y → ι) : instability π 0 = 0 := by
  rw [instability_eq_iSup_flip_compl]
  simp [QueryCache.flip_zero]

/-- A constant labelling has instability `0`: no answer leaves the only class. -/
@[simp]
theorem instability_const (i₀ : ι) (t : ℕ) : instability (fun _ : Database X Y ↦ i₀) t = 0 := by
  rw [instability_eq_iSup_flip_compl]
  refine ENNReal.iSup_eq_zero.mpr fun i ↦ ?_
  by_cases h : i₀ = i
  · subst h
    have : (labelPartition (fun _ : Database X Y ↦ i₀) i₀)ᶜ = ∅ := by
      ext c
      simp
    rw [this, QueryCache.flip_empty_right]
  · have : labelPartition (fun _ : Database X Y ↦ i₀) i = ∅ := by
      ext c
      simp [h]
    rw [this, QueryCache.flip_empty_left]

end instability

section uniform

variable [Fintype X] [Fintype Y] [DecidableEq ι] [UniformAnswerMeasure (X →ₒ Y)]

/-- **Definition 5.3 of ePrint 2025/2166, spelled out.** For uniform answers, the instability is
the supremum, over labels `i`, databases `D` of label `i` with fewer than `t` nonempty cells, and
empty cells `x` of `D`, of the proportion of answers `u` with `π D[x ↦ u] ≠ i`. -/
theorem instability_eq_iSup (π : Database X Y → ι) (t : ℕ) :
    instability π t =
      ⨆ (i : ι) (D : Database X Y) (_ : π D = i) (_ : D.size < t) (x : X) (_ : D x = none),
        ((Finset.univ.filter fun u : Y ↦ π (Function.update D x (some u)) ≠ i).card : ℝ≥0∞) /
          Fintype.card Y := by
  classical
  rw [instability_eq_iSup_flip_compl]
  refine iSup_congr fun i ↦ ?_
  rw [QueryCache.flip, ← equivQueryCache.iSup_comp]
  refine iSup_congr fun D ↦ ?_
  refine iSup_congr_Prop (by simp) fun _ ↦ ?_
  refine iSup_congr_Prop (by rw [encard_toSet_equivQueryCache]; exact Nat.cast_lt) fun _ ↦ ?_
  refine iSup_congr fun x ↦ iSup_congr_Prop Iff.rfl fun _ ↦ ?_
  rw [QueryCache.extendProb_eq_card_div]
  refine congrArg (· / _) (congrArg Nat.cast (congrArg Finset.card (Finset.ext fun u ↦ ?_)))
  simp

/-- **Every admissible extension is bounded by the instability.** For a database `D` with fewer
than `t` nonempty cells and an empty cell `x`, the proportion of answers `u` that change the label
of `D[x ↦ u]` is at most the instability. -/
theorem card_div_le_instability (π : Database X Y → ι) {t : ℕ} {D : Database X Y} {x : X}
    (hD : D.size < t) (hx : D x = none) :
    ((Finset.univ.filter fun u : Y ↦ π (Function.update D x (some u)) ≠ π D).card : ℝ) /
        Fintype.card Y ≤ (instability π t).toReal := by
  have h : ((Finset.univ.filter fun u : Y ↦ π (Function.update D x (some u)) ≠ π D).card :
      ℝ≥0∞) / Fintype.card Y ≤ instability π t := by
    rw [instability_eq_iSup]
    exact le_iSup_of_le (π D) <| le_iSup_of_le D <| le_iSup_of_le rfl <| le_iSup_of_le hD <|
      le_iSup_of_le x <| le_iSup_of_le hx le_rfl
  have h' := ENNReal.toReal_mono (instability_ne_top π t) h
  rwa [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at h'

end uniform

end Quantum.Database
