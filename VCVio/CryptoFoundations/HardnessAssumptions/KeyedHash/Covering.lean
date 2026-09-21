/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Interleaved-target coverage of a uniform digest by a fixed list

The combinatorial model behind the interleaved-target hop of a hash-based signature scheme.  A
digest is a *leaf* together with one *digit* per index: `Digest h a k = Fin (2 ^ h) × (Fin k →
Fin (2 ^ a))`.  `Covered L z` says that each of `z`'s `k` digits is matched by some digest of the
list `L` that also shares `z`'s leaf — the subset relation of interleaved target subset
resilience, with the leaf standing for the hypertree position and the digits for the per-tree
leaf indices.

Against a *fixed* list `L` a uniform digest is covered with mass at most
`|L| / (2 ^ h * 2 ^ a)` (`evalDist_covered_le`): only one of the `k` digits is used, and fixing
the leaf and one digit leaves a `(2 ^ a) ^ (k - 1)` fibre of the `2 ^ h * (2 ^ a) ^ k` digests.

**The two bounds coincide at the saturating list.**  `evalDist_covered_satList_eq` computes, for
every set `S` of leaves, the mass at the list of `|S| * 2 ^ a` digests that covers *every* digest
at a leaf of `S`: it is exactly `|S| / 2 ^ h`, the value the upper bound takes there.  So
`|L| / (2 ^ h * 2 ^ a)` is attained at those list sizes — the multiples of `2 ^ a`, which is what
a witness respecting a budget `q` uses, `⌊q / 2 ^ a⌋ * 2 ^ a` entries — and the loss of the
fixed-list formulation is its exact worst case, not slack in the counting: such a list really can
make a `⌊q / 2 ^ a⌋ / 2 ^ h` fraction of all digests covered.  At a size that is not a multiple
of `2 ^ a` the bound need not be attained.

**Consequently the fixed-list formulation alone yields no useful figure.**  The small numbers
associated with this hop are numbers about *uniform* logged digests, where covering all `k`
digits costs a product of `k` independent events; here the list is arbitrary, hence adversarial,
and one saturating list buys coverage of every digit at once.  Turning uniformity of the logged
digests into a bound needs a product-style argument over a tuple of fresh answers, which is not
in this library.  `not_covered_satList_erase` records that the saturating list is not itself
covered, so it is a legitimate state of an argument that stops at the first covered digest.

## Scope

* The model is abstract.  Nothing here says that the leaf and the digits of a real digest are
  independent and uniform, or even surjective images of it; transporting a byte-level digest
  into `Digest h a k` is the instantiating module's obligation.
* No adversary, oracle or game appears.  `L` is a `Finset`, quantified universally, and the only
  probabilistic object is one uniform sample.
* Nothing is proved about a *tuple* of digests, which is what a product-style argument needs.
* Nothing here is quantum.

## Labels

Thirteen declarations.

*The model*: `Digest`, `Covered`.

*The upper bound*: `fiber`, `card_fiber_le`, `encard_covered_le`, `evalDist_covered_le`.

*The matching lower bound*: `satList`, `card_satList_le`, `covered_satList`,
`evalDist_covered_satList_ge`, `evalDist_covered_satList_eq`, `not_covered_satList_erase_coord`,
`not_covered_satList_erase`.

## References

* Hülsing and Kudinov, "Recovering the Tight Security Proof of SPHINCS+", the interleaved
  target subset resilience bound.
-/

public section

namespace KeyedHash.Covering

open MeasureTheory
open scoped ENNReal

variable (h a k : ℕ)

/-! ## The model -/

/-- A digest: a leaf among `2 ^ h`, together with one digit among `2 ^ a` for each of `k`
indices. -/
abbrev Digest := Fin (2 ^ h) × (Fin k → Fin (2 ^ a))

/-- **Interleaved-target coverage.**  Every digit of `z` is matched by some digest of `L` at the
same leaf. -/
def Covered (L : Finset (Digest h a k)) (z : Digest h a k) : Prop :=
  ∀ i : Fin k, ∃ d ∈ L, d.1 = z.1 ∧ d.2 i = z.2 i

/-! ## The upper bound -/

/-- The digests agreeing with `d` on the leaf and on digit `i₀`. -/
def fiber (i₀ : Fin k) (d : Digest h a k) : Finset (Digest h a k) :=
  {z | z.1 = d.1 ∧ z.2 i₀ = d.2 i₀}

/-- Fixing the leaf and one digit leaves at most `(2 ^ a) ^ (k - 1)` digests. -/
theorem card_fiber_le (i₀ : Fin k) (d : Digest h a k) :
    (fiber h a k i₀ d).card ≤ (2 ^ a) ^ (k - 1) := by
  classical
  have hcard : Fintype.card ({j : Fin k // j ≠ i₀} → Fin (2 ^ a)) = (2 ^ a) ^ (k - 1) := by
    simp [Fintype.card_subtype_compl]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun z => fun j : {j : Fin k // j ≠ i₀} => z.2 j.1) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨l1, f1⟩ h1 ⟨l2, f2⟩ h2 heq
  simp only [fiber, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at h1 h2
  obtain ⟨hl1, hf1⟩ := h1
  obtain ⟨hl2, hf2⟩ := h2
  have hf : f1 = f2 := by
    funext j
    by_cases hj : j = i₀
    · subst hj; exact hf1.trans hf2.symm
    · exact congrFun heq ⟨j, hj⟩
  simp only [Prod.mk.injEq]
  exact ⟨hl1.trans hl2.symm, hf⟩

/-- **The covering set is small.**  Against a fixed list `L`, at most `|L| * (2 ^ a) ^ (k - 1)`
of the `2 ^ h * (2 ^ a) ^ k` digests have all `k` digits covered. -/
theorem encard_covered_le (hk : 0 < k) (L : Finset (Digest h a k)) :
    {z | Covered h a k L z}.encard ≤ ((L.card * (2 ^ a) ^ (k - 1) : ℕ) : ℕ∞) := by
  classical
  have hsub : {z | Covered h a k L z} ⊆ (L.biUnion (fiber h a k ⟨0, hk⟩) : Finset _) := by
    intro z hz
    obtain ⟨d, hd, h1, h2⟩ := hz ⟨0, hk⟩
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨d, hd, by simp [fiber, h1.symm, h2.symm]⟩)
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard]
  refine Nat.cast_le.mpr ((Finset.card_biUnion_le).trans ?_)
  calc ∑ d ∈ L, (fiber h a k ⟨0, hk⟩ d).card
      ≤ ∑ _d ∈ L, (2 ^ a) ^ (k - 1) :=
        Finset.sum_le_sum fun d _ => card_fiber_le h a k ⟨0, hk⟩ d
    _ = L.card * (2 ^ a) ^ (k - 1) := by simp [mul_comm]

/-- **The covering probability against a fixed list.**  A uniform digest has all `k` digits
covered by a fixed list `L` with probability at most `|L| / (2 ^ h * 2 ^ a)`. -/
theorem evalDist_covered_le (hk : 0 < k) (L : Finset (Digest h a k)) :
    letI : MeasurableSpace (Digest h a k) := ⊤
    𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))] {z | Covered h a k L z} ≤
      (L.card : ℝ≥0∞) / (2 ^ h * 2 ^ a) := by
  classical
  let _ : MeasurableSpace (Digest h a k) := ⊤
  have hcard : Fintype.card (Digest h a k) = 2 ^ h * (2 ^ a) ^ k := by simp
  refine (SampleableType.evalDist_uniformSample_le_of_encard_le _ _
    (encard_covered_le h a k hk L)).trans ?_
  rw [hcard]
  have hP : ((2 : ℝ≥0∞) ^ a) ^ (k - 1) ≠ 0 := by positivity
  have hP' : ((2 : ℝ≥0∞) ^ a) ^ (k - 1) ≠ ⊤ := by finiteness
  have hnum : ((L.card * (2 ^ a) ^ (k - 1) : ℕ) : ℝ≥0∞)
      = (L.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ a) ^ (k - 1) := by push_cast; ring
  have hden : ((2 ^ h * (2 ^ a) ^ k : ℕ) : ℝ≥0∞)
      = ((2 : ℝ≥0∞) ^ h * 2 ^ a) * ((2 : ℝ≥0∞) ^ a) ^ (k - 1) := by
    have hk1 : k - 1 + 1 = k := by omega
    push_cast
    rw [mul_assoc, mul_comm ((2 : ℝ≥0∞) ^ a) _, ← pow_succ, hk1]
  rw [hnum, hden, ENNReal.mul_div_mul_right _ _ hP hP']

/-! ## The matching lower bound -/

/-- **The saturating list.**  For each leaf in `S` and each digit value, the digest all of whose
digits are that value.  It has at most `|S| * 2 ^ a` entries and covers every digest at a leaf of
`S`. -/
def satList (S : Finset (Fin (2 ^ h))) : Finset (Digest h a k) :=
  (S ×ˢ (Finset.univ : Finset (Fin (2 ^ a)))).image (fun p => (p.1, fun _ => p.2))

/-- The saturating list has at most `|S| * 2 ^ a` entries. -/
theorem card_satList_le (S : Finset (Fin (2 ^ h))) :
    (satList h a k S).card ≤ S.card * 2 ^ a :=
  (Finset.card_image_le).trans (by simp)

/-- **Saturation.**  Every digest at a leaf of `S` is fully covered by `satList S`. -/
theorem covered_satList {S : Finset (Fin (2 ^ h))} {z : Digest h a k} (hz : z.1 ∈ S) :
    Covered h a k (satList h a k S) z := fun i =>
  ⟨(z.1, fun _ => z.2 i), Finset.mem_image.mpr ⟨(z.1, z.2 i), by simp [hz], rfl⟩, rfl, rfl⟩

/-- **The upper bound is attained at the saturating list.**  With the `|S| * 2 ^ a` digests of
`satList S` the covering probability is at least `|S| / 2 ^ h`, the value `|L| / (2 ^ h * 2 ^ a)`
takes there, so no smaller multiple of `|L|` bounds the covering probability uniformly over the
lists whose size is a multiple of `2 ^ a`. -/
theorem evalDist_covered_satList_ge (S : Finset (Fin (2 ^ h))) :
    letI : MeasurableSpace (Digest h a k) := ⊤
    (S.card : ℝ≥0∞) / 2 ^ h ≤
      𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))] {z | Covered h a k (satList h a k S) z} := by
  classical
  let _ : MeasurableSpace (Digest h a k) := ⊤
  have hsub :
      ((S ×ˢ (Finset.univ : Finset (Fin k → Fin (2 ^ a))) : Finset (Digest h a k)) : Set _) ⊆
        {z | Covered h a k (satList h a k S) z} := fun z hz =>
    covered_satList h a k (by simpa using hz)
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [SampleableType.evalDist_uniformSample_eq_encard_div, Set.encard_coe_eq_coe_finsetCard]
  have hcard : Fintype.card (Digest h a k) = 2 ^ h * (2 ^ a) ^ k := by simp
  have hpk : ((2 : ℝ≥0∞) ^ a) ^ k ≠ 0 := by positivity
  have hpk' : ((2 : ℝ≥0∞) ^ a) ^ k ≠ ⊤ := by finiteness
  rw [hcard, Finset.card_product, show (Finset.univ : Finset (Fin k → Fin (2 ^ a))).card
    = (2 ^ a) ^ k from by simp]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ hpk hpk']

/-- **The mass at the saturating list.**  The `|S| * 2 ^ a` digests of `satList S` leave exactly
a `|S| / 2 ^ h` fraction of the digests covered. -/
theorem evalDist_covered_satList_eq (hk : 0 < k) (S : Finset (Fin (2 ^ h))) :
    letI : MeasurableSpace (Digest h a k) := ⊤
    𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))]
        {z | Covered h a k (satList h a k S) z} = (S.card : ℝ≥0∞) / 2 ^ h := by
  classical
  let _ : MeasurableSpace (Digest h a k) := ⊤
  refine le_antisymm ((evalDist_covered_le h a k hk _).trans ?_)
    (evalDist_covered_satList_ge h a k S)
  have h1 : ((satList h a k S).card : ℝ≥0∞) ≤ (S.card : ℝ≥0∞) * 2 ^ a := by
    have := (Nat.cast_le (α := ℝ≥0∞)).mpr (card_satList_le h a k S)
    rw [Nat.cast_mul] at this
    simpa using this
  have h2 : ((2 : ℝ≥0∞) ^ a) ≠ 0 := by positivity
  have h3 : ((2 : ℝ≥0∞) ^ a) ≠ ⊤ := by finiteness
  calc ((satList h a k S).card : ℝ≥0∞) / (2 ^ h * 2 ^ a)
      ≤ ((S.card : ℝ≥0∞) * 2 ^ a) / (2 ^ h * 2 ^ a) := by gcongr
    _ = (S.card : ℝ≥0∞) / 2 ^ h := ENNReal.mul_div_mul_right _ _ h2 h3

/-- **The saturating list does not cover itself.**  No entry of `satList S` has even one digit
matched by another entry of the list at the same leaf. -/
theorem not_covered_satList_erase_coord {S : Finset (Fin (2 ^ h))} {d : Digest h a k}
    (hd : d ∈ satList h a k S) (i : Fin k) :
    ¬ ∃ d' ∈ (satList h a k S).erase d, d'.1 = d.1 ∧ d'.2 i = d.2 i := by
  classical
  rintro ⟨d', hd', h1, h2⟩
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hd')
  obtain ⟨p0, -, hp0⟩ := Finset.mem_image.mp hd
  have hdd : d' = d := by
    subst hp
    subst hp0
    simp only [Prod.mk.injEq] at h1 h2 ⊢
    exact ⟨h1, funext fun _ => h2⟩
  exact Finset.notMem_erase d _ (hdd ▸ hd')

/-- No entry of `satList S` is covered by the other entries of the list. -/
theorem not_covered_satList_erase (hk : 0 < k) {S : Finset (Fin (2 ^ h))} {d : Digest h a k}
    (hd : d ∈ satList h a k S) :
    ¬ Covered h a k ((satList h a k S).erase d) d :=
  fun hcov => not_covered_satList_erase_coord h a k hd ⟨0, hk⟩ (hcov ⟨0, hk⟩)

end KeyedHash.Covering
