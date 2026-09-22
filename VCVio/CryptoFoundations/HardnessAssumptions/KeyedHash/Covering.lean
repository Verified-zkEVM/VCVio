/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
public import VCVio.OracleComp.QueryTracking.RandomOracle.Tape

/-!
# Interleaved-target coverage of uniform digests

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
and one saturating list buys coverage of every digit at once.  `not_covered_satList_erase`
records that the saturating list is not itself covered, so it is a legitimate state of an
argument that stops at the first covered digest.

## The tuple formulation

`TapeCoveredReuse` states coverage on a *tuple* of `q` independent uniform digests: some
coordinate has each of its `k` digits matched, at its own leaf, by another coordinate.  One
coordinate may cover several digits, which is how an adversary with few logged digests covers a
target, so no distinctness among the coverers is required.  This is where uniformity of the
logged digests is used, and it is the product-style argument the fixed-list formulation cannot
make.

`evalDist_answerTape_tapeCoveredReuse_le` bounds it by a union over the target coordinate and
the coverer assignment, each contributing `(2 ^ h)⁻¹ ^ r * ((2 ^ a)⁻¹) ^ k` where `r` is the
number of *distinct* coverers the assignment uses.  The `r` in the leaf exponent is the whole
content of the accounting: a coordinate covering several digits pays for its leaf once and for
each of those digits, so `evalDist_multiFiber_le` charges `2 ^ (-h - a * m)` for `m` digits and
not `(2 ^ (-h - a)) ^ m`.

A coverer must differ from the target: `tapeCoveredNoFresh_of_pos` shows that without that
requirement every nonempty tuple is covered.

`CacheCovered` states the event on the answer cache of a lazy random oracle, and
`evalDist_run_randomOracle_setOf_cacheCovered_le` transports the tuple bound to a random-oracle
run, through the answer tape of `VCVio.OracleComp.QueryTracking.RandomOracle.Tape`: the tape
identification turns the run into `q` independent uniform answers, and the tape positions of the
cache entries turn a covered cache into a covered tuple.  The bounded event is coverage
*conjoined with* `QueryCache.enncard ≤ q`; the run itself is unconstrained.

## Scope

* The model is abstract.  Nothing here says that the leaf and the digits of a real digest are
  independent and uniform, or even surjective images of it; transporting a byte-level digest
  into `Digest h a k` is the instantiating module's obligation.
* The probabilistic objects are one uniform digest for the fixed-list bounds, where `L` is a
  `Finset` quantified universally, and `q` independent uniform digests for the tuple bounds.  No
  game, key or signature appears: the random-oracle bound quantifies over an arbitrary
  computation `oa` and an arbitrary query domain `D`, and says nothing about what a scheme
  queries or about how a digest reaches the oracle.
* The right-hand side is an advantage at a single query budget `q` serving both roles: the
  target coordinate and the coverers are drawn from the same `q` samples.  Separating the
  target's hash-query budget from the coverers' signature budget, and regrouping the sum by the
  number of distinct coverers, are what turn this into the published per-hash-query form, and
  neither is done here.  The sum ranges over `q ^ (k + 1)` assignments, so as a function of a
  single `q` it degrades accordingly.
* Nothing here is quantum.

## Labels

Twenty-eight declarations.

*The model*: `Digest`, `Covered`.

*The upper bound*: `fiber`, `card_fiber_le`, `encard_covered_le`, `evalDist_covered_le`.

*The matching lower bound*: `satList`, `card_satList_le`, `covered_satList`,
`evalDist_covered_satList_ge`, `evalDist_covered_satList_eq`, `not_covered_satList_erase_coord`,
`not_covered_satList_erase`.

*The per-coordinate cost*: `multiFiber`, `mem_multiFiber`, `card_multiFiber_le`,
`evalDist_multiFiber_le`, `prod_image_mul_pow_card_filter`.

*The tuple bound*: `TapeCoveredReuse`, `TapeCoveredNoFresh`, `tapeCoveredNoFresh_of_pos`,
`roleAssign`, `roleSet`, `image_roleAssign`, `evalDist_answerTape_tapeCoveredReuse_le`.

*The random-oracle run*: `CacheCovered`, `tapeCoveredReuse_of_cacheCovered`,
`evalDist_run_randomOracle_setOf_cacheCovered_le`.

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
    𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))] {z | Covered h a k L z} ≤
      (L.card : ℝ≥0∞) / (2 ^ h * 2 ^ a) := by
  classical
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
    (S.card : ℝ≥0∞) / 2 ^ h ≤
      𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))] {z | Covered h a k (satList h a k S) z} := by
  classical
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
    𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))]
        {z | Covered h a k (satList h a k S) z} = (S.card : ℝ≥0∞) / 2 ^ h := by
  classical
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

/-! ## Coverage of a tuple of independent uniform digests -/

open AnswerTape OracleComp OracleSpec

/-- The digests agreeing with `w` on the leaf and on every digit in `T`. -/
def multiFiber (T : Finset (Fin k)) (w : Digest h a k) : Finset (Digest h a k) :=
  {u | u.1 = w.1 ∧ ∀ i ∈ T, u.2 i = w.2 i}

theorem mem_multiFiber {T : Finset (Fin k)} {w u : Digest h a k} :
    u ∈ multiFiber h a k T w ↔ u.1 = w.1 ∧ ∀ i ∈ T, u.2 i = w.2 i := by
  simp [multiFiber]

/-- Fixing the leaf and the `|T|` digits in `T` leaves at most `(2 ^ a) ^ (k - |T|)` digests. -/
theorem card_multiFiber_le (T : Finset (Fin k)) (w : Digest h a k) :
    (multiFiber h a k T w).card ≤ (2 ^ a) ^ (k - T.card) := by
  classical
  have hcard : Fintype.card ({j : Fin k // j ∉ T} → Fin (2 ^ a)) = (2 ^ a) ^ (k - T.card) := by
    simp [Fintype.card_subtype_compl]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun u => fun j : {j : Fin k // j ∉ T} => u.2 j.1) (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨l₁, f₁⟩ h₁ ⟨l₂, f₂⟩ h₂ heq
  rw [Finset.mem_coe, mem_multiFiber] at h₁ h₂
  have hf : f₁ = f₂ := by
    funext j
    by_cases hj : j ∈ T
    · exact (h₁.2 j hj).trans (h₂.2 j hj).symm
    · exact congrFun heq ⟨j, hj⟩
  simp only [Prod.mk.injEq]
  exact ⟨h₁.1.trans h₂.1.symm, hf⟩

/-- **One coordinate matching `|T|` digits costs `2 ^ (-h - a * |T|)`.**  A uniform digest agrees
with `w` on the leaf and on every digit of `T` with mass at most
`(2 ^ h)⁻¹ * ((2 ^ a)⁻¹) ^ |T|`: the leaf factor is paid once, the digit factor once per digit
of `T`. -/
theorem evalDist_multiFiber_le (T : Finset (Fin k)) (w : Digest h a k) :
    𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))]
        (multiFiber h a k T w : Set (Digest h a k)) ≤
      ((2 : ℝ≥0∞) ^ h)⁻¹ * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ T.card := by
  classical
  have hen : (multiFiber h a k T w : Set (Digest h a k)).encard
      ≤ (((2 ^ a) ^ (k - T.card) : ℕ) : ℕ∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact Nat.cast_le.mpr (card_multiFiber_le h a k T w)
  have hcard : Fintype.card (Digest h a k) = 2 ^ h * (2 ^ a) ^ k := by simp
  refine (SampleableType.evalDist_uniformSample_le_of_encard_le _ _ hen).trans ?_
  rw [hcard]
  have hP : ((2 : ℝ≥0∞) ^ a) ^ (k - T.card) ≠ 0 := by positivity
  have hP' : ((2 : ℝ≥0∞) ^ a) ^ (k - T.card) ≠ ⊤ := by finiteness
  have hnum : (((2 ^ a) ^ (k - T.card) : ℕ) : ℝ≥0∞)
      = 1 * ((2 : ℝ≥0∞) ^ a) ^ (k - T.card) := by push_cast; ring
  have hden : ((2 ^ h * (2 ^ a) ^ k : ℕ) : ℝ≥0∞)
      = ((2 : ℝ≥0∞) ^ h * ((2 : ℝ≥0∞) ^ a) ^ T.card) * ((2 : ℝ≥0∞) ^ a) ^ (k - T.card) := by
    have hk1 : T.card + (k - T.card) = k := by
      have := Finset.card_le_univ T
      simp only [Fintype.card_fin] at this
      omega
    push_cast
    rw [mul_assoc, ← pow_add, hk1]
  rw [hnum, hden, ENNReal.mul_div_mul_right _ _ hP hP', one_div,
    ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
  exact le_of_eq (congrArg _ ENNReal.inv_pow)

/-- **The per-coordinate costs multiply.**  Over the coordinates an assignment `f` uses, the leaf
factor is paid once per coordinate and the digit factor once per digit, so the product of the
per-coordinate costs is `(2 ^ h)⁻¹ ^ r * ((2 ^ a)⁻¹) ^ k` with `r` the number of distinct
coordinates `f` uses. -/
theorem prod_image_mul_pow_card_filter {q : ℕ} (f : Fin k → Fin q) :
    ∏ j ∈ Finset.univ.image f,
        (((2 : ℝ≥0∞) ^ h)⁻¹ *
          (((2 : ℝ≥0∞) ^ a)⁻¹) ^ (Finset.univ.filter (fun i => f i = j)).card)
      = (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image f).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by
  classical
  have hsum : (∑ j ∈ Finset.univ.image f, (Finset.univ.filter (fun i => f i = j)).card) = k := by
    rw [← Finset.card_eq_sum_card_image]
    simp
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, hsum]

/-! ## The coverage event on a tuple -/

/-- **Interleaved-target coverage on a tuple.**  Some coordinate `j₀` has each of its `k` digits
matched, at its own leaf, by some *other* coordinate.  The `k` covering coordinates need not be
distinct from each other: one coordinate may cover several digits, which is what an adversary
with few logged digests does. -/
@[expose] def TapeCoveredReuse (q : ℕ) (v : Fin q → Digest h a k) : Prop :=
  ∃ j₀ : Fin q, ∃ f : Fin k → Fin q, (∀ i, f i ≠ j₀) ∧
    ∀ i, (v (f i)).1 = (v j₀).1 ∧ (v (f i)).2 i = (v j₀).2 i

/-- The same event *without* the requirement that a coverer differ from the target. -/
@[expose] def TapeCoveredNoFresh (q : ℕ) (v : Fin q → Digest h a k) : Prop :=
  ∃ j₀ : Fin q, ∃ f : Fin k → Fin q,
    ∀ i, (v (f i)).1 = (v j₀).1 ∧ (v (f i)).2 i = (v j₀).2 i

/-- **The freshness requirement is load-bearing.**  Without it the event holds for every
nonempty tuple — take the target as its own coverer — so no bound on it can be nontrivial. -/
theorem tapeCoveredNoFresh_of_pos {q : ℕ} (hq : 0 < q) (v : Fin q → Digest h a k) :
    TapeCoveredNoFresh h a k q v :=
  ⟨⟨0, hq⟩, fun _ => ⟨0, hq⟩, fun _ => ⟨rfl, rfl⟩⟩

/-- The `m + 1` coordinates a coverage witness designates: the target first, then the covering
coordinate of each digit. -/
def roleAssign {m q : ℕ} (j₀ : Fin q) (f : Fin m → Fin q) : Fin (m + 1) → Fin q :=
  Fin.cons j₀ f

/-- The `k + 1` coordinate conditions of a coverage witness at a guessed target value `w`: the
target coordinate must be `w`, and the covering coordinate of digit `i` must match `w` on the
leaf and on digit `i`. -/
def roleSet (w : Digest h a k) : Fin (k + 1) → Set (Digest h a k) :=
  Fin.cons {w} (fun i => (multiFiber h a k {i} w : Set (Digest h a k)))

theorem image_roleAssign {m q : ℕ} (j₀ : Fin q) (f : Fin m → Fin q) :
    Finset.univ.image (roleAssign j₀ f) = insert j₀ (Finset.univ.image f) := by
  classical
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact Or.inl (Eq.symm (by simpa [roleAssign] using hi))
    · exact Or.inr ⟨i', by simpa [roleAssign] using hi⟩
  · rintro (rfl | ⟨i, hi⟩)
    · exact ⟨0, by simp [roleAssign]⟩
    · exact ⟨i.succ, by simpa [roleAssign] using hi⟩

/-- **The coverage bound on a tuple of independent uniform digests.**  The mass of the event is
at most the sum, over the target coordinate and the coverer assignment, of
`(2 ^ h)⁻¹ ^ r * ((2 ^ a)⁻¹) ^ k`, where `r` is the number of *distinct* coverers the assignment
uses: the leaf factor is paid once per coverer, the digit factor once per digit. -/
theorem evalDist_answerTape_tapeCoveredReuse_le (q : ℕ) :
    𝒟[answerTape (Digest h a k) q] {v | TapeCoveredReuse h a k q v} ≤
      ∑ c ∈ Finset.univ.filter (fun c : Fin q × (Fin k → Fin q) => ∀ i, c.2 i ≠ c.1),
        (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.2).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by
  classical
  have hN0 : (Fintype.card (Digest h a k) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hNt : (Fintype.card (Digest h a k) : ℝ≥0∞) ≠ ⊤ := by finiteness
  refine (evalDist_answerTape_le_sum_of_subset_biUnion
    ((Finset.univ.filter (fun c : Fin q × (Fin k → Fin q) => ∀ i, c.2 i ≠ c.1)) ×ˢ
      (Finset.univ : Finset (Digest h a k)))
    {v | TapeCoveredReuse h a k q v}
    (fun c => {v | ∀ i, v (roleAssign c.1.1 c.1.2 i) ∈ roleSet h a k c.2 i})
    (fun c => (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹ *
      ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.1.2).card *
        (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k)) ?_ ?_).trans ?_
  · rintro v ⟨j₀, f, hne, hcov⟩
    refine Set.mem_biUnion (x := ((j₀, f), v j₀))
      (Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, Finset.mem_univ _⟩)) fun i => ?_
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · simp [roleAssign, roleSet]
    · simp only [roleAssign, Fin.cons_succ, roleSet]
      rw [Finset.mem_coe, mem_multiFiber]
      refine ⟨(hcov i').1, fun i'' hi'' => ?_⟩
      rw [Finset.mem_singleton] at hi''
      rw [hi'']
      exact (hcov i').2
  · rintro ⟨⟨j₀, f⟩, w⟩ hc
    have hne : ∀ i, f i ≠ j₀ := (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).2
    have hj₀ : j₀ ∉ Finset.univ.image f := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun i hi => hne i hi
    set δ : Fin q → ℝ≥0∞ := fun j =>
      if j = j₀ then (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹
      else ((2 : ℝ≥0∞) ^ h)⁻¹ *
        (((2 : ℝ≥0∞) ^ a)⁻¹) ^ (Finset.univ.filter (fun i => f i = j)).card with hδdef
    have hδ0 : δ j₀ = (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹ := by simp [hδdef]
    have hδn : ∀ j, j ≠ j₀ → δ j = ((2 : ℝ≥0∞) ^ h)⁻¹ *
        (((2 : ℝ≥0∞) ^ a)⁻¹) ^ (Finset.univ.filter (fun i => f i = j)).card :=
      fun j hj => by simp [hδdef, hj]
    have hδ : ∀ j ∈ Finset.univ.image (roleAssign j₀ f),
        𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))]
          (piOfAssign (roleAssign j₀ f) (roleSet h a k w) j) ≤ δ j := by
      intro j hj
      by_cases hjj : j = j₀
      · have hsub : piOfAssign (roleAssign j₀ f) (roleSet h a k w) j ⊆ {w} := fun u hu => by
          simpa [roleSet] using mem_piOfAssign.mp hu 0 (by simp [roleAssign, hjj])
        refine (measure_mono hsub).trans (le_of_eq ?_)
        rw [SampleableType.evalDist_uniformSample_singleton (α := Digest h a k) w, hjj, hδ0]
      · have hjf : j ∈ Finset.univ.image f := by
          rw [image_roleAssign] at hj
          exact (Finset.mem_insert.mp hj).resolve_left hjj
        obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hjf
        have hall : ∀ i : Fin k, f i = j →
            ∀ u : Digest h a k, u ∈ piOfAssign (roleAssign j₀ f) (roleSet h a k w) j →
              u ∈ (multiFiber h a k {i} w : Set (Digest h a k)) := fun i hi u hu => by
          simpa [roleSet] using mem_piOfAssign.mp hu i.succ (by simp [roleAssign, hi])
        have hsub : piOfAssign (roleAssign j₀ f) (roleSet h a k w) j ⊆
            (multiFiber h a k (Finset.univ.filter (fun i => f i = j)) w :
              Set (Digest h a k)) := by
          intro u hu
          rw [Finset.mem_coe, mem_multiFiber]
          refine ⟨((mem_multiFiber h a k).mp (hall i₀ hi₀ u hu)).1, fun i hi => ?_⟩
          rw [Finset.mem_filter] at hi
          exact ((mem_multiFiber h a k).mp (hall i hi.2 u hu)).2 i (Finset.mem_singleton_self i)
        refine (measure_mono hsub).trans ?_
        rw [hδn j hjj]
        exact evalDist_multiFiber_le h a k _ w
    refine (evalDist_answerTape_setOf_forall_mem_le_prod_image (roleAssign j₀ f)
      (roleSet h a k w) δ hδ).trans ?_
    rw [image_roleAssign, Finset.prod_insert hj₀, hδ0,
      Finset.prod_congr rfl (fun j hj => hδn j (fun hjj => hj₀ (hjj ▸ hj))),
      prod_image_mul_pow_card_filter h a k f]
  · rw [Finset.sum_product]
    refine le_of_eq (Finset.sum_congr rfl fun c _ => ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hN0 hNt, one_mul]

/-! ## Coverage of a random-oracle answer cache -/

/-- **Interleaved-target coverage inside an answer cache.**  Some cached query's digest has each
of its `k` digits matched, at its own leaf, by the digest of another cached query.  As in
`TapeCoveredReuse`, one cached query may cover several digits. -/
@[expose] def CacheCovered {D : Type} (c : (D →ₒ Digest h a k).QueryCache) : Prop :=
  ∃ t₀ : D, ∃ f : Fin k → D, (∀ i, f i ≠ t₀) ∧
    ∃ z₀, c t₀ = some z₀ ∧ ∀ i, ∃ z, c (f i) = some z ∧ z.1 = z₀.1 ∧ z.2 i = z₀.2 i

/-- **Cache coverage transports to tuple coverage.**  Given for each cache entry a coordinate of
`v` holding its value, with distinct entries at distinct coordinates, a covered cache exhibits a
covered tuple.  Coordinate distinctness is what carries the freshness of a coverer across; the
coverers themselves are not required to be distinct on either side. -/
theorem tapeCoveredReuse_of_cacheCovered {D : Type} {q : ℕ} {v : Fin q → Digest h a k}
    {c : (D →ₒ Digest h a k).QueryCache} (pos : D → Option (Fin q))
    (hval : ∀ t u, c t = some u → ∃ i, pos t = some i ∧ u = v i)
    (hinj : ∀ t t' i, pos t = some i → pos t' = some i → t = t')
    (hc : CacheCovered h a k c) : TapeCoveredReuse h a k q v := by
  obtain ⟨t₀, f, hfne, z₀, hz₀, hcov⟩ := hc
  obtain ⟨i₀, hi₀, hv₀⟩ := hval t₀ z₀ hz₀
  have hstep : ∀ i, ∃ j : Fin q, pos (f i) = some j ∧
      (v j).1 = (v i₀).1 ∧ (v j).2 i = (v i₀).2 i := by
    intro i
    obtain ⟨z, hz, h₁, h₂⟩ := hcov i
    obtain ⟨j, hj, hvj⟩ := hval (f i) z hz
    exact ⟨j, hj, by rw [← hvj, ← hv₀]; exact h₁, by rw [← hvj, ← hv₀]; exact h₂⟩
  choose j hj hj₁ hj₂ using hstep
  exact ⟨i₀, j, fun i hji => hfne i (hinj (f i) t₀ (j i) (hj i) (by rw [hji]; exact hi₀)),
    fun i => ⟨hj₁ i, hj₂ i⟩⟩

/-- **The interleaved-target coverage bound for a lazy random-oracle run.**  Running `oa` under
the lazy random oracle from the empty cache leaves a covered cache holding at most `q` entries
with mass at most the tuple bound of `evalDist_answerTape_tapeCoveredReuse_le`.

The cache bound `QueryCache.enncard ≤ q` is part of the event rather than a hypothesis, which is
how a caller with a query bound uses it.  No distinctness of the coverers is assumed: the bound
is for interleaved-target coverage as an adversary with `q` logged digests can achieve it. -/
theorem evalDist_run_randomOracle_setOf_cacheCovered_le {D : Type} [DecidableEq D] {α : Type}
    (q : ℕ) (oa : OracleComp (D →ₒ Digest h a k) α) :
    letI : MeasurableSpace (α × (D →ₒ Digest h a k).QueryCache) := ⊤
    𝒟[(simulateQ (OracleSpec.randomOracle (spec := (D →ₒ Digest h a k))) oa).run ∅]
        {z | CacheCovered h a k z.2 ∧ z.2.enncard ≤ (q : ℝ≥0∞)} ≤
      ∑ c ∈ Finset.univ.filter (fun c : Fin q × (Fin k → Fin q) => ∀ i, c.2 i ≠ c.1),
        (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.2).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by
  classical
  refine evalDist_run_randomOracle_setOf_le_of_transport q oa
    (fun c => CacheCovered h a k c ∧ c.enncard ≤ (q : ℝ≥0∞))
    {v | TapeCoveredReuse h a k q v} _
    (evalDist_answerTape_tapeCoveredReuse_le h a k q) fun v hv z hz hP => hv ?_
  obtain ⟨pos, hval, hposinj⟩ := exists_pos_of_mem_support_run_tapeCachingImpl v oa hz hP.2
  exact tapeCoveredReuse_of_cacheCovered h a k pos hval hposinj hP.1

end KeyedHash.Covering
