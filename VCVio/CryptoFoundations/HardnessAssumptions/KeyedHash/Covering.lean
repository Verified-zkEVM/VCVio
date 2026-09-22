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

## Separating the two roles

`TapeCoveredSplit` places the target and the coverers in two *disjoint* families of positions, of
sizes `qh` and `qs`, inside the same tuple, and `evalDist_answerTape_tapeCoveredSplit_le` bounds
it by a union over `qh * qs ^ k` witnesses rather than over `q ^ (k + 1)` of them.  No freshness
filter survives the separation: disjointness of the families makes every witness fresh, so the
sum is over a whole product type.  `evalDist_answerTape_tapeCoveredSplit_le_closedForm` evaluates
that sum, as `∑ r ≤ k, qh * C(qs, r) * #{surjections Fin k → Fin r} * 2 ^ (-h * r - a * k)`, by
counting the assignments with `r` distinct coverers (`card_filter_card_image_eq_split`).  This is
the shape of the published interleaved-target bound: the coverer multiplicity is drawn from the
coverer budget and the target from its own.

**The obligation the separation carries.**  Confining the coverers to their own family is sound
only if every position a coverer may occupy is one at which a digest was really signed; otherwise
the separated budget is not a budget at all.  That obligation has a cardinality part and a
positional part, and only the first is met anywhere.  The cardinality part — that a run makes no
more signing queries than hash queries, so a coverer family of size `qs` fits within a hash
budget — is what `HashSig.SLHDSA.Security.JointRom.hasSignQueryBound_of_hasHashQueryBound`
supplies, as an implication between query counts.  The positional part — exhibiting the tape
positions of the signing queries, and a coverer family confined to them and disjoint from the
target's — is a statement about positions rather than counts, and no declaration in this
repository proves it.  Nothing in this module carries out the instantiation, and nothing here
identifies either family with hash-query or with signature positions.

## Scope

* The model is abstract.  Nothing here says that the leaf and the digits of a real digest are
  independent and uniform, or even surjective images of it; transporting a byte-level digest
  into `Digest h a k` is the instantiating module's obligation.
* The probabilistic objects are one uniform digest for the fixed-list bounds, where `L` is a
  `Finset` quantified universally, and `q` independent uniform digests for the tuple bounds.  No
  game, key or signature appears: the random-oracle bound quantifies over an arbitrary
  computation `oa` and an arbitrary query domain `D`, and says nothing about what a scheme
  queries or about how a digest reaches the oracle.
* `evalDist_answerTape_tapeCoveredReuse_le` is stated at a single query budget `q` serving both
  roles, so its sum ranges over `q ^ (k + 1)` assignments.  The separated statements take the two
  families as data and are the ones with the smaller union.
* The two families of `TapeCoveredSplit` are abstract maps into the tuple's index type.  Nothing
  here says that one consists of hash-query positions and the other of signature positions, nor
  constructs any such pair; supplying them, together with the disjointness the bound requires,
  is the instantiating module's obligation.
* `sum_pow_card_image_eq_closedForm` is an equality, so the closed form adds no slack of its own
  to `evalDist_answerTape_tapeCoveredSplit_le`.  The inequalities that contribute slack lie
  upstream of it, in the union over witnesses and in `evalDist_multiFiber_le`; the third one, the
  product step of `evalDist_answerTape_setOf_forall_mem_le_prod_image`, is tight, because off the
  image of the assignment `piOfAssign p S` is an intersection over an empty index set and hence
  `Set.univ`, so the product over `univ` already equals the product over the image.  No matching
  lower bound on the mass of the event appears here.
* The random-oracle transport `evalDist_run_randomOracle_setOf_cacheCovered_le` is stated for the
  single-budget event only.  Nothing here transports the separated bound to a random-oracle run,
  which would need the tape positions of the signing queries located inside the cache.
* Nothing here is quantum.

## Labels

Forty-three declarations, six of them `private` and internal to the proofs: the five canonical
representative helpers and `evalDist_answerTape_roleSet_le`.

*The model*: `Digest`, `Covered`.

*The upper bound*: `fiber`, `card_fiber_le`, `encard_covered_le`, `evalDist_covered_le`.

*The matching lower bound*: `satList`, `card_satList_le`, `covered_satList`,
`evalDist_covered_satList_ge`, `evalDist_covered_satList_eq`, `not_covered_satList_erase_coord`,
`not_covered_satList_erase`.

*The per-coordinate cost*: `multiFiber`, `mem_multiFiber`, `card_multiFiber_le`,
`evalDist_multiFiber_le`, `prod_image_mul_pow_card_filter`.

*The tuple bound*: `TapeCoveredReuse`, `TapeCoveredNoFresh`, `tapeCoveredNoFresh_of_pos`,
`roleAssign`, `roleSet`, `image_roleAssign`, `evalDist_answerTape_roleSet_le`,
`evalDist_answerTape_tapeCoveredReuse_le`.

*Canonical coverer representatives*: `rep`, `cov_rep`, `rep_eq_of`, `rep_idem`,
`injOn_cov_rep`.

*The separated roles*: `TapeCoveredSplit`, `tapeCoveredReuse_of_tapeCoveredSplit`,
`evalDist_answerTape_tapeCoveredSplit_le`.

*The closed form*: `card_filter_image_eq_card_filter_surjective`, `card_filter_card_image_eq`,
`card_filter_card_image_eq_split`, `sum_pow_card_image_eq_sum_range`,
`sum_pow_card_image_eq_closedForm`, `evalDist_answerTape_tapeCoveredSplit_le_closedForm`.

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

/-- **The per-witness product bound.**  A tuple whose coordinate `j₀` holds `w` and whose
coordinate `g i` agrees with `w` on the leaf and on digit `i`, for every digit `i`, has mass at
most `|Digest|⁻¹ * ((2 ^ h)⁻¹ ^ r * ((2 ^ a)⁻¹) ^ k)`, where `r` is the number of distinct
coordinates `g` uses.  The hypothesis is freshness: no coverer sits on the target. -/
private theorem evalDist_answerTape_roleSet_le {q : ℕ} (j₀ : Fin q) (g : Fin k → Fin q)
    (hj₀ : j₀ ∉ Finset.univ.image g) (w : Digest h a k) :
    𝒟[answerTape (Digest h a k) q] {v | ∀ i, v (roleAssign j₀ g i) ∈ roleSet h a k w i} ≤
      (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹ *
        ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image g).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
  classical
  set δ : Fin q → ℝ≥0∞ := fun j =>
    if j = j₀ then (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹
    else ((2 : ℝ≥0∞) ^ h)⁻¹ *
      (((2 : ℝ≥0∞) ^ a)⁻¹) ^ (Finset.univ.filter (fun i => g i = j)).card with hδdef
  have hδ0 : δ j₀ = (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹ := by simp [hδdef]
  have hδn : ∀ j, j ≠ j₀ → δ j = ((2 : ℝ≥0∞) ^ h)⁻¹ *
      (((2 : ℝ≥0∞) ^ a)⁻¹) ^ (Finset.univ.filter (fun i => g i = j)).card :=
    fun j hj => by simp [hδdef, hj]
  have hδ : ∀ j ∈ Finset.univ.image (roleAssign j₀ g),
      𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))]
        (piOfAssign (roleAssign j₀ g) (roleSet h a k w) j) ≤ δ j := by
    intro j hj
    by_cases hjj : j = j₀
    · have hsub : piOfAssign (roleAssign j₀ g) (roleSet h a k w) j ⊆ {w} := fun u hu => by
        simpa [roleSet] using mem_piOfAssign.mp hu 0 (by simp [roleAssign, hjj])
      refine (measure_mono hsub).trans (le_of_eq ?_)
      rw [SampleableType.evalDist_uniformSample_singleton (α := Digest h a k) w, hjj, hδ0]
    · have hjg : j ∈ Finset.univ.image g := by
        rw [image_roleAssign] at hj
        exact (Finset.mem_insert.mp hj).resolve_left hjj
      obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hjg
      have hall : ∀ i : Fin k, g i = j →
          ∀ u : Digest h a k, u ∈ piOfAssign (roleAssign j₀ g) (roleSet h a k w) j →
            u ∈ (multiFiber h a k {i} w : Set (Digest h a k)) := fun i hi u hu => by
        simpa [roleSet] using mem_piOfAssign.mp hu i.succ (by simp [roleAssign, hi])
      have hsub : piOfAssign (roleAssign j₀ g) (roleSet h a k w) j ⊆
          (multiFiber h a k (Finset.univ.filter (fun i => g i = j)) w :
            Set (Digest h a k)) := by
        intro u hu
        rw [Finset.mem_coe, mem_multiFiber]
        refine ⟨((mem_multiFiber h a k).mp (hall i₀ hi₀ u hu)).1, fun i hi => ?_⟩
        rw [Finset.mem_filter] at hi
        exact ((mem_multiFiber h a k).mp (hall i hi.2 u hu)).2 i (Finset.mem_singleton_self i)
      refine (measure_mono hsub).trans ?_
      rw [hδn j hjj]
      exact evalDist_multiFiber_le h a k _ w
  refine (evalDist_answerTape_setOf_forall_mem_le_prod_image (roleAssign j₀ g)
    (roleSet h a k w) δ hδ).trans ?_
  rw [image_roleAssign, Finset.prod_insert hj₀, hδ0,
    Finset.prod_congr rfl (fun j hj => hδn j (fun hjj => hj₀ (hjj ▸ hj))),
    prod_image_mul_pow_card_filter h a k g]

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
    refine evalDist_answerTape_roleSet_le h a k j₀ f ?_ w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun i hi => hne i hi
  · rw [Finset.sum_product]
    refine le_of_eq (Finset.sum_congr rfl fun c _ => ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hN0 hNt, one_mul]

/-! ## Coverage with the two roles at separate positions -/

/-- **Interleaved-target coverage with the target and the coverers drawn from separate position
families.**  Some position of the target family `tgt` has each of its `k` digits matched, at its
own leaf, by a position of the coverer family `cov`.  As in `TapeCoveredReuse` the coverers need
not be distinct.

**Meaningful only for disjoint families.**  No freshness clause appears here, so if `tgt` and
`cov` share a position this event is satisfied by every tuple — a target covers itself — and it
is the caller's disjointness hypothesis, not this definition, that rules that out.  Every bound
below assumes `∀ n j, tgt n ≠ cov j`, and without it the bound is false rather than merely
loose. -/
@[expose] def TapeCoveredSplit (q qh qs : ℕ) (tgt : Fin qh → Fin q) (cov : Fin qs → Fin q)
    (v : Fin q → Digest h a k) : Prop :=
  ∃ n : Fin qh, ∃ f : Fin k → Fin qs,
    ∀ i, (v (cov (f i))).1 = (v (tgt n)).1 ∧ (v (cov (f i))).2 i = (v (tgt n)).2 i

/-- **The split event is a sub-event of the single-budget one.**  Disjointness of the two
families supplies the freshness `TapeCoveredReuse` requires. -/
theorem tapeCoveredReuse_of_tapeCoveredSplit {q qh qs : ℕ} {tgt : Fin qh → Fin q}
    {cov : Fin qs → Fin q} (hdisj : ∀ n j, tgt n ≠ cov j) {v : Fin q → Digest h a k}
    (hv : TapeCoveredSplit h a k q qh qs tgt cov v) : TapeCoveredReuse h a k q v := by
  obtain ⟨n, f, hcov⟩ := hv
  exact ⟨tgt n, fun i => cov (f i), fun i hi => hdisj n (f i) hi.symm, hcov⟩

/-! ### Canonical representatives of coverer positions -/

/-- The least index sharing a given coverer position. -/
private def rep {q qs : ℕ} (cov : Fin qs → Fin q) (j : Fin qs) : Fin qs :=
  (Finset.univ.filter fun j' => cov j' = cov j).min' ⟨j, by simp⟩

private theorem cov_rep {q qs : ℕ} (cov : Fin qs → Fin q) (j : Fin qs) :
    cov (rep cov j) = cov j := by
  have := (Finset.univ.filter fun j' => cov j' = cov j).min'_mem ⟨j, by simp⟩
  simpa [rep] using (Finset.mem_filter.mp this).2

private theorem rep_eq_of {q qs : ℕ} (cov : Fin qs → Fin q) {j₁ j₂ : Fin qs}
    (he : cov j₁ = cov j₂) : rep cov j₁ = rep cov j₂ := by
  have hs : (Finset.univ.filter fun j' => cov j' = cov j₁)
      = (Finset.univ.filter fun j' => cov j' = cov j₂) := by simp [he]
  simp only [rep]
  congr 1

private theorem rep_idem {q qs : ℕ} (cov : Fin qs → Fin q) (j : Fin qs) :
    rep cov (rep cov j) = rep cov j :=
  rep_eq_of cov (cov_rep cov j)

private theorem injOn_cov_rep {q qs : ℕ} (cov : Fin qs → Fin q) {j₁ j₂ : Fin qs}
    (he : cov (rep cov j₁) = cov (rep cov j₂)) : rep cov j₁ = rep cov j₂ := by
  rw [cov_rep cov j₁, cov_rep cov j₂] at he
  exact rep_eq_of cov he

/-- **The coverage bound with the two roles at separate positions.**  The target ranges over `qh`
positions and each coverer over `qs` positions, so the union is over `qh * qs ^ k` witnesses
rather than over `q ^ (k + 1)` of them, and the number `r` of distinct coverers is drawn from
`qs`.  No freshness filter restricts the sum: the disjointness hypothesis makes every witness
fresh.

The exponent `r` counts distinct coverer *indices*, and coverers sharing a position are charged
for their common leaf once.  The coverer family need not be injective: it is enough to take the
union over those witnesses whose indices are the canonical representatives `rep cov` of their
positions, which already cover the event, and to bound that sum by the sum over all witnesses.

Disjointness, by contrast, is necessary for the statement and not merely for this proof: with
`tgt` and `cov` sharing a position the event holds for every tuple while the right-hand side
stays below `1`. -/
theorem evalDist_answerTape_tapeCoveredSplit_le (q qh qs : ℕ) (tgt : Fin qh → Fin q)
    (cov : Fin qs → Fin q) (hdisj : ∀ n j, tgt n ≠ cov j) :
    𝒟[answerTape (Digest h a k) q] {v | TapeCoveredSplit h a k q qh qs tgt cov v} ≤
      ∑ c : Fin qh × (Fin k → Fin qs),
        (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.2).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k := by
  classical
  have hN0 : (Fintype.card (Digest h a k) : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hNt : (Fintype.card (Digest h a k) : ℝ≥0∞) ≠ ⊤ := by finiteness
  set C : Finset (Fin qh × (Fin k → Fin qs)) :=
    Finset.univ.filter fun c => ∀ i, rep cov (c.2 i) = c.2 i
  have himg : ∀ f : Fin k → Fin qs, (∀ i, rep cov (f i) = f i) →
      (Finset.univ.image fun i => cov (f i)).card = (Finset.univ.image f).card := by
    intro f hf
    rw [show (Finset.univ.image fun i => cov (f i)) = (Finset.univ.image f).image cov from
      (Finset.image_image ..).symm]
    refine Finset.card_image_of_injOn ?_
    intro x hx y hy hxy
    obtain ⟨ix, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨iy, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hf ix, ← hf iy] at hxy ⊢
    exact injOn_cov_rep cov hxy
  refine (evalDist_answerTape_le_sum_of_subset_biUnion
    (C ×ˢ (Finset.univ : Finset (Digest h a k)))
    {v | TapeCoveredSplit h a k q qh qs tgt cov v}
    (fun c => {v | ∀ i, v (roleAssign (tgt c.1.1) (fun i => cov (c.1.2 i)) i) ∈
      roleSet h a k c.2 i})
    (fun c => (Fintype.card (Digest h a k) : ℝ≥0∞)⁻¹ *
      ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.1.2).card *
        (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k)) ?_ ?_).trans ?_
  · rintro v ⟨n, f, hcovv⟩
    refine Set.mem_biUnion (x := ((n, fun i => rep cov (f i)), v (tgt n)))
      (Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩)) fun i => ?_
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => rep_idem cov (f i)⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · simp [roleAssign, roleSet]
      · simp only [roleAssign, Fin.cons_succ, roleSet]
        rw [Finset.mem_coe, mem_multiFiber, cov_rep cov (f i')]
        refine ⟨(hcovv i').1, fun i'' hi'' => ?_⟩
        rw [Finset.mem_singleton] at hi''
        rw [hi'']
        exact (hcovv i').2
  · rintro ⟨⟨n, f⟩, w⟩ hc
    have hf : ∀ i, rep cov (f i) = f i :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).2
    refine (evalDist_answerTape_roleSet_le h a k (tgt n) (fun i => cov (f i)) ?_ w).trans ?_
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun i hi => hdisj n (f i) hi.symm
    · rw [himg f hf]
  · rw [Finset.sum_product]
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset (Finset.subset_univ C))
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel hN0 hNt, one_mul]

/-! ## The closed form of the split bound -/

/-- The functions `Fin n → β` whose image is exactly a given `r`-element `T` are in bijection
with the surjections `Fin n → Fin r`. -/
theorem card_filter_image_eq_card_filter_surjective {β : Type*} [Fintype β] [DecidableEq β]
    {n r : ℕ} {T : Finset β} (hT : T.card = r) :
    (Finset.univ.filter fun f : Fin n → β => Finset.univ.image f = T).card
      = (Finset.univ.filter fun s : Fin n → Fin r => Function.Surjective s).card := by
  classical
  let e : ↥T ≃ Fin r := T.equivFin.trans (finCongr hT)
  refine Finset.card_bij (fun f hf x => e ⟨f x, by
      rw [← (Finset.mem_filter.mp hf).2]; exact Finset.mem_image_of_mem f (Finset.mem_univ x)⟩)
    ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun y => ?_⟩
    have hmem : (e.symm y : β) ∈ Finset.univ.image f := by
      rw [(Finset.mem_filter.mp hf).2]; exact (e.symm y).2
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmem
    exact ⟨x, e.eq_symm_apply.mp (Subtype.ext hx)⟩
  · intro f hf g hg hfg
    funext x
    simpa [Subtype.ext_iff] using e.injective (congrFun hfg x)
  · intro s hs
    have hsurj := (Finset.mem_filter.mp hs).2
    refine ⟨fun x => (e.symm (s x) : β), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Finset.Subset.antisymm (fun b hb => ?_) fun b hb => ?_⟩
      · obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hb
        exact hx ▸ (e.symm (s x)).2
      · obtain ⟨x, hx⟩ := hsurj (e ⟨b, hb⟩)
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, by simp [hx]⟩
    · funext x
      simp

/-- **Counting by image size.**  The functions `Fin n → β` with exactly `r` distinct values
number `C(|β|, r)` times the number of surjections `Fin n → Fin r`.  No positivity hypothesis on
`n` or `r` is needed; at `r > n` both sides vanish. -/
theorem card_filter_card_image_eq {β : Type*} [Fintype β] [DecidableEq β] (n r : ℕ) :
    (Finset.univ.filter fun f : Fin n → β => (Finset.univ.image f).card = r).card
      = (Fintype.card β).choose r *
        (Finset.univ.filter fun s : Fin n → Fin r => Function.Surjective s).card := by
  classical
  have key : ∀ T ∈ Finset.powersetCard r (Finset.univ : Finset β),
      (Finset.filter (fun f : Fin n → β => Finset.univ.image f = T)
        (Finset.univ.filter fun f : Fin n → β => (Finset.univ.image f).card = r)).card
        = (Finset.univ.filter fun s : Fin n → Fin r => Function.Surjective s).card := by
    intro T hT
    have hTc : T.card = r := (Finset.mem_powersetCard.mp hT).2
    rw [Finset.filter_filter,
      Finset.filter_congr (fun f _ => ⟨fun hh => hh.2, fun hh => ⟨hh ▸ hTc, hh⟩⟩)]
    exact card_filter_image_eq_card_filter_surjective hTc
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f : Fin n → β => Finset.univ.image f)
    (t := Finset.powersetCard r (Finset.univ : Finset β))
    (fun f hf => Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
      (Finset.mem_filter.mp hf).2⟩),
    Finset.sum_const_nat key, Finset.card_powersetCard, Finset.card_univ]

/-- **The fibre count on the separated index set.**  The witnesses using exactly `r` distinct
coverers number `qh * C(qs, r) * #{surjections Fin n → Fin r}`.

The factor is a binomial coefficient and not `Nat.descFactorial`: the surjection count is
`r ! * S(n, r)` for `S` the Stirling number of the second kind, so it already carries the `r !`
by which `(qs).descFactorial r` exceeds `C(qs, r)`. -/
theorem card_filter_card_image_eq_split (qh qs n r : ℕ) :
    (Finset.univ.filter fun c : Fin qh × (Fin n → Fin qs) =>
        (Finset.univ.image c.2).card = r).card
      = qh * qs.choose r *
        (Finset.univ.filter fun s : Fin n → Fin r => Function.Surjective s).card := by
  classical
  have hsplit : (Finset.univ.filter fun c : Fin qh × (Fin n → Fin qs) =>
      (Finset.univ.image c.2).card = r)
      = (Finset.univ : Finset (Fin qh)) ×ˢ
        (Finset.univ.filter fun f : Fin n → Fin qs => (Finset.univ.image f).card = r) := by
    ext c
    simp [Finset.mem_product]
  rw [hsplit, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    card_filter_card_image_eq (β := Fin qs) n r, Fintype.card_fin, mul_assoc]

/-- **Regrouping the split sum by the number of distinct coverers.**  Unconditional: the image of
a `Fin k`-indexed assignment has at most `k` elements, so `r` never escapes `range (k + 1)`. -/
theorem sum_pow_card_image_eq_sum_range (qh qs : ℕ) :
    ∑ c : Fin qh × (Fin k → Fin qs),
        (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.2).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k
      = ∑ r ∈ Finset.range (k + 1),
          ((Finset.univ.filter fun c : Fin qh × (Fin k → Fin qs) =>
              (Finset.univ.image c.2).card = r).card : ℝ≥0∞) *
            ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun c : Fin qh × (Fin k → Fin qs) =>
    (Finset.univ.image c.2).card) (t := Finset.range (k + 1)) ?_]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.mp hc).2],
      Finset.sum_const, nsmul_eq_mul]
  · intro c _
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.card_image_le.trans (by simp)

/-- **The split sum in closed form.**  It is
`∑ r ≤ k, qh * C(qs, r) * #{surjections Fin k → Fin r} * (2 ^ (-h * r) * 2 ^ (-a * k))`. -/
theorem sum_pow_card_image_eq_closedForm (qh qs : ℕ) :
    ∑ c : Fin qh × (Fin k → Fin qs),
        (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image c.2).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k
      = ∑ r ∈ Finset.range (k + 1),
          ((qh * qs.choose r *
              (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card : ℕ) :
            ℝ≥0∞) *
            ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
  rw [sum_pow_card_image_eq_sum_range h a k qh qs]
  exact Finset.sum_congr rfl fun r _ => by rw [card_filter_card_image_eq_split]

/-- **The split coverage bound in closed form.**  The mass of the event in which a target among
`qh` positions is covered, with reuse, by coverers among `qs` positions disjoint from them is at
most `∑ r ≤ k, qh * C(qs, r) * #{surjections Fin k → Fin r} * 2 ^ (-h * r) * 2 ^ (-a * k)`, the
sum being over the number `r` of distinct coverers.  The surjection count is `r ! * S(k, r)` for
`S` the Stirling number of the second kind. -/
theorem evalDist_answerTape_tapeCoveredSplit_le_closedForm (q qh qs : ℕ) (tgt : Fin qh → Fin q)
    (cov : Fin qs → Fin q) (hdisj : ∀ n j, tgt n ≠ cov j) :
    𝒟[answerTape (Digest h a k) q] {v | TapeCoveredSplit h a k q qh qs tgt cov v} ≤
      ∑ r ∈ Finset.range (k + 1),
        ((qh * qs.choose r *
            (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card : ℕ) :
          ℝ≥0∞) *
          ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) :=
  (evalDist_answerTape_tapeCoveredSplit_le h a k q qh qs tgt cov hdisj).trans
    (le_of_eq (sum_pow_card_image_eq_closedForm h a k qh qs))

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
