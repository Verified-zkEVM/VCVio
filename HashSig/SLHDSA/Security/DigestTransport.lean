/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.EncodingLemmas
public import HashSig.SLHDSA.Fors
public import HashSig.SLHDSA.Position
public import HashSig.SLHDSA.Security.CanonicalGames
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering
public import VCVio.OracleComp.EvalDist.MeasureSpec

/-!
# Byte-level transport of the interleaved-target coverage model

`VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering` computes with an *abstract*
digest, `Digest h a k = Fin (2 ^ h) × (Fin k → Fin (2 ^ a))`: a leaf index together with one
digit per FORS tree.  FIPS 205's `H_msg` returns bytes, `Bytes p.m`, and the FORS message digest
and the hypertree position are *extracted* from those bytes by `SLHDSA.splitDigest` and
`SLHDSA.forsIdx`.  Every covering number the abstract module proves is therefore a number about
the abstract model, not about SLH-DSA, until the decoding is shown to carry a uniform byte
string to a uniform abstract digest.  `Covering`'s own Scope section names that as the
instantiating module's obligation; this module discharges it.

`coveringDigest` is the decoding: the hypertree position `splitDigest` selects, packed as one
index among `2 ^ h`, together with the `k` base-`2 ^ a` digits `forsIdx` reads off `md`.

## The decoding is surjective with equal fibers

`card_fiber_coveringDigest` computes the fiber: every abstract digest is decoded from exactly
`2 ^ (mdSlack + treeSlack + leafSlack)` of the `256 ^ m` message digests, and
`surjective_coveringDigest` records that no fiber is empty.  The three widths are the slack of
the three byte slices — `8⌈ka/8⌉ − ka`, `8⌈(h−h')/8⌉ − (h−h')` and `8⌈h/(8d)⌉ − h'` — and
`ka_le_eight_mul_digestBytes`, `sub_le_eight_mul_treeIdxBytes` and
`hp_le_eight_mul_leafIdxBytes` are the three inequalities that make them well defined.
`eight_mul_m` is the resulting bit accounting: the `8m` bits of a digest are the `ka` digit
bits, the `h` position bits, and the three slack fields.

**The slack is real, and that is why the statement is an equality anyway.**  At no FIPS 205
parameter set are all three slack widths zero: `8m` strictly exceeds `h + ka` at every one of
them, so the decoding is not a bijection and `Bytes p.m` is not an abstract digest in disguise.
What makes the transport exact rather than approximate is not the absence of unread bits but
their *position*: the unread bits form bit fields of their own, disjoint from the fields the
decoding reads.  A remainder modulo `2 ^ w` and a `base2b` digit are both truncations by a power
of two that divides the range of their slice, so each read field is equidistributed over the
slice and independent of the rest.  Hence no fiber-imbalance constant appears anywhere below,
and none is hidden in the bounds: `evalDist_uniformSample_preimage_coveringDigest` is an
equality of masses, not an inequality.

`idxLeaf_val_eq`, `idxTree_val_eq` and `forsIdx_eq` are where this is established against the
*actual* decoding rather than an idealisation of it.  Each rewrites one FIPS 205 output as a
bit field `toInt digest / 2 ^ offset % 2 ^ width` of the digest's big-endian value, through the
byte-slice lemmas of `SLHDSA.Position` and the MSB-first characterisation
`SLHDSA.base2b_bigEndian` of Algorithm 4.  The fiber count then follows from a right-inverse
family: `packLow` packs a list of `(width, value)` fields least-significant-first, `packLow_field`
reads any field back, and the encoder built from them realises every abstract digest at every
slack assignment with the slack recoverable, which is enough — `card_fiber_eq_of_fiberInj`
turns an injective copy of the slack in each fiber, plus the cardinality identity, into the
exact fiber count, since no fiber has room to be larger.

## The transport

`evalDist_uniformSample_preimage_eq_of_fiberInj` is the generic step: a map whose fibers each
carry an injective copy of `C`, with `card A = card B * card C`, carries a uniform sample to a
uniform sample.  `map_evalDist_uniformSample_coveringDigest` is
its measure form at the decoding, and `evalDist_answerTape_preimage_coveringDigest` lifts it
coordinatewise to the answer tape of `q` independent uniform answers, through
`MeasureTheory.Measure.pi_map_pi`.  `evalDist_answerTape_tapeCoveredSplit_coveringDigest_le` and
`evalDist_answerTape_tapeCoveredSplit_coveringDigest_le_closedForm` are the separated coverage
bounds of `Covering`, stated for the event about decoded digests, with the same right-hand
sides: the transport contributes no loss.

## Scope

* **This is a distributional bridge, not a game.**  Every statement here is about a *uniform*
  `Bytes p.m` answer, or a tape of `q` of them.  Nothing here routes the signer's or the
  forger's `H_msg` query to such an answer, and no unforgeability statement follows from anything
  below.  It supplies the distributional step such an argument needs, not the
  argument.
* **The positional obligation of the split is not discharged.**  Confining the coverers to their
  own family needs the tape positions of the signing queries exhibited, as `Covering` records
  under the obligation the separation carries, and nothing here exhibits them: `tgt` and `cov`
  here are the same abstract maps, and `evalDist_answerTape_tapeCoveredSplit_coveringDigest_le`
  assumes the same disjointness hypothesis.  Decoding the digests does not identify either
  family with anything.
* **Nothing here bounds a coverage event of a cache.**  A cache's logged digests are chosen by
  the run, not drawn uniformly, so the tape statements below do not reach such an event directly.
* The abstract leaf is the whole hypertree position, `idxTree` and `idxLeaf` packed together,
  and `coveringDigest_fst_eq_iff` states that two decoded leaves agree exactly when both
  indices do, so a coverage event stated on FIPS 205 positions is the event on decoded
  digests.  Nothing here says that a real signature is produced at that position, only that
  the decoding of a uniform digest is uniform on it.
* `coveringDigest` takes a `ValidatedParams`: `hp_le_h` is needed for the packed leaf to be an
  index among `2 ^ h` at all, and `hp_le_eight_mul_leafIdxBytes` — the one slack inequality
  that is not pure ceiling arithmetic — needs `h = d·h'` and `0 < d`.  The other two slack
  inequalities, `ka_le_eight_mul_digestBytes` and `sub_le_eight_mul_treeIdxBytes`, hold for
  every `Params`.
* The measurable structure on `Bytes p.m` is taken as an instance *parameter* throughout, not
  pinned here: `MeasurableSpace (Vector UInt8 n)` does not synthesise, and pinning `⊤` in this
  module would fix that choice for every consumer.  The transport statements ask only for a
  measurable space that is discrete.
* Nothing here is quantum.

## Placement

The bridge sits on the scheme side because it mentions both `HashSig.SLHDSA`'s decoding and
`VCVio`'s abstract model, and `VCVio` must not depend on `HashSig`.  The generic lemmas of the
first section are scheme independent and would be at home in `VCVio`; their statements mention
nothing from `HashSig`.

## Labels

Sixty-four declarations, thirty-nine of them `private`: the field-packing algebra, the
byte-slice arithmetic, the digest-value bijection, and the encoder with its offsets.

*The generic transport*: `card_fiber_eq_of_fiberInj`, `surjective_of_fiberInj`,
`evalDist_uniformSample_preimage_eq_of_fiberInj`.

*The bit accounting*: `mdSlack`, `treeSlack`, `leafSlack`, `ka_le_eight_mul_digestBytes`,
`sub_le_eight_mul_treeIdxBytes`, `hp_le_eight_mul_leafIdxBytes`, `hp_le_h`, `eight_mul_m`.

*The decoding as bit fields*: `idxLeaf_val_eq`, `idxTree_val_eq`, `forsIdx_eq`.

*The decoding*: `coveringDigest`, `coveringDigest_fst_val`, `coveringDigest_snd_val`,
`coveringDigest_fst_eq_iff`.

*Surjectivity with equal fibers*: `card_fiber_coveringDigest`, `surjective_coveringDigest`.

*The transport*: `evalDist_uniformSample_preimage_coveringDigest`,
`map_evalDist_uniformSample_coveringDigest`, `evalDist_answerTape_preimage_coveringDigest`,
`evalDist_answerTape_tapeCoveredSplit_coveringDigest_le`,
`evalDist_answerTape_tapeCoveredSplit_coveringDigest_le_closedForm`.

## References

* NIST FIPS 205, §9 and Algorithms 19–20 (the message-digest decomposition), Algorithm 4
  (`base2b`).
* Hülsing and Kudinov, "Recovering the Tight Security Proof of SPHINCS+", the interleaved
  target subset resilience bound the abstract model computes.
-/

public section

namespace SLHDSA.DigestTransport

open MeasureTheory
open scoped ENNReal

/-! ## Uniform transport along a map with equal fibers -/

/-- **Equal fibers from a right-inverse family.**  `ι` injects `C` into every fiber of `g`, so
every fiber has at least `card C` elements; the cardinality identity leaves no room for any
fiber to be larger. -/
theorem card_fiber_eq_of_fiberInj {A B C : Type} [Fintype A] [Fintype B]
    [DecidableEq B] [Fintype C] (g : A → B) (ι : B → C → A) (hgι : ∀ z c, g (ι z c) = z)
    (hι : ∀ z, Function.Injective (ι z))
    (hcard : Fintype.card A = Fintype.card B * Fintype.card C) (z : B) :
    (Finset.univ.filter fun x : A => g x = z).card = Fintype.card C := by
  set F : B → Finset A := fun z => Finset.univ.filter fun x => g x = z with hF
  have hmemF : ∀ (z : B) (x : A), x ∈ F z ↔ g x = z := by intro z x; simp [hF]
  have hge : ∀ z, Fintype.card C ≤ (F z).card := fun z =>
    Finset.card_le_card_of_injOn (ι z) (fun c _ => (hmemF z _).mpr (hgι z c)) ((hι z).injOn)
  have hsum : ∑ z : B, (F z).card = Fintype.card B * Fintype.card C := by
    rw [← hcard, Fintype.card, Finset.card_eq_sum_card_fiberwise (f := g)
      (t := (Finset.univ : Finset B)) fun _ _ => Finset.mem_univ _]
  have hconst : ∑ _z : B, Fintype.card C = Fintype.card B * Fintype.card C := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h := (Finset.sum_eq_sum_iff_of_le (s := (Finset.univ : Finset B))
    (f := fun _ : B => Fintype.card C) (g := fun z => (F z).card)
    fun z _ => hge z).mp (hconst.trans hsum.symm)
  exact (h z (Finset.mem_univ z)).symm

/-- A map with a right-inverse family over a nonempty index type is surjective. -/
theorem surjective_of_fiberInj {A B C : Type} (g : A → B) (ι : B → C → A) [Nonempty C]
    (hgι : ∀ z c, g (ι z c) = z) : Function.Surjective g :=
  fun z => ⟨ι z (Classical.arbitrary C), hgι z _⟩

/-- **A uniform sample transports along a map whose fibers all carry a copy of `C`.**
Given the cardinality identity `card A = card B * card C`, the uniform sample on `A` assigns
`g ⁻¹' S` the mass the uniform sample on `B` assigns `S`. -/
theorem evalDist_uniformSample_preimage_eq_of_fiberInj {A B C : Type}
    [SampleableType A] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [SampleableType B] [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype C] [Nonempty C]
    (g : A → B) (ι : B → C → A) (hgι : ∀ z c, g (ι z c) = z)
    (hι : ∀ z, Function.Injective (ι z))
    (hcard : Fintype.card A = Fintype.card B * Fintype.card C) (S : Set B) :
    𝒟[($ᵗ A : ProbComp A)] (g ⁻¹' S) = 𝒟[($ᵗ B : ProbComp B)] S := by
  let _ : DecidableEq B := Classical.decEq B
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  have hfib := card_fiber_eq_of_fiberInj g ι hgι hι hcard
  set T : Finset B := Finset.univ.filter (· ∈ S) with hT
  have hmemT : ∀ z : B, z ∈ T ↔ z ∈ S := by intro z; simp [hT]
  have hpre : g ⁻¹' S = ↑(Finset.univ.filter fun x => g x ∈ S) := by ext x; simp
  have hTset : S = ↑T := by ext z; simpa using (hmemT z).symm
  have hcount : (Finset.univ.filter fun x => g x ∈ S).card = T.card * Fintype.card C := by
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := T)
      (fun x hx => (hmemT _).mpr (by simpa using (Finset.mem_filter.mp hx).2))]
    have hterm : ∀ z ∈ T, ((Finset.univ.filter fun x => g x ∈ S).filter
        fun x => g x = z).card = Fintype.card C := by
      intro z hz
      rw [← hfib z]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ (hmemT z).mp hz, h⟩⟩
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  rw [SampleableType.evalDist_uniformSample_eq_encard_div,
    SampleableType.evalDist_uniformSample_eq_encard_div, hpre,
    Set.encard_coe_eq_coe_finsetCard, hcount, hcard]
  rw [hTset, Set.encard_coe_eq_coe_finsetCard]
  push_cast
  rw [ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp)]

/-! ## Little-endian field packing -/

/-- Pack a list of `(width, value)` fields into one natural number, least-significant field
first: the head occupies the low `w` bits and the tail sits above it. -/
private def packLow : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (w, x) :: rest => x + packLow rest * 2 ^ w

/-- The total width of a field list. -/
private def totalWidth (l : List (ℕ × ℕ)) : ℕ := (l.map Prod.fst).sum

@[simp] private theorem packLow_nil : packLow [] = 0 := rfl

private theorem packLow_cons (w x : ℕ) (rest : List (ℕ × ℕ)) :
    packLow ((w, x) :: rest) = x + packLow rest * 2 ^ w := rfl

@[simp] private theorem totalWidth_nil : totalWidth [] = 0 := rfl

private theorem totalWidth_cons (w x : ℕ) (rest : List (ℕ × ℕ)) :
    totalWidth ((w, x) :: rest) = w + totalWidth rest := by
  simp [totalWidth]

/-- A packed value fits the total width, provided every field fits its own. -/
private theorem packLow_lt (l : List (ℕ × ℕ)) (hl : ∀ q ∈ l, q.2 < 2 ^ q.1) :
    packLow l < 2 ^ totalWidth l := by
  induction l with
  | nil => simp
  | cons q rest ih =>
      obtain ⟨w, x⟩ := q
      have hx : x < 2 ^ w := hl _ List.mem_cons_self
      have hrest := ih fun r hr => hl r (List.mem_cons_of_mem _ hr)
      rw [packLow_cons, totalWidth_cons, pow_add]
      calc x + packLow rest * 2 ^ w
          < 2 ^ w + packLow rest * 2 ^ w := by omega
        _ = (packLow rest + 1) * 2 ^ w := by ring
        _ ≤ 2 ^ totalWidth rest * 2 ^ w := by
            exact Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ w * 2 ^ totalWidth rest := by ring

/-- The low field is read by a remainder. -/
private theorem packLow_mod (w x : ℕ) (rest : List (ℕ × ℕ)) (hx : x < 2 ^ w) :
    packLow ((w, x) :: rest) % 2 ^ w = x := by
  rw [packLow_cons, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

/-- Dividing by the low field's width discards it. -/
private theorem packLow_div (w x : ℕ) (rest : List (ℕ × ℕ)) (hx : x < 2 ^ w) :
    packLow ((w, x) :: rest) / 2 ^ w = packLow rest := by
  rw [packLow_cons, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
    Nat.div_eq_of_lt hx, Nat.zero_add]

/-- Dividing by the width of the first `n` fields drops exactly those fields. -/
private theorem packLow_div_totalWidth_take (l : List (ℕ × ℕ))
    (hl : ∀ q ∈ l, q.2 < 2 ^ q.1) (n : ℕ) :
    packLow l / 2 ^ totalWidth (l.take n) = packLow (l.drop n) := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      match l with
      | [] => simp
      | (w, x) :: rest =>
          have hx : x < 2 ^ w := hl _ List.mem_cons_self
          have hrest : ∀ q ∈ rest, q.2 < 2 ^ q.1 := fun r hr => hl r (List.mem_cons_of_mem _ hr)
          rw [List.take_succ_cons, totalWidth_cons, pow_add, ← Nat.div_div_eq_div_mul,
            packLow_div w x rest hx, ih rest hrest, List.drop_succ_cons]

/-- **Field extraction.**  The `n`-th field of a packed value is read by the division and
remainder its offset and width prescribe. -/
private theorem packLow_field (l : List (ℕ × ℕ)) (hl : ∀ q ∈ l, q.2 < 2 ^ q.1) (n w x : ℕ)
    (hn : l.drop n = (w, x) :: l.drop (n + 1)) :
    packLow l / 2 ^ totalWidth (l.take n) % 2 ^ w = x := by
  have hx : x < 2 ^ w := by
    refine hl (w, x) ?_
    have : (w, x) ∈ l.drop n := hn ▸ List.mem_cons_self
    exact List.mem_of_mem_drop this
  rw [packLow_div_totalWidth_take l hl n, hn, packLow_mod w x _ hx]


/-! ## Byte slices as division and remainder -/

/-- The suffix of a byte string denotes the low part of its value. -/
private theorem toInt_drop (x : List Byte) (c : ℕ) :
    toInt (x.drop c) = toInt x % 256 ^ (x.length - c) := by
  have hsplit : toInt x = toInt (x.take c) * 256 ^ (x.length - c) + toInt (x.drop c) := by
    conv_lhs => rw [← List.take_append_drop c x]
    rw [toInt_append, List.length_drop]
  have hlt : toInt (x.drop c) < 256 ^ (x.length - c) := by
    simpa [List.length_drop] using toInt_lt_pow (x.drop c)
  rw [hsplit, Nat.mul_add_mod', Nat.mod_eq_of_lt hlt]

/-- The prefix of a byte string denotes the high part of its value. -/
private theorem toInt_take (x : List Byte) (c : ℕ) :
    toInt (x.take c) = toInt x / 256 ^ (x.length - c) := by
  have hsplit : toInt x = 256 ^ (x.length - c) * toInt (x.take c) + toInt (x.drop c) := by
    conv_lhs => rw [← List.take_append_drop c x]
    rw [toInt_append, List.length_drop, Nat.mul_comm]
  have hlt : toInt (x.drop c) < 256 ^ (x.length - c) := by
    simpa [List.length_drop] using toInt_lt_pow (x.drop c)
  rw [hsplit, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt, Nat.add_zero]

/-- `256 ^ c = 2 ^ (8 * c)`. -/
private theorem pow_256 (c : ℕ) : (256 : ℕ) ^ c = 2 ^ (8 * c) := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]

/-! ## The bit accounting of the FIPS 205 message-digest widths -/

/-- Slack bits of the FORS-message slice: `8⌈ka/8⌉ − ka`.

Exposed, with the other two slack widths, because their values at a parameter set are what the
fiber count of the decoding is stated in terms of: a consumer must be able to reduce them. -/
@[expose] def mdSlack (p : Params) : ℕ := 8 * p.digestBytes - p.k * p.a

/-- Slack bits of the tree-index slice: `8⌈(h−h')/8⌉ − (h−h')`. -/
@[expose] def treeSlack (p : Params) : ℕ := 8 * p.treeIdxBytes - (p.h - p.hp)

/-- Slack bits of the leaf-index slice: `8⌈h/(8d)⌉ − h'`. -/
@[expose] def leafSlack (p : Params) : ℕ := 8 * p.leafIdxBytes - p.hp

/-- The FORS-message slice has room for its `ka` digit bits. -/
theorem ka_le_eight_mul_digestBytes (p : Params) : p.k * p.a ≤ 8 * p.digestBytes := by
  rw [Params.digestBytes]; omega

/-- The tree-index slice has room for its `h − h'` bits. -/
theorem sub_le_eight_mul_treeIdxBytes (p : Params) : p.h - p.hp ≤ 8 * p.treeIdxBytes := by
  rw [Params.treeIdxBytes]; omega

/-- The leaf-index slice has room for its `h'` bits. -/
theorem hp_le_eight_mul_leafIdxBytes {p : Params} (valid : p.Valid) :
    p.hp ≤ 8 * p.leafIdxBytes := by
  have hd : 0 < p.d := valid.d_pos
  have key : (p.hp + 7) / 8 ≤ p.leafIdxBytes := by
    rw [Params.leafIdxBytes, Nat.le_div_iff_mul_le (by positivity)]
    have h8 : 8 * ((p.hp + 7) / 8) ≤ p.hp + 7 := by omega
    calc (p.hp + 7) / 8 * (8 * p.d) = p.d * (8 * ((p.hp + 7) / 8)) := by ring
      _ ≤ p.d * (p.hp + 7) := Nat.mul_le_mul_left _ h8
      _ = p.d * p.hp + 7 * p.d := by ring
      _ ≤ p.h + 8 * p.d - 1 := by rw [valid.h_eq_layers]; omega
  omega

/-- A hypertree layer is no taller than the whole hypertree. -/
theorem hp_le_h {p : Params} (valid : p.Valid) : p.hp ≤ p.h :=
  valid.h_eq_layers ▸ Nat.le_mul_of_pos_left _ valid.d_pos

/-- **The bit accounting.**  The `8m` bits of an `H_msg` digest are exactly the `ka` FORS digit
bits, the `h` hypertree-position bits, and the three per-slice slack fields. -/
theorem eight_mul_m {p : Params} (valid : p.Valid) :
    8 * p.m = p.k * p.a + mdSlack p + treeSlack p + (p.h - p.hp) + leafSlack p + p.hp := by
  have h1 := ka_le_eight_mul_digestBytes p
  have h2 := sub_le_eight_mul_treeIdxBytes p
  have h3 := hp_le_eight_mul_leafIdxBytes valid
  rw [Params.m, mdSlack, treeSlack, leafSlack]
  omega


/-- Reading a mapped range at an index inside it. -/
private theorem getD_map_range {α : Type*} (f : ℕ → α) (n i : ℕ) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
    List.getElem_map, List.getElem_range, Option.getD_some]

/-! ## The FIPS 205 decoding as bit fields of the digest value -/

variable {p : Params}

/-- The leaf index is the low `h'` bits of the digest value. -/
theorem idxLeaf_val_eq (valid : p.Valid) (digest : Bytes p.m) :
    (splitDigest p digest).idxLeaf.val = toInt digest.toList % 2 ^ p.hp := by
  have hlen : digest.toList.length = p.m := by simp
  have hslice : (digest.toList.drop (p.digestBytes + p.treeIdxBytes)).take p.leafIdxBytes =
      digest.toList.drop (p.digestBytes + p.treeIdxBytes) := by
    rw [List.take_of_length_le]
    rw [List.length_drop, hlen, Params.m]
    omega
  have hdvd : (2 : ℕ) ^ p.hp ∣ 2 ^ (8 * p.leafIdxBytes) :=
    pow_dvd_pow 2 (hp_le_eight_mul_leafIdxBytes valid)
  rw [splitDigest_idxLeaf_val, hslice, toInt_drop, hlen,
    show p.m - (p.digestBytes + p.treeIdxBytes) = p.leafIdxBytes by rw [Params.m]; omega,
    pow_256, Nat.mod_mod_of_dvd _ hdvd]

/-- The tree index is the `h − h'` bits of the digest value above bit `8⌈h/(8d)⌉`. -/
theorem idxTree_val_eq (digest : Bytes p.m) :
    (splitDigest p digest).idxTree.val =
      toInt digest.toList / 2 ^ (8 * p.leafIdxBytes) % 2 ^ (p.h - p.hp) := by
  have hlen : digest.toList.length = p.m := by simp
  have hdroplen : (digest.toList.drop p.digestBytes).length = p.treeIdxBytes +
      p.leafIdxBytes := by rw [List.length_drop, hlen, Params.m]; omega
  have hdvd : (2 : ℕ) ^ (p.h - p.hp) ∣ 2 ^ (8 * p.treeIdxBytes) :=
    pow_dvd_pow 2 (sub_le_eight_mul_treeIdxBytes p)
  rw [splitDigest_idxTree_val, toInt_take, hdroplen,
    show p.treeIdxBytes + p.leafIdxBytes - p.treeIdxBytes = p.leafIdxBytes by omega,
    toInt_drop, hlen, show p.m - p.digestBytes = p.treeIdxBytes + p.leafIdxBytes by
      rw [Params.m]; omega, pow_256, pow_256,
    show 8 * (p.treeIdxBytes + p.leafIdxBytes) = 8 * p.leafIdxBytes + 8 * p.treeIdxBytes by ring,
    pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hdvd]

/-- The `i`-th FORS index is the `a` bits of the digest value at offset `8m − a(i+1)`. -/
theorem forsIdx_eq (digest : Bytes p.m) (i : ℕ) (hi : i < p.k) :
    forsIdx p (splitDigest p digest).md.toList i =
      toInt digest.toList / 2 ^ (8 * p.m - p.a * (i + 1)) % 2 ^ p.a := by
  have hlen : digest.toList.length = p.m := by simp
  have hmdlen : (digest.toList.take p.digestBytes).length = p.digestBytes := by
    rw [List.length_take, hlen, Params.m]; omega
  have hka := ka_le_eight_mul_digestBytes p
  have hai : p.a * (i + 1) ≤ 8 * p.digestBytes := by
    calc p.a * (i + 1) ≤ p.a * p.k := Nat.mul_le_mul_left _ (by omega)
      _ = p.k * p.a := Nat.mul_comm _ _
      _ ≤ 8 * p.digestBytes := hka
  rw [splitDigest_md_toList, forsIdx, base2b_bigEndian _ _ _ (by rw [hmdlen]; omega),
    getD_map_range _ _ _ hi, hmdlen, toInt_take, hlen,
    show p.m - p.digestBytes = p.treeIdxBytes + p.leafIdxBytes by rw [Params.m]; omega,
    pow_256, Nat.div_div_eq_div_mul, ← pow_add,
    show 8 * (p.treeIdxBytes + p.leafIdxBytes) + (8 * p.digestBytes - p.a * (i + 1)) =
      8 * p.m - p.a * (i + 1) by rw [Params.m]; omega]


/-! ## The digest value as a bijection -/

private theorem toInt_lt (n : ℕ) (d : Bytes n) : toInt d.toList < 256 ^ n := by
  simpa using toInt_lt_pow d.toList

/-- An `n`-byte string is determined by its big-endian value, and every value below
`256 ^ n` is realised. -/
private theorem toInt_bijective (n : ℕ) :
    Function.Bijective fun d : Bytes n => (⟨toInt d.toList, toInt_lt n d⟩ : Fin (256 ^ n)) := by
  constructor
  · intro d d' hdd
    refine Vector.toList_inj.mp (eq_of_length_eq_of_toInt_eq (by simp) ?_)
    simpa using congrArg Fin.val hdd
  · rintro ⟨j, hj⟩
    refine ⟨⟨(toByte j n).toArray, by simp⟩, ?_⟩
    have hj' : toInt (toByte j n) = j := by rw [toInt_toByte_mod, Nat.mod_eq_of_lt hj]
    simpa [Vector.toList] using hj'

/-- The big-endian value of an `n`-byte string, as an equivalence. -/
private noncomputable def bytesEquivFin (n : ℕ) : Bytes n ≃ Fin (256 ^ n) :=
  Equiv.ofBijective _ (toInt_bijective n)

@[simp] private theorem bytesEquivFin_symm_toInt (n : ℕ) (j : Fin (256 ^ n)) :
    toInt ((bytesEquivFin n).symm j).toList = j.val :=
  congrArg Fin.val ((bytesEquivFin n).apply_symm_apply j)

private theorem card_bytes (n : ℕ) : Fintype.card (Bytes n) = 256 ^ n := by
  rw [Fintype.card_of_bijective (toInt_bijective n), Fintype.card_fin]

/-! ## The abstract covering digest of a message digest -/

/-- **The abstract covering digest of an SLH-DSA message digest.**  The leaf is the hypertree
position `splitDigest` selects, packed as one index among `2 ^ h`; the digits are the `k` FORS
indices `forsIdx` reads off `md`.  It carries an `H_msg` answer into the digest type of
`KeyedHash.Covering`, whose coverage events are stated on such digests. -/
def coveringDigest (vp : ValidatedParams) (digest : Bytes vp.params.m) :
    KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k :=
  (⟨(splitDigest vp.params digest).idxTree.val * 2 ^ vp.params.hp +
      (splitDigest vp.params digest).idxLeaf.val, by
    have h2 := (splitDigest vp.params digest).idxLeaf.isLt
    calc (splitDigest vp.params digest).idxTree.val * 2 ^ vp.params.hp +
          (splitDigest vp.params digest).idxLeaf.val
        < (splitDigest vp.params digest).idxTree.val * 2 ^ vp.params.hp + 2 ^ vp.params.hp :=
          Nat.add_lt_add_left h2 _
      _ = ((splitDigest vp.params digest).idxTree.val + 1) * 2 ^ vp.params.hp := by ring
      _ ≤ 2 ^ (vp.params.h - vp.params.hp) * 2 ^ vp.params.hp :=
          Nat.mul_le_mul_right _ (splitDigest vp.params digest).idxTree.isLt
      _ = 2 ^ vp.params.h := by
          rw [← pow_add]; congr 1; have := hp_le_h vp.valid; omega⟩,
   fun i => ⟨forsIdx vp.params (splitDigest vp.params digest).md.toList i.val,
     forsIdx_lt _ _ _⟩)

@[simp] theorem coveringDigest_fst_val (vp : ValidatedParams) (digest : Bytes vp.params.m) :
    (coveringDigest vp digest).1.val = (splitDigest vp.params digest).idxTree.val *
      2 ^ vp.params.hp + (splitDigest vp.params digest).idxLeaf.val := by
  unfold coveringDigest; rfl

@[simp] theorem coveringDigest_snd_val (vp : ValidatedParams) (digest : Bytes vp.params.m)
    (i : Fin vp.params.k) :
    ((coveringDigest vp digest).2 i).val =
      forsIdx vp.params (splitDigest vp.params digest).md.toList i.val := by
  unfold coveringDigest; rfl

/-- Two decoded leaves agree exactly when the FIPS 205 hypertree positions agree, tree index
and leaf index both. -/
theorem coveringDigest_fst_eq_iff (vp : ValidatedParams) (d d' : Bytes vp.params.m) :
    (coveringDigest vp d).1 = (coveringDigest vp d').1 ↔
      (splitDigest vp.params d).idxTree = (splitDigest vp.params d').idxTree ∧
        (splitDigest vp.params d).idxLeaf = (splitDigest vp.params d').idxLeaf := by
  rw [Fin.ext_iff, coveringDigest_fst_val, coveringDigest_fst_val, Fin.ext_iff, Fin.ext_iff]
  have l1 := (splitDigest vp.params d).idxLeaf.isLt
  have l2 := (splitDigest vp.params d').idxLeaf.isLt
  refine ⟨fun h => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
  have hm := congrArg (· % 2 ^ vp.params.hp) h
  have hd := congrArg (· / 2 ^ vp.params.hp) h
  simp only [Nat.mul_add_mod_of_lt l1, Nat.mul_add_mod_of_lt l2] at hm
  simp only [mul_comm _ (2 ^ vp.params.hp), Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt l1, Nat.div_eq_of_lt l2, add_zero] at hd
  exact ⟨hd, hm⟩

open Security.CanonicalGames in
/-- A FORS digit of a digest is matched, leaf and digit, by every digest whose index list
contains that digit's index. -/
theorem coveringDigest_match_of_mem_hmsgIndices (vp : ValidatedParams)
    (digest d' : Bytes vp.params.m) (i : Fin vp.params.k)
    (h : (⟨(splitDigest vp.params digest).idxTree, (splitDigest vp.params digest).idxLeaf, i,
        ⟨forsIdx vp.params (splitDigest vp.params digest).md.toList i.val,
          forsIdx_lt _ _ _⟩⟩ : HmsgIndex vp.params) ∈ hmsgIndices vp.params d') :
    (coveringDigest vp d').1 = (coveringDigest vp digest).1 ∧
      (coveringDigest vp d').2 i = (coveringDigest vp digest).2 i := by
  obtain ⟨h1, h2, h3⟩ := (mem_hmsgIndices _ _ _).1 h
  exact ⟨(coveringDigest_fst_eq_iff vp d' digest).2 ⟨h1.symm, h2.symm⟩,
    Fin.ext (by rw [coveringDigest_snd_val, coveringDigest_snd_val]; exact h3.symm)⟩

/-! ## The slack fields and the encoder -/

/-- The bits of an `H_msg` digest that no FIPS 205 output reads: the low padding of the
FORS-message slice and the high padding of the two index slices. -/
private abbrev Slack (p : Params) : Type :=
  Fin (2 ^ mdSlack p) × Fin (2 ^ treeSlack p) × Fin (2 ^ leafSlack p)

/-- The `ka`-bit packing of the `k` FORS digits, most significant digit first. -/
private def packDigits (p : Params) (d : Fin p.k → Fin (2 ^ p.a)) : ℕ :=
  (finFunctionFinEquiv fun j => d j.rev : Fin ((2 ^ p.a) ^ p.k)).val

private theorem packDigits_lt (p : Params) (d : Fin p.k → Fin (2 ^ p.a)) :
    packDigits p d < 2 ^ (p.k * p.a) := by
  have h : packDigits p d < (2 ^ p.a) ^ p.k :=
    (finFunctionFinEquiv (m := 2 ^ p.a) (n := p.k) fun j => d j.rev).isLt
  rwa [← pow_mul, Nat.mul_comm p.a p.k] at h

/-- Each digit is read back off the packing by the division and remainder at its own offset. -/
private theorem packDigits_field (p : Params) (d : Fin p.k → Fin (2 ^ p.a)) (i : Fin p.k) :
    packDigits p d / 2 ^ (p.a * (p.k - 1 - i.val)) % 2 ^ p.a = (d i).val := by
  have h : finFunctionFinEquiv.symm (finFunctionFinEquiv fun j => d j.rev) i.rev = d i := by
    rw [Equiv.symm_apply_apply, Fin.rev_rev]
  have h' : packDigits p d / (2 ^ p.a) ^ (i.rev : ℕ) % 2 ^ p.a = (d i).val := by
    simp only [packDigits]
    rw [← congrArg Fin.val h, finFunctionFinEquiv_symm_apply_val]
  rwa [Fin.val_rev, ← pow_mul,
    show p.a * (p.k - (i.val + 1)) = p.a * (p.k - 1 - i.val) by congr 1; omega] at h'

/-- The digest value carrying the covering digest `z` in its read fields and `r` in its slack
fields, as a list of `(width, value)` fields with the least significant first. -/
private def fields (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k)
    (r : Slack vp.params) : List (ℕ × ℕ) :=
  [(vp.params.hp, z.1.val % 2 ^ vp.params.hp),
   (leafSlack vp.params, r.2.2.val),
   (vp.params.h - vp.params.hp, z.1.val / 2 ^ vp.params.hp),
   (treeSlack vp.params, r.2.1.val),
   (mdSlack vp.params, r.1.val),
   (vp.params.k * vp.params.a, packDigits vp.params z.2)]

private theorem fields_lt (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    ∀ q ∈ fields vp z r, q.2 < 2 ^ q.1 := by
  have hhp := hp_le_h vp.valid
  have hdiv : z.1.val / 2 ^ vp.params.hp < 2 ^ (vp.params.h - vp.params.hp) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    exact lt_of_lt_of_le z.1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
  intro q hq
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h <;> subst h
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · exact r.2.2.isLt
  · exact hdiv
  · exact r.2.1.isLt
  · exact r.1.isLt
  · exact packDigits_lt _ _

private theorem totalWidth_fields (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    totalWidth (fields vp z r) = 8 * vp.params.m := by
  rw [eight_mul_m vp.valid]
  simp only [fields, totalWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have := hp_le_h vp.valid
  omega

/-- The `m`-byte digest carrying `z` in its read fields and `r` in its slack fields. -/
private noncomputable def encode (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    Bytes vp.params.m :=
  (bytesEquivFin vp.params.m).symm ⟨packLow (fields vp z r), by
    rw [pow_256, ← totalWidth_fields vp z r]
    exact packLow_lt _ (fields_lt vp z r)⟩

@[simp] private theorem toInt_encode (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    toInt (encode vp z r).toList = packLow (fields vp z r) := by
  rw [encode, bytesEquivFin_symm_toInt]


/-! ## Offsets of the six fields -/

private theorem offset_one (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    totalWidth ((fields vp z r).take 1) = vp.params.hp := by
  simp [fields, totalWidth]

private theorem offset_two (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    totalWidth ((fields vp z r).take 2) = 8 * vp.params.leafIdxBytes := by
  have := hp_le_eight_mul_leafIdxBytes vp.valid
  simp only [fields, totalWidth, List.take_succ_cons, List.take_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, leafSlack]
  omega

private theorem offset_three (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    totalWidth ((fields vp z r).take 3) =
      8 * vp.params.leafIdxBytes + (vp.params.h - vp.params.hp) := by
  have := hp_le_eight_mul_leafIdxBytes vp.valid
  simp only [fields, totalWidth, List.take_succ_cons, List.take_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, leafSlack]
  omega

private theorem offset_four (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    totalWidth ((fields vp z r).take 4) = 8 * vp.params.treeIdxBytes +
      8 * vp.params.leafIdxBytes := by
  have := hp_le_eight_mul_leafIdxBytes vp.valid
  have := sub_le_eight_mul_treeIdxBytes vp.params
  simp only [fields, totalWidth, List.take_succ_cons, List.take_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, leafSlack, treeSlack]
  omega

private theorem offset_five (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    totalWidth ((fields vp z r).take 5) =
      8 * vp.params.m - vp.params.k * vp.params.a := by
  have h := eight_mul_m vp.valid
  have := hp_le_eight_mul_leafIdxBytes vp.valid
  have := sub_le_eight_mul_treeIdxBytes vp.params
  have := ka_le_eight_mul_digestBytes vp.params
  simp only [fields, totalWidth, List.take_succ_cons, List.take_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, leafSlack, treeSlack, mdSlack] at *
  omega

private theorem drop_five (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    packLow ((fields vp z r).drop 5) = packDigits vp.params z.2 := by
  simp [fields, packLow]

/-! ## The encoder is a right inverse with injective slack -/

/-- **The encoder is a right inverse of the decoding.**  Every covering digest is decoded from
the message digest that carries it, at every choice of the slack bits. -/
private theorem coveringDigest_encode (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) (r : Slack vp.params) :
    coveringDigest vp (encode vp z r) = z := by
  have hl := fields_lt vp z r
  have hka := ka_le_eight_mul_digestBytes vp.params
  have hleaf : (splitDigest vp.params (encode vp z r)).idxLeaf.val =
      z.1.val % 2 ^ vp.params.hp := by
    rw [idxLeaf_val_eq vp.valid, toInt_encode]
    have h := packLow_field (fields vp z r) hl 0 vp.params.hp (z.1.val % 2 ^ vp.params.hp)
      (by simp [fields])
    simpa using h
  have htree : (splitDigest vp.params (encode vp z r)).idxTree.val =
      z.1.val / 2 ^ vp.params.hp := by
    rw [idxTree_val_eq, toInt_encode, ← offset_two vp z r]
    exact packLow_field (fields vp z r) hl 2 (vp.params.h - vp.params.hp) _ (by simp [fields])
  refine Prod.ext (Fin.ext ?_) (funext fun i => Fin.ext ?_)
  · rw [coveringDigest_fst_val, hleaf, htree, Nat.div_add_mod']
  · have hai : vp.params.a * (i.val + 1) ≤ vp.params.k * vp.params.a := by
      calc vp.params.a * (i.val + 1) ≤ vp.params.a * vp.params.k :=
            Nat.mul_le_mul_left _ i.isLt
        _ = vp.params.k * vp.params.a := Nat.mul_comm _ _
    have hsplit : 8 * vp.params.m - vp.params.a * (i.val + 1) =
        (8 * vp.params.m - vp.params.k * vp.params.a) +
          vp.params.a * (vp.params.k - 1 - i.val) := by
      have h := eight_mul_m vp.valid
      have hm : vp.params.a * (vp.params.k - 1 - i.val) =
          vp.params.k * vp.params.a - vp.params.a * (i.val + 1) := by
        rw [show vp.params.k - 1 - i.val = vp.params.k - (i.val + 1) by omega,
          Nat.mul_sub, Nat.mul_comm vp.params.a vp.params.k]
      omega
    rw [coveringDigest_snd_val, forsIdx_eq _ _ i.isLt, toInt_encode, hsplit, pow_add,
      ← Nat.div_div_eq_div_mul, ← offset_five vp z r,
      packLow_div_totalWidth_take (fields vp z r) hl 5, drop_five, packDigits_field]


/-- **The slack bits are recoverable.**  Two encodings of the same covering digest at different
slack values differ, so each fiber of the decoding carries an injective copy of the slack. -/
private theorem encode_injective (vp : ValidatedParams)
    (z : KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) :
    Function.Injective (encode vp z) := by
  intro r r' hrr
  have hN : packLow (fields vp z r) = packLow (fields vp z r') := by
    rw [← toInt_encode vp z r, ← toInt_encode vp z r', hrr]
  have hleaf : r.2.2.val = r'.2.2.val := by
    have a1 := packLow_field (fields vp z r) (fields_lt vp z r) 1 (leafSlack vp.params)
      r.2.2.val (by simp [fields])
    have a2 := packLow_field (fields vp z r') (fields_lt vp z r') 1 (leafSlack vp.params)
      r'.2.2.val (by simp [fields])
    rw [offset_one] at a1 a2
    rw [← a1, ← a2, hN]
  have htree : r.2.1.val = r'.2.1.val := by
    have a1 := packLow_field (fields vp z r) (fields_lt vp z r) 3 (treeSlack vp.params)
      r.2.1.val (by simp [fields])
    have a2 := packLow_field (fields vp z r') (fields_lt vp z r') 3 (treeSlack vp.params)
      r'.2.1.val (by simp [fields])
    rw [offset_three] at a1 a2
    rw [← a1, ← a2, hN]
  have hmd : r.1.val = r'.1.val := by
    have a1 := packLow_field (fields vp z r) (fields_lt vp z r) 4 (mdSlack vp.params)
      r.1.val (by simp [fields])
    have a2 := packLow_field (fields vp z r') (fields_lt vp z r') 4 (mdSlack vp.params)
      r'.1.val (by simp [fields])
    rw [offset_four] at a1 a2
    rw [← a1, ← a2, hN]
  exact Prod.ext (Fin.ext hmd) (Prod.ext (Fin.ext htree) (Fin.ext hleaf))

/-! ## The cardinality identity -/

private theorem card_slack (p : Params) :
    Fintype.card (Slack p) = 2 ^ mdSlack p * 2 ^ treeSlack p * 2 ^ leafSlack p := by
  simp [Slack, mul_assoc]

/-- **The bit accounting, as a cardinality.**  An `m`-byte digest has exactly as many values as
a covering digest has, times the number of slack assignments. -/
private theorem card_bytes_eq (vp : ValidatedParams) :
    Fintype.card (Bytes vp.params.m) =
      Fintype.card (KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) *
        Fintype.card (Slack vp.params) := by
  have h := eight_mul_m vp.valid
  have hhp := hp_le_h vp.valid
  have hd : Fintype.card (KeyedHash.Covering.Digest vp.params.h vp.params.a vp.params.k) =
      2 ^ vp.params.h * (2 ^ vp.params.a) ^ vp.params.k := by simp
  rw [card_bytes, pow_256, card_slack, hd, h, ← pow_mul,
    show vp.params.k * vp.params.a + mdSlack vp.params + treeSlack vp.params +
        (vp.params.h - vp.params.hp) + leafSlack vp.params + vp.params.hp =
      vp.params.h + vp.params.a * vp.params.k + mdSlack vp.params + treeSlack vp.params +
        leafSlack vp.params by rw [Nat.mul_comm vp.params.a vp.params.k]; omega]
  simp [pow_add, mul_assoc]


/-! ## Surjectivity with equal fibers -/

open KeyedHash.Covering in
/-- **The FIPS 205 message-digest decoding is surjective with equal fibers.**  Every covering
digest is decoded from exactly `2 ^ (mdSlack + treeSlack + leafSlack)` of the `256 ^ m` message
digests — the assignments of the bits the decoding does not read.  The three slack widths are
`8⌈ka/8⌉ − ka`, `8⌈(h−h')/8⌉ − (h−h')` and `8⌈h/(8d)⌉ − h'`, and they are not all zero at any
FIPS 205 parameter set; what makes the transport exact is that the unread bits form bit fields of
their own, not that there are none of them. -/
theorem card_fiber_coveringDigest (vp : ValidatedParams)
    (z : Digest vp.params.h vp.params.a vp.params.k) :
    (Finset.univ.filter fun d : Bytes vp.params.m => coveringDigest vp d = z).card =
      2 ^ (mdSlack vp.params + treeSlack vp.params + leafSlack vp.params) := by
  rw [card_fiber_eq_of_fiberInj (coveringDigest vp) (encode vp) (coveringDigest_encode vp)
    (encode_injective vp) (card_bytes_eq vp) z, card_slack, ← pow_add, ← pow_add]

open KeyedHash.Covering in
/-- Every covering digest is decoded from some message digest. -/
theorem surjective_coveringDigest (vp : ValidatedParams) :
    Function.Surjective (coveringDigest vp) :=
  surjective_of_fiberInj _ (encode vp) (coveringDigest_encode vp)

/-! ## The transport -/

section Transport

open AnswerTape KeyedHash.Covering

variable (vp : ValidatedParams) [MeasurableSpace (Bytes vp.params.m)]
  [DiscreteMeasurableSpace (Bytes vp.params.m)]

/-- **A uniform `H_msg` answer decodes to a uniform covering digest, event by event.**  The
mass a uniform `m`-byte digest gives the decodings landing in `S` is the mass a uniform
covering digest gives `S`: the decoding is surjective and its fibers all have the same size,
namely the number of slack-bit assignments. -/
theorem evalDist_uniformSample_preimage_coveringDigest
    (S : Set (Digest vp.params.h vp.params.a vp.params.k)) :
    𝒟[($ᵗ (Bytes vp.params.m) : ProbComp (Bytes vp.params.m))] (coveringDigest vp ⁻¹' S) =
      𝒟[($ᵗ (Digest vp.params.h vp.params.a vp.params.k) :
        ProbComp (Digest vp.params.h vp.params.a vp.params.k))] S :=
  evalDist_uniformSample_preimage_eq_of_fiberInj (coveringDigest vp) (encode vp)
    (coveringDigest_encode vp) (encode_injective vp) (card_bytes_eq vp) S

/-- **The decoding pushes the uniform byte measure forward to the uniform digest measure.** -/
theorem map_evalDist_uniformSample_coveringDigest :
    Measure.map (coveringDigest vp)
        𝒟[($ᵗ (Bytes vp.params.m) : ProbComp (Bytes vp.params.m))] =
      𝒟[($ᵗ (Digest vp.params.h vp.params.a vp.params.k) :
        ProbComp (Digest vp.params.h vp.params.a vp.params.k))] := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply Measurable.of_discrete hS]
  exact evalDist_uniformSample_preimage_coveringDigest vp S

/-- **The tape transport.**  A tuple of `q` independent uniform `m`-byte digests, decoded
coordinatewise, is a tuple of `q` independent uniform covering digests: every event of the
abstract tape pulls back to the event about decoded digests with the same mass. -/
theorem evalDist_answerTape_preimage_coveringDigest (q : ℕ)
    (E : Set (Fin q → Digest vp.params.h vp.params.a vp.params.k)) :
    𝒟[answerTape (Bytes vp.params.m) q] ((fun w i => coveringDigest vp (w i)) ⁻¹' E) =
      𝒟[answerTape (Digest vp.params.h vp.params.a vp.params.k) q] E := by
  rw [← Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    evalDist_answerTape, Measure.pi_map_pi fun _ => Measurable.of_discrete.aemeasurable,
    evalDist_answerTape]
  simp only [map_evalDist_uniformSample_coveringDigest]

/-- **The separated interleaved-target bound, on decoded FIPS 205 digests.**  The abstract
coverage bound of `KeyedHash.Covering` applies verbatim to the event stated on the covering
digests decoded from a tape of independent uniform `H_msg` answers. -/
theorem evalDist_answerTape_tapeCoveredSplit_coveringDigest_le (q qh qs : ℕ)
    (tgt : Fin qh → Fin q) (cov : Fin qs → Fin q) (hdisj : ∀ n j, tgt n ≠ cov j) :
    𝒟[answerTape (Bytes vp.params.m) q]
        {w | TapeCoveredSplit vp.params.h vp.params.a vp.params.k q qh qs tgt cov
          fun i => coveringDigest vp (w i)} ≤
      ∑ c : Fin qh × (Fin vp.params.k → Fin qs),
        (((2 : ℝ≥0∞) ^ vp.params.h)⁻¹) ^ (Finset.univ.image c.2).card *
          (((2 : ℝ≥0∞) ^ vp.params.a)⁻¹) ^ vp.params.k :=
  (evalDist_answerTape_preimage_coveringDigest vp q _).trans_le
    (evalDist_answerTape_tapeCoveredSplit_le _ _ _ q qh qs tgt cov hdisj)

/-- **The separated interleaved-target bound in closed form, on decoded FIPS 205 digests.** -/
theorem evalDist_answerTape_tapeCoveredSplit_coveringDigest_le_closedForm (q qh qs : ℕ)
    (tgt : Fin qh → Fin q) (cov : Fin qs → Fin q) (hdisj : ∀ n j, tgt n ≠ cov j) :
    𝒟[answerTape (Bytes vp.params.m) q]
        {w | TapeCoveredSplit vp.params.h vp.params.a vp.params.k q qh qs tgt cov
          fun i => coveringDigest vp (w i)} ≤
      ∑ r ∈ Finset.range (vp.params.k + 1),
        ((qh * qs.choose r *
            (Finset.univ.filter fun s : Fin vp.params.k → Fin r =>
              Function.Surjective s).card : ℕ) : ℝ≥0∞) *
          ((((2 : ℝ≥0∞) ^ vp.params.h)⁻¹) ^ r *
            (((2 : ℝ≥0∞) ^ vp.params.a)⁻¹) ^ vp.params.k) :=
  (evalDist_answerTape_tapeCoveredSplit_coveringDigest_le vp q qh qs tgt cov hdisj).trans
    (sum_pow_card_image_eq_closedForm _ _ _ qh qs).le

end Transport

end SLHDSA.DigestTransport
