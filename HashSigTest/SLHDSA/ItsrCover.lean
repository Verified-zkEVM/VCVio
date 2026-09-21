/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ItsrCover
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering

/-!
# The interleaved-target per-step limitation witness

`SLHDSA.Security.evalDist_romRunFull_itsrCovered_le_of_fresh_bound` bounds the interleaved-target
disjunct by `q * ε` for any `ε` bounding the fresh-answer firing mass of
`SLHDSA.Security.ItsrCacheCovered`.  `le_of_uniform_covering_bound` is the witness that no such
`ε` is small in the abstract covering model of `KeyedHash.Covering`: every `ε` valid uniformly
over the lists of at most `qs` logged digests is at least `⌊qs / 2 ^ a⌋ / 2 ^ h`.  That
quantification is the abstract *counterpart* of the engine's hypothesis, which quantifies over
the caches of the SLH-DSA run that are not yet covering; the two range over different types, and
nothing here connects them.

The construction is the saturating list: `⌊qs / 2 ^ a⌋` hypertree leaves, each carrying all
`2 ^ a` constant-digit digests, cover every digest at those leaves, and the list respects the
signing budget because it has `⌊qs / 2 ^ a⌋ * 2 ^ a ≤ qs` entries.  It is a legitimate
not-yet-firing state: `KeyedHash.Covering.not_covered_satList_erase` shows no entry of it is
covered by the others.  At the FIPS 205 parameter sets `⌊qs / 2 ^ a⌋ / 2 ^ h` times a
public-hash budget exceeds one by more than fifty bits, so the conclusion of that theorem is
vacuous at every satisfiable `ε`.

This is a limitation of the *formulation*, not of the counting.  The upper bound
`KeyedHash.Covering.evalDist_covered_le` and the lower bound
`KeyedHash.Covering.evalDist_covered_satList_ge` coincide at the saturating list, where
`KeyedHash.Covering.evalDist_covered_satList_eq` computes the mass exactly, so a tighter
fixed-list estimate does not exist.  What the small figures associated with this hop are about is
*uniform* logged digests; the fresh-answer engine sees adversarially arranged ones.

## Scope

* The witness is stated in the abstract model.  A saturating *cache* of the SLH-DSA run would
  additionally need the byte-level transport — that a digest's hypertree leaf and its `md`
  digits are surjective images with equal fibres — which is proved nowhere, so the witness does
  not exhibit a concrete `SLHDSA.Security.ItsrCacheCovered`-avoiding cache.
* No parameter set is substituted.  The statement is the general inequality; the arithmetic that
  turns it into a bit count is not formalised.
* Nothing here is runnable: every statement is an `ℝ≥0∞` inequality, so the file has no `main`
  and is built by the `HashSigTest` library glob alone.
* Nothing here says the interleaved-target term is large.  It says the *per-step* formulation
  cannot bound it; a product-style argument over a tuple of fresh answers is untouched by this.

## Labels

One declaration: `le_of_uniform_covering_bound`.
-/

public section

namespace SLHDSA.ItsrCoverTest

open MeasureTheory KeyedHash.Covering
open scoped ENNReal

/-- **No uniform per-step covering bound is small.**  An `ε` bounding the covering probability of
a uniform digest uniformly over every list of at most `qs` logged digests — the abstract
counterpart of what the fresh-answer engine's hypothesis in
`SLHDSA.Security.evalDist_romRunFull_itsrCovered_le_of_fresh_bound` demands, the two quantifying
over different types — is at least `⌊qs / 2 ^ a⌋ / 2 ^ h`. -/
theorem le_of_uniform_covering_bound (h a k qs : ℕ) (hqs : qs / 2 ^ a ≤ 2 ^ h) (ε : ℝ≥0∞)
    (hε : ∀ L : Finset (Digest h a k), L.card ≤ qs →
      letI : MeasurableSpace (Digest h a k) := ⊤
      𝒟[($ᵗ (Digest h a k) : ProbComp (Digest h a k))] {z | Covered h a k L z} ≤ ε) :
    ((qs / 2 ^ a : ℕ) : ℝ≥0∞) / 2 ^ h ≤ ε := by
  classical
  let _ : MeasurableSpace (Digest h a k) := ⊤
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (show qs / 2 ^ a ≤ (Finset.univ : Finset (Fin (2 ^ h))).card by simpa using hqs)
  refine le_trans (le_of_eq ?_) ((evalDist_covered_satList_ge h a k S).trans
    (hε _ ((card_satList_le h a k S).trans ?_)))
  · rw [hScard]
  · rw [hScard]
    exact Nat.div_mul_le_self _ _

end SLHDSA.ItsrCoverTest
