/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.RomDescent
public import HashSig.SLHDSA.Security.RomFresh

/-!
# The interleaved-target disjunct as a cache predicate

`HashSig.SLHDSA.Security.RomDescent`'s `ItsrCovered` is the third disjunct of the bad-event
bridge: every FORS coordinate the forgery's `H_msg` digest selects is also selected by the digest
of some logged signature.  It is a predicate of the transcript *and* the cache, so the
fresh-answer engine of `HashSig.SLHDSA.Security.RomFresh` — which bounds the mass of a predicate
of the cache alone — does not apply to it.  `ItsrCacheCovered qs` is such a cache predicate, and
`itsrCacheCovered_of_itsrCovered` shows the disjunct implies it once the forgery's message is
fresh and the log has length at most `qs`.  Freshness is what supplies the distinctness clause:
the logged `H_msg` points are then existentially quantified as a list of at most `qs` points
none of which carries the forger's message, under any randomizer, which is what a covering
argument counts against.

`forall_mem_hmsgIndices_iff` and `mem_hmsgIndices_coord` certify what the coverage event says:
after unfolding `hmsgIndices`, it is "the same hypertree leaf, the same `i`-th base-`2 ^ a` digit
of `md`, for each of the `k` FORS trees" — the shape
`VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.Covering` computes with.

## Scope

**The run-level statement here does not bound the interleaved-target term.**
`evalDist_romRunFull_itsrCovered_le_of_fresh_bound` takes its per-step bound `ε` as a hypothesis,
and no useful value is known to satisfy it.  The engine's per-step hypothesis asks for one `ε`
uniform over *every* cache at which `ItsrCacheCovered qs` does not yet hold, and the logged
digests of such a cache are chosen by the adversary, not sampled uniformly.  What is proved, and
where it stops:

* *In the abstract model.*  Any `ε` uniform over the lists of at most `qs` digests of
  `KeyedHash.Covering.Digest` is at least `⌊qs / 2 ^ a⌋ / 2 ^ h`; this is
  `HashSigTest.SLHDSA.ItsrCover.le_of_uniform_covering_bound`, and the witness is
  `KeyedHash.Covering.satList` over `⌊qs / 2 ^ a⌋` leaves, which respects the budget
  (`KeyedHash.Covering.card_satList_le`), covers every digest at one of those leaves
  (`KeyedHash.Covering.covered_satList`) and is itself not covering
  (`KeyedHash.Covering.not_covered_satList_erase`), hence is a legitimate not-yet-firing state.
  The loss is the formulation's exact worst case and not slack in the counting:
  `KeyedHash.Covering.evalDist_covered_satList_eq` computes the mass at the witness, and it is
  the value `KeyedHash.Covering.evalDist_covered_le` takes there.
* *Transport to `ItsrCacheCovered` is not proved.*  It needs the map from a real digest to its
  hypertree leaf and its `md` digits to be surjective with equal fibres, which is proved nowhere,
  so no cache of the SLH-DSA run is exhibited at which the covering mass is large.  The lower
  bound above is a statement about `KeyedHash.Covering.Digest`, not about this module's
  predicate.
* *The arithmetic is not formalised.*  That `q * ⌊qs / 2 ^ a⌋ / 2 ^ h` exceeds one, by upwards of
  fifty bits at the FIPS 205 parameter sets, is a calculation on the parameters that no
  declaration here or in `HashSigTest.SLHDSA.ItsrCover` performs; no parameter set is substituted
  anywhere.
* The missing ingredient for a bound is a product-style argument over a *tuple* of fresh answers:
  the logged digests really are uniform, so covering all `k` coordinates is a product of `k`
  events, but expressing that needs the answers of several queries at once, which a single-step
  bound cannot express.  Nothing of that shape exists in this repository.
* `HasSignQueryBound` is not related to `HasHashQueryBound` here.  That every signing query costs
  at least one public-hash query, hence `qs ≤ q`, is true of `signInternalM` and not proved, and
  it is not one induction away: no single distribution currently carries both a charge and a log,
  since the counted experiment returns only the win bit and `romRunFull` is uninstrumented, so a
  joint counted-and-logged run has to be built first, with projection lemmas to each of the two
  existing runs.
* Nothing here is quantum: the oracle is a classical lazily-sampled table.

## Labels

Seven declarations.

*The coordinate form of coverage*: `forall_mem_hmsgIndices_iff`, `mem_hmsgIndices_coord`.

*The cache predicate*: `ItsrCacheCovered`, `not_itsrCacheCovered_empty`,
`itsrCacheCovered_of_itsrCovered`.

*The logged digests and the run*: `encard_loggedDigests_le_of_hasSignQueryBound`,
`evalDist_romRunFull_itsrCovered_le_of_fresh_bound`.

## References

- NIST FIPS 205, §9, Algorithms 19--20
- Hülsing and Kudinov, "Recovering the Tight Security Proof of SPHINCS+"
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec MeasureTheory SignatureAlg CanonicalGames
open scoped ENNReal

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The coordinate form of coverage -/

section Coords

variable [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]

/-- Coverage of the index list is coverage of each of the `k` FORS coordinates: a logged digest at
the same hypertree leaf whose `i`-th base-`2 ^ a` digit of `md` agrees. -/
theorem forall_mem_hmsgIndices_iff (digest : Bytes vp.params.m)
    (Q : HmsgIndex vp.params → Prop) :
    (∀ idx ∈ hmsgIndices vp.params digest, Q idx) ↔
      ∀ i : Fin vp.params.k, Q ⟨(splitDigest vp.params digest).idxTree,
        (splitDigest vp.params digest).idxLeaf, i,
        ⟨forsIdx vp.params (splitDigest vp.params digest).md.toList i.val,
          forsIdx_lt vp.params _ _⟩⟩ := by
  constructor
  · intro hq i
    exact hq _ ((mem_hmsgIndices vp.params digest _).mpr ⟨rfl, rfl, rfl⟩)
  · intro hq idx hidx
    obtain ⟨h1, h2, h3⟩ := (mem_hmsgIndices vp.params digest idx).mp hidx
    have hidx' : idx = ⟨(splitDigest vp.params digest).idxTree,
        (splitDigest vp.params digest).idxLeaf, idx.tree,
        ⟨forsIdx vp.params (splitDigest vp.params digest).md.toList idx.tree.val,
          forsIdx_lt vp.params _ _⟩⟩ := by
      obtain ⟨t, l, i, f⟩ := idx
      simp only at h1 h2 h3
      subst h1; subst h2
      simp only [HmsgIndex.mk.injEq, true_and]
      exact Fin.ext h3
    rw [hidx']
    exact hq idx.tree

/-- Membership of a coordinate in a *logged* digest's index list, spelled out: the same hypertree
leaf and the same base-`2 ^ a` digit. -/
theorem mem_hmsgIndices_coord (digest digest' : Bytes vp.params.m) (i : Fin vp.params.k) :
    (⟨(splitDigest vp.params digest).idxTree, (splitDigest vp.params digest).idxLeaf, i,
      ⟨forsIdx vp.params (splitDigest vp.params digest).md.toList i.val,
        forsIdx_lt vp.params _ _⟩⟩ : HmsgIndex vp.params) ∈ hmsgIndices vp.params digest' ↔
      ((splitDigest vp.params digest).idxTree = (splitDigest vp.params digest').idxTree ∧
        (splitDigest vp.params digest).idxLeaf = (splitDigest vp.params digest').idxLeaf ∧
        forsIdx vp.params (splitDigest vp.params digest).md.toList i.val =
          forsIdx vp.params (splitDigest vp.params digest').md.toList i.val) := by
  rw [mem_hmsgIndices]

end Coords

/-! ## The cache predicate -/

/-- **Interleaved-target coverage as a cache predicate.**  Some cached `H_msg` entry's digest has
every one of its `k` FORS coordinates covered by the digest of one of at most `qs` cached `H_msg`
entries sharing the public key, none of them at that entry's own message under any randomizer. -/
def ItsrCacheCovered (qs : ℕ) (c : PublicHash.Cache core) : Prop :=
  ∃ (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y) (msg : List Byte)
      (digest : Bytes vp.params.m) (L : List (core.Y × List Byte)),
    c (.hmsg r pkSeed pkRoot (emptyContextMessage msg)) = some digest ∧
    L.length ≤ qs ∧ (∀ p ∈ L, p.2 ≠ msg) ∧
    ∀ idx ∈ hmsgIndices vp.params digest, ∃ p ∈ L, ∃ digest',
      c (.hmsg p.1 pkSeed pkRoot (emptyContextMessage p.2)) = some digest' ∧
        idx ∈ hmsgIndices vp.params digest'

/-- The empty cache is not covering. -/
theorem not_itsrCacheCovered_empty (qs : ℕ) : ¬ ItsrCacheCovered core qs ∅ := by
  rintro ⟨r, s, root, msg, digest, L, hc, -, -, -⟩
  simp at hc

/-- **Freshness reduces the interleaved-target event to a cache predicate.**  A transcript whose
forgery's digest is covered by the logged digests and whose message was never signed has a cache
satisfying `ItsrCacheCovered qs`, provided the signing log has length at most `qs`.

Freshness supplies the distinctness clause: a logged pair at the forger's message, under any
randomizer, would exhibit that message in the log. -/
theorem itsrCacheCovered_of_itsrCovered (qs : ℕ) (o : RomOutcome vp core)
    (c : PublicHash.Cache core) (hcov : ItsrCovered o c)
    (hfresh : o.msg ∉ o.log.map (fun e => e.1)) (hlen : o.log.length ≤ qs) :
    ItsrCacheCovered core qs c := by
  obtain ⟨digest, hd, hcov⟩ := hcov
  refine ⟨o.sig.randomness, o.pk.pkSeed, o.pk.pkRoot, o.msg, digest,
    o.log.map (fun e => (e.2.randomness, e.1)), hd, by simpa using hlen, ?_, ?_⟩
  · rintro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    intro hcon
    exact hfresh (List.mem_map.mpr ⟨e, he, hcon⟩)
  · intro idx hidx
    obtain ⟨e, he, digest', hd', hi'⟩ := hcov idx hidx
    exact ⟨(e.2.randomness, e.1), List.mem_map.mpr ⟨e, he, rfl⟩, digest', hd', hi'⟩

/-! ## The logged digests and the run -/

section Run

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

local notation "romSpec" => unifSpec + publicHashSpec core

/-- The signing budget bounds the number of distinct logged digests: every logged digest is the
cache value at the `H_msg` point of some log entry, so the set of logged digests is the image of
a list of length at most `qs`. -/
theorem encard_loggedDigests_le_of_hasSignQueryBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (qs : ℕ)
    (hqs : HasSignQueryBound core adv qs)
    {z : RomOutcome vp core × PublicHash.Cache core} (hz : z ∈ support (romRunFull core adv)) :
    {d : Bytes vp.params.m | ∃ e ∈ z.1.log, LoggedDigest z.1 z.2 e d}.encard ≤ (qs : ℕ∞) := by
  classical
  have hsub : {d : Bytes vp.params.m | ∃ e ∈ z.1.log, LoggedDigest z.1 z.2 e d} ⊆
      (fun e => (z.2 (.hmsg e.2.randomness z.1.pk.pkSeed z.1.pk.pkRoot
        (emptyContextMessage e.1))).getD default) '' {e | e ∈ z.1.log} := by
    rintro d ⟨e, he, hd⟩
    exact ⟨e, he, by rw [LoggedDigest] at hd; simp [hd]⟩
  refine ((Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)).trans ?_
  rw [show {e | e ∈ z.1.log} = (z.1.log.toFinset : Set _) from by ext x; simp,
    Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast le_trans (List.toFinset_card_le _)
    (by simpa using length_map_fst_le_of_hasSignQueryBound core adv qs hqs hz)

/-- **The interleaved-target disjunct through the fresh-answer engine.**  Under a public-hash
budget `q` and a signing budget `qs`, the disjunct has mass at most `q * ε` for any `ε` bounding
the fresh-answer firing mass of `ItsrCacheCovered qs`.

**No useful `ε` is known to satisfy that hypothesis.**  It quantifies over every cache at which
`ItsrCacheCovered qs` does not yet hold, and the logged digests of such a cache are the
adversary's to arrange.  In the abstract covering model of `KeyedHash.Covering` every bound
uniform over the lists of at most `qs` digests is at least `⌊qs / 2 ^ a⌋ / 2 ^ h`
(`KeyedHash.Covering.evalDist_covered_satList_ge`); carrying that lower bound over to this
predicate needs a byte-level transport that is not proved, and the arithmetic from the ratio to a
bit count is not formalised either.  The statement is the shape the term has, not a bound on it;
see this module's scope. -/
theorem evalDist_romRunFull_itsrCovered_le_of_fresh_bound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q qs : ℕ)
    (hq : HasHashQueryBound core adv q) (hqs : HasSignQueryBound core adv qs)
    (ε : ℝ≥0∞) (hε : ε ≠ ⊤)
    (hfresh : ∀ (t : (publicHashSpec core).Domain) (c : PublicHash.Cache core),
      ¬ ItsrCacheCovered core qs c → c t = none →
      (letI : MeasurableSpace ((publicHashSpec core).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core).Range t : ProbComp _)]
          {u | ItsrCacheCovered core qs (c.cacheQuery t u)} ≤ ε)) :
    (letI : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤;
      𝒟[romRunFull core adv]
        {z | ItsrCovered z.1 z.2 ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)} ≤ (q : ℝ≥0∞) * ε) := by
  let _ : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤
  have hae : ∀ᵐ z ∂𝒟[romRunFull core adv],
      z ∈ {z : RomOutcome vp core × PublicHash.Cache core |
          ItsrCovered z.1 z.2 ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)} →
        z ∈ {z : RomOutcome vp core × PublicHash.Cache core |
          ItsrCacheCovered core qs z.2} :=
    evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      fun z hz hp => itsrCacheCovered_of_itsrCovered core qs z.1 z.2 hp.1 hp.2
        (by simpa using length_map_fst_le_of_hasSignQueryBound core adv qs hqs hz)
  refine (measure_mono_ae hae).trans ?_
  exact evalDist_romRunFull_setOf_le_of_fresh_bound core (ItsrCacheCovered core qs)
    (not_itsrCacheCovered_empty core qs) ε hε hfresh adv q hq

end Run

end SLHDSA.Security
