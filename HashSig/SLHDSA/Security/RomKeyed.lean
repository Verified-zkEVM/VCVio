/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomDescent
public import HashSig.SLHDSA.Security.RomFresh

/-!
# The linear same-key collision bound for the SLH-DSA random-oracle run

A same-key collision on a settled honest input (`KeyCollision`) is the same-address target
collision of `HashSig.SLHDSA.Security.RomDescent` with the honest side abstracted to a relation
`Honest` between a cache and a query.  This module bounds the mass of that event over a run of
the shared lazy public-hash oracle, and the bound is **linear** in the public-hash query budget:

  `r * q / Nat.card core.Y + B`.

The two constants are supplied, not derived.

* `r` is a *separator bound*: the caller exhibits a map `ρ` from public-hash queries to `Fin r`
  which, at each `thash` key, separates the settled honest inputs — two settled honest inputs at
  one key with the same `ρ`-value are equal.  At `r = 1` this says a key carries at most one
  settled honest input.  It is not injectivity of the address encoding: the encoding is not
  assumed injective anywhere here, and `ρ` is free to be constant on keys the honest parties
  never use.  The separator hypothesis gives the counting lemma `encard_honestPairs_le`, whose
  content is `Σ_K n_K · h_K ≤ r · Σ_K n_K`, and it is the whole source of the linearity: the
  charge a fresh answer pays is the *increment* of the key-weighted potential
  `keyedPotential`, not a flat per-step `ε`.
* `B` is an abstract budget for an abstract auxiliary event `Aux`, carried by an abstract
  monotone potential `Ψ`.  Nothing is proved about `Aux` here; it is a parameter of the main
  theorem and of the SLH-DSA consumable, discharged by the caller.

The auxiliary event is a parameter rather than a definition because the step bound needs a
fresh answer not to *create* honest entries retroactively (`hhonest`), and the one candidate
definition of that failure examined here has mass one.  A cache is a table of query-answer pairs
and records no attribution: an entry the signer computed and an entry whose value the adversary
guessed before the signer reached it are the same entry.  The candidate is the prefix-quantified
one — there is a sub-cache with the query unset for which the entry is honest once the query is
recorded and not before — and quantifying the prefix over *arbitrary* sub-caches makes it fire
on every cache recording a query an honest party makes, since a sub-cache may drop exactly the
entry the honest reading needs.  `Aux` is therefore a parameter, discharged by the caller; being
a predicate of the cache is part of its type, and it need only over-approximate the failure of
the step condition rather than express it.

The engine is `OracleComp.evalDist_apply_setOf_and_le_of_potential`; the per-step uniform charge
is `SampleableType.evalDist_uniformSample_le_encard_div`; the budget side condition is discharged
by `enncard_le_of_hasHashQueryBound` of `HashSig.SLHDSA.Security.RomFresh`.  The SLH-DSA
instantiation takes `Honest` to be `HonestSome`, the honest-entry relation of
`HashSig.SLHDSA.Security.RomDescent` closed over the transcript, and
`evalDist_romRunFull_targetCollision_le` is the consumable statement.

## Scope

* **For the SLH-DSA honest-entry relation `HonestSome` there is no constant `r` independent of
  the cache, so the two theorems stated at that relation carry no information.**  `HonestSome`
  closes `HonestEntry` over the transcript; `RomOutcome` is a plain structure carrying no
  invariant, so the existential ranges over every key pair rather than over the run's own; and
  `HonestEntry.forsLeaf` has no premises, so every secret seed contributes a settled honest
  entry at its own FORS leaf key.  The separator hypothesis `hρ` then forces `r` to be at least
  the number of seeds the FORS leaf secret separates, which exceeds `Nat.card core.Y` at the
  FIPS 205 parameter sets, so `r * q / Nat.card core.Y` is at least `1` already at `q = 1`.
  `HashSigTest.SLHDSA.RomKeyed` carries the witnesses.
* **The hypothesis of the trivial-auxiliary corollary is false for that same relation.**
  `hstable` asks that no fresh answer create an honest entry, and caching a WOTS+ chain entry
  makes the chain value one step further an honest entry, with the reading that certifies it
  absent before that entry.  So `evalDist_run_setOf_keyCollision_le` and
  `evalDist_romRunFull_keyCollision_le` are sound but not instantiable at `HonestSome`.
* **The event the SLH-DSA theorems bound is a lossy over-approximation of the event the bridge
  produces.**  `TargetCollision` of `HashSig.SLHDSA.Security.RomDescent` is diagonal in the
  transcript: the honest side and the run are one and the same `o`.
  `keyCollision_of_targetCollision` closes that transcript existentially, which is the same loss
  as the one above, so the weakness of the bound and the coarseness of the event have one cause.
* The fix lies in the honest relation, not in the arithmetic: the relation has to pin the run's
  own secret key rather than quantify a transcript.  Key generation precedes the adversary, so
  the engine can instead be applied to the residual run after key generation with the sampled
  secret key fixed, which the engine permits because it tolerates a non-empty starting state and
  a non-zero potential there.
* The bound is stated with the denominator `Nat.card core.Y`.  Identifying that cardinality with
  a concrete power of two for a FIPS 205 parameter set is a separate step and is not done here.
* The separator hypothesis `hρ` is not discharged from the repository's per-role encoded
  distinctness lemmas.  Supplying `r` and `ρ` for the SLH-DSA honest-entry relation, and proving
  `hρ` from the address bookkeeping, is left to the caller.
* Nothing is proved about the auxiliary event `Aux`, its potential `Ψ`, or its budget `B`.  A
  caller that instantiates `Aux := fun _ => False` gets `B = 0` and the bound
  `r * q / Nat.card core.Y`, at the price of the hypothesis `hstable`: no fresh answer ever
  creates an honest entry.  That is the shape of `evalDist_run_setOf_keyCollision_le` and
  `evalDist_romRunFull_keyCollision_le`.
* `honestPairs` sees only `thash` entries, so an `H_msg` answer pays no charge; the step bound
  at such a query is that the collision half of its bad set is empty (`encard_badSetAt_le`).
* The event bounded is a predicate of the final cache.  Relating it to the winning event of the
  forgery game is the job of the bridge, not of this module.
* The measurable-space instances on the sampled and outcome types are pinned to `⊤` by `letI`
  inside the statements, inherited from the engine.  A consumer must fix `⊤` as well.
* Nothing here is quantum: the oracle is a classical lazily-sampled table and `q` is a classical
  query count.

## Labels

Twenty-nine declarations.

*Settled honest entries, the key-weighted potential and the collision*: `SettledHonest`,
`keyDom`, `cachedAt`, `honestAt`, `honestPairs`, `keyedPotential`, `KeyCollision`.

*Per-key counting*: `thash_injective_right`, `encard_keyDom_and`, `encard_honestAt`,
`encard_cachedAt`, `encard_vals_le`.

*Monotonicity*: `honestPairs_mono`, `keyedPotential_mono`.

*The budget clause*: `encard_honestPairs_le`.

*The SLH-DSA honest-entry relation*: `HonestSome`, `honestSome_mono`,
`keyCollision_of_targetCollision`.

*The charged step*: `newPairs`, `encard_newPairs_add_le`, `encard_badSet_le`, `newPairsAt`,
`encard_newPairsAt_add_le`, `keyedPotential_add_le`, `encard_badSetAt_le`.

*The bound along a run*: `evalDist_run_setOf_keyCollision_aux_le`,
`evalDist_run_setOf_keyCollision_le`, `evalDist_romRunFull_keyCollision_le`,
`evalDist_romRunFull_targetCollision_le`.

## References

- NIST FIPS 205, §6--§9
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec MeasureTheory SignatureAlg
open scoped ENNReal

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## Settled honest entries, the key-weighted potential and the collision -/

/-- A settled honest query: cached, and honest for the cache it is read against. -/
@[expose] def SettledHonest (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain) : Prop :=
  (c t).isSome ∧ Honest c t

/-- The `thash` queries at one tweakable-hash key: one public seed and one encoded address. -/
def keyDom (p : core.PkSeed) (k : core.AdrsKey) : Set ((publicHashSpec core).Domain) :=
  {a | ∃ xs, a = .thash p k xs}

/-- The cached `thash` queries at one key. -/
def cachedAt (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) :
    Set ((publicHashSpec core).Domain) :=
  {a | a ∈ keyDom p k ∧ (c a).isSome}

/-- The settled honest `thash` queries at one key. -/
def honestAt (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) :
    Set ((publicHashSpec core).Domain) :=
  {a | a ∈ keyDom p k ∧ SettledHonest Honest c a}

/-- Pairs of a cached `thash` entry and a settled honest `thash` entry at the same key.  Its
cardinality is `Σ_K n_K · h_K`, with `n_K` the number of cached `thash` entries at key `K` and
`h_K` the number of settled honest ones. -/
def honestPairs (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) :
    Set ((publicHashSpec core).Domain × (publicHashSpec core).Domain) :=
  {pq | (∃ p k, pq.1 ∈ keyDom p k ∧ pq.2 ∈ keyDom p k) ∧ (c pq.1).isSome ∧
    SettledHonest Honest c pq.2}

/-- **The key-weighted potential.**  The cardinality of `honestPairs` over the size of the
tweakable-hash range: `Σ_K n_K(c) · h_K(c) / |core.Y|`. -/
noncomputable def keyedPotential
    (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) : ℝ≥0∞ :=
  ((honestPairs Honest c).encard : ℝ≥0∞) / Nat.card core.Y

/-- **A same-key collision on a settled honest input.**  Two cache entries at one `thash` key
with equal answers and different inputs, the first of which is honest for the cache. -/
@[expose] def KeyCollision (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) : Prop :=
  ∃ (p : core.PkSeed) (k : core.AdrsKey) (xs ys : List core.Y) (v : core.Y),
    Honest c (.thash p k xs) ∧ xs ≠ ys ∧
    c (.thash p k xs) = some v ∧ c (.thash p k ys) = some v

/-! ## Per-key counting -/

/-- A `thash` query determines its input list, the public seed and key being fixed. -/
theorem thash_injective_right (p : core.PkSeed) (k : core.AdrsKey) :
    Function.Injective
      (fun ys => (PublicHashQuery.thash p k ys : (publicHashSpec core).Domain)) := by
  intro ys ys' h
  simpa using h

/-- A set of `thash` queries at one key is the image of the set of input lists it names. -/
theorem encard_keyDom_and (P : (publicHashSpec core).Domain → Prop) (p : core.PkSeed)
    (k : core.AdrsKey) :
    {a | a ∈ keyDom p k ∧ P a}.encard = {ys : List core.Y | P (.thash p k ys)}.encard := by
  rw [← (thash_injective_right p k).injOn.encard_image]
  congr 1
  ext a
  simp only [keyDom, Set.mem_ofPred_eq, Set.mem_image]
  exact ⟨fun ⟨⟨ys, hys⟩, hs⟩ => ⟨ys, hys ▸ hs, hys.symm⟩,
    fun ⟨ys, hs, hys⟩ => ⟨⟨ys, hys.symm⟩, hys ▸ hs⟩⟩

/-- `honestAt` is the image of the settled honest input lists. -/
theorem encard_honestAt
    (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) :
    (honestAt Honest c p k).encard =
      {ys : List core.Y | SettledHonest Honest c (.thash p k ys)}.encard :=
  encard_keyDom_and _ p k

/-- `cachedAt` is the image of the cached input lists. -/
theorem encard_cachedAt (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) :
    (cachedAt c p k).encard = {ys : List core.Y | (c (.thash p k ys)).isSome}.encard :=
  encard_keyDom_and _ p k

/-- The answers a set of input lists is cached at has at most as many elements as the set. -/
theorem encard_vals_le (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey)
    (S : Set (List core.Y)) :
    {v : core.Y | ∃ ys ∈ S, c (.thash p k ys) = some v}.encard ≤ S.encard := by
  refine le_trans (le_of_eq (Set.InjOn.encard_image (f := Option.some)
      (Option.some_injective core.Y).injOn).symm) ?_
  refine le_trans (Set.encard_le_encard
    (?_ : _ ⊆ (fun ys => c (PublicHashQuery.thash p k ys)) '' S)) (Set.encard_image_le _ _)
  rintro _ ⟨v, ⟨ys, hys, hc⟩, rfl⟩
  exact ⟨ys, hys, hc⟩

/-! ## Monotonicity -/

/-- `honestPairs` grows with the cache, for a cache-monotone honest-entry relation. -/
theorem honestPairs_mono
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    {c c' : PublicHash.Cache core} (h : c ≤ c') :
    honestPairs Honest c ⊆ honestPairs Honest c' := by
  rintro ⟨a, b⟩ ⟨hkey, ha, hb, hh⟩
  exact ⟨hkey, QueryCache.isSome_mono h ha, QueryCache.isSome_mono h hb, hmonoH h b hh⟩

/-- The key-weighted potential never decreases along a cache extension. -/
theorem keyedPotential_mono
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    {c c' : PublicHash.Cache core} (h : c ≤ c') :
    keyedPotential Honest c ≤ keyedPotential Honest c' :=
  ENNReal.div_le_div_right (by exact_mod_cast Set.encard_le_encard (honestPairs_mono hmonoH h)) _

/-! ## The budget clause -/

/-- **The separator hypothesis makes the key-weighted count linear.**  A map `ρ` to `Fin r` that
separates the settled honest inputs at every key bounds `Σ_K n_K · h_K` by `r` times the cache
size. -/
theorem encard_honestPairs_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest Honest c (.thash p k xs) → SettledHonest Honest c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (c : PublicHash.Cache core) :
    (honestPairs Honest c).encard ≤ (r : ℕ∞) * c.toSet.encard := by
  classical
  have hinj : Set.InjOn (fun pq => (pq.1, ρ pq.2)) (honestPairs Honest c) := by
    rintro ⟨a, b⟩ ⟨⟨p, k, ⟨xs, rfl⟩, ⟨ys, rfl⟩⟩, ha, hb⟩ ⟨a', b'⟩
      ⟨⟨p', k', ⟨xs', rfl⟩, ⟨ys', rfl⟩⟩, ha', hb'⟩ heq
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    obtain ⟨rfl, rfl, rfl⟩ : p = p' ∧ k = k' ∧ xs = xs' := by simpa using h1
    simp [hρ c p k ys ys' hb hb' h2]
  have hsub : (fun pq => (pq.1, ρ pq.2)) '' honestPairs Honest c ⊆
      (Sigma.fst '' c.toSet) ×ˢ (Set.univ : Set (Fin r)) := by
    rintro ⟨a, i⟩ ⟨⟨a', b⟩, ⟨-, ha, -⟩, heq⟩
    obtain ⟨rfl, -⟩ := Prod.mk.inj heq
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp ha
    exact ⟨⟨⟨a', u⟩, hu, rfl⟩, trivial⟩
  calc (honestPairs Honest c).encard
      = ((fun pq => (pq.1, ρ pq.2)) '' honestPairs Honest c).encard := hinj.encard_image.symm
    _ ≤ ((Sigma.fst '' c.toSet) ×ˢ (Set.univ : Set (Fin r))).encard := Set.encard_le_encard hsub
    _ = (Sigma.fst '' c.toSet).encard * (Set.univ : Set (Fin r)).encard := Set.encard_prod
    _ ≤ c.toSet.encard * (r : ℕ∞) := by
        gcongr
        · exact Set.encard_image_le _ _
        · simp [Set.encard_univ]
    _ = (r : ℕ∞) * c.toSet.encard := mul_comm _ _

/-! ## The SLH-DSA honest-entry relation -/

/-- The honest-entry relation of `HashSig.SLHDSA.Security.RomDescent`, closed over the transcript
so that it is a relation between a cache and a query. -/
@[expose] def HonestSome (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain) : Prop :=
  ∃ o : RomOutcome vp core, HonestEntry o c t

/-- `HonestSome` is monotone in the cache. -/
theorem honestSome_mono {c c' : PublicHash.Cache core} (h : c ≤ c') (t) :
    HonestSome c t → HonestSome c' t := fun ⟨o, ho⟩ => ⟨o, ho.mono h⟩

/-- `TargetCollision`, closed over the transcript, is a `KeyCollision` for `HonestSome`. -/
theorem keyCollision_of_targetCollision {o : RomOutcome vp core} {c : PublicHash.Cache core}
    (h : TargetCollision o c) : KeyCollision HonestSome c := by
  obtain ⟨pkSeed, key, xs, ys, v, hhon, hne, h1, h2⟩ := h
  exact ⟨pkSeed, key, xs, ys, v, ⟨o, hhon⟩, hne, h1, h2⟩

/-! ## The charged step -/

section Step

variable [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]

open scoped Classical in
/-- The pairs a fresh `thash` entry at key `(p, k)` adds to `honestPairs`: the fresh entry
against every settled honest entry at that key, and — when the fresh input is itself honest —
every entry at that key against the fresh one. -/
noncomputable def newPairs
    (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) (xs₀ : List core.Y) :
    Set ((publicHashSpec core).Domain × (publicHashSpec core).Domain) :=
  ({PublicHashQuery.thash p k xs₀} ×ˢ honestAt Honest c p k) ∪
    (if Honest c (.thash p k xs₀) then
      (insert (PublicHashQuery.thash p k xs₀) (cachedAt c p k)) ×ˢ
        {PublicHashQuery.thash p k xs₀}
    else ∅)

open scoped Classical in
/-- **The potential increment covers the new pairs.**  The two halves of `newPairs` are disjoint,
and neither meets `honestPairs` of the cache before the fresh entry. -/
theorem encard_newPairs_add_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) (xs₀ : List core.Y)
    (hnone : c (.thash p k xs₀) = none) (u : core.Y) :
    (newPairs Honest c p k xs₀).encard + (honestPairs Honest c).encard ≤
      (honestPairs Honest (c.cacheQuery (.thash p k xs₀) u)).encard := by
  set t : (publicHashSpec core).Domain := .thash p k xs₀ with ht
  set c' := c.cacheQuery t u with hc'
  have hle : c ≤ c' := QueryCache.le_cacheQuery c hnone
  have htsome : (c' t).isSome := by simp [hc']
  have hnotc : ∀ q : (publicHashSpec core).Domain × (publicHashSpec core).Domain,
      q ∈ newPairs Honest c p k xs₀ → q ∉ honestPairs Honest c := by
    rintro ⟨a, b⟩ hq ⟨-, ha, hb, -⟩
    rcases hq with ⟨hae, -⟩ | hq
    · rw [Set.mem_singleton_iff] at hae
      rw [hae, hnone] at ha
      exact absurd ha (by simp)
    · split at hq
      · obtain ⟨-, hbe⟩ := hq
        rw [Set.mem_singleton_iff] at hbe
        rw [hbe, hnone] at hb
        exact absurd hb (by simp)
      · exact absurd hq (Set.notMem_empty _)
  have hsub : newPairs Honest c p k xs₀ ⊆ honestPairs Honest c' := by
    rintro ⟨a, b⟩ hq
    rcases hq with ⟨hae, hbe⟩ | hq
    · rw [Set.mem_singleton_iff] at hae
      obtain ⟨⟨ys, hys⟩, hbs, hbh⟩ := hbe
      exact ⟨⟨p, k, ⟨xs₀, hae⟩, ⟨ys, hys⟩⟩, by rw [hae]; exact htsome,
        QueryCache.isSome_mono hle hbs, hmonoH hle b hbh⟩
    · split at hq
      · rename_i hhon
        obtain ⟨hae, hbe⟩ := hq
        rw [Set.mem_singleton_iff] at hbe
        refine ⟨⟨p, k, ?_, ⟨xs₀, hbe⟩⟩, ?_, by rw [hbe]; exact htsome,
          by rw [hbe]; exact hmonoH hle t hhon⟩
        · rcases hae with h | hs
          · exact ⟨xs₀, h⟩
          · exact hs.1
        · rcases hae with h | hs
          · rw [h]; exact htsome
          · exact QueryCache.isSome_mono hle hs.2
      · exact absurd hq (Set.notMem_empty _)
  calc (newPairs Honest c p k xs₀).encard + (honestPairs Honest c).encard
      = (newPairs Honest c p k xs₀ ∪ honestPairs Honest c).encard :=
        (Set.encard_union_eq (Set.disjoint_left.mpr hnotc)).symm
    _ ≤ (honestPairs Honest c').encard :=
        Set.encard_le_encard (Set.union_subset hsub (honestPairs_mono hmonoH hle))

open scoped Classical in
/-- **The fresh-answer bad set is the key-weighted charge.**  With no retroactive honesty, a
fresh `thash` answer at a key can complete a same-key collision on a settled honest input only
by landing on an honest answer already cached at that key, or — when the fresh input is itself
the honest one — on any answer already cached at that key. -/
theorem encard_badSet_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    {Aux : PublicHash.Cache core → Prop}
    (hhonest : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain)
      (u : (publicHashSpec core).Range t) (g : (publicHashSpec core).Domain), c t = none →
      ¬ Aux (c.cacheQuery t u) → Honest (c.cacheQuery t u) g → Honest c g)
    (c : PublicHash.Cache core) (p : core.PkSeed) (k : core.AdrsKey) (xs₀ : List core.Y)
    (hnone : c (.thash p k xs₀) = none) (hc : ¬ KeyCollision Honest c) :
    {u : core.Y | KeyCollision Honest (c.cacheQuery (.thash p k xs₀) u) ∧
      ¬ Aux (c.cacheQuery (.thash p k xs₀) u)}.encard ≤
      (newPairs Honest c p k xs₀).encard := by
  have hbad : {u : core.Y | KeyCollision Honest (c.cacheQuery (.thash p k xs₀) u) ∧
      ¬ Aux (c.cacheQuery (.thash p k xs₀) u)} ⊆
      {v : core.Y | ∃ ys ∈ {ys : List core.Y | SettledHonest Honest c (.thash p k ys)},
        c (.thash p k ys) = some v} ∪
      {v : core.Y | Honest c (.thash p k xs₀) ∧
        ∃ ys ∈ {ys : List core.Y | (c (.thash p k ys)).isSome},
          c (.thash p k ys) = some v} := by
    rintro u ⟨⟨p', k', xs, ys, v, hhon, hne, hxs, hys⟩, hnaux⟩
    by_cases hAt : (PublicHashQuery.thash p' k' xs : (publicHashSpec core).Domain) =
        .thash p k xs₀
    · -- the fresh query is the honest input: charge every answer cached at the key
      obtain ⟨rfl, rfl, rfl⟩ : p' = p ∧ k' = k ∧ xs = xs₀ := by simpa using hAt
      have hBt : (PublicHashQuery.thash p' k' ys : (publicHashSpec core).Domain) ≠
          .thash p' k' xs := by simpa using Ne.symm hne
      have hvu : v = u := by simpa using hxs.symm
      subst hvu
      have hcB : c (.thash p' k' ys) = some v := by
        rw [← QueryCache.cacheQuery_of_ne c v hBt]; exact hys
      exact Or.inr ⟨hhonest c (.thash p' k' xs) v (.thash p' k' xs) hnone hnaux hhon,
        ys, by simp [hcB], hcB⟩
    · have hhc : Honest c (.thash p' k' xs) :=
        hhonest c (.thash p k xs₀) u (.thash p' k' xs) hnone hnaux hhon
      have hcA : c (.thash p' k' xs) = some v := by
        rw [← QueryCache.cacheQuery_of_ne c u hAt]; exact hxs
      by_cases hBt : (PublicHashQuery.thash p' k' ys : (publicHashSpec core).Domain) =
          .thash p k xs₀
      · -- the fresh query is the non-honest input: charge the honest answers at the key
        obtain ⟨rfl, rfl, rfl⟩ : p' = p ∧ k' = k ∧ ys = xs₀ := by simpa using hBt
        have hvu : v = u := by simpa using hys.symm
        subst hvu
        exact Or.inl ⟨xs, ⟨by simp [hcA], hhc⟩, hcA⟩
      · -- neither is fresh: the collision was already there
        exact absurd ⟨p', k', xs, ys, v, hhc, hne, hcA,
          by rw [← QueryCache.cacheQuery_of_ne c u hBt]; exact hys⟩ hc
  refine le_trans (Set.encard_le_encard hbad) (le_trans (Set.encard_union_le _ _) ?_)
  have hdisj : Disjoint (({PublicHashQuery.thash p k xs₀} :
        Set ((publicHashSpec core).Domain)) ×ˢ honestAt Honest c p k)
      (if Honest c (.thash p k xs₀) then
        (insert (PublicHashQuery.thash p k xs₀) (cachedAt c p k)) ×ˢ
          ({PublicHashQuery.thash p k xs₀} : Set _) else ∅) := by
    refine Set.disjoint_left.mpr ?_
    rintro ⟨a, b⟩ ⟨-, hb⟩ hq
    split at hq
    · obtain ⟨-, hbe⟩ := hq
      rw [Set.mem_singleton_iff] at hbe
      rw [hbe] at hb
      exact absurd hb.2.1 (by simp [hnone])
    · exact absurd hq (Set.notMem_empty _)
  rw [newPairs, Set.encard_union_eq hdisj, Set.encard_prod, Set.encard_singleton, one_mul,
    encard_honestAt]
  refine add_le_add (encard_vals_le c p k _) ?_
  split
  · rw [Set.encard_prod, Set.encard_singleton, mul_one]
    refine le_trans (Set.encard_le_encard fun v hv => hv.2) (le_trans (encard_vals_le c p k _)
      (le_trans (le_of_eq (encard_cachedAt c p k).symm)
        (Set.encard_le_encard (Set.subset_insert _ _))))
  · rename_i hhon
    rw [Set.encard_empty, nonpos_iff_eq_zero, Set.encard_eq_zero]
    exact Set.eq_empty_iff_forall_notMem.mpr fun v hv => hhon hv.1

open scoped Classical in
/-- The pairs a fresh entry at query `t` adds to `honestPairs`: none when `t` is an `H_msg`
query, since `honestPairs` sees only `thash` entries. -/
noncomputable def newPairsAt
    (Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop)
    (c : PublicHash.Cache core) : (publicHashSpec core).Domain →
    Set ((publicHashSpec core).Domain × (publicHashSpec core).Domain)
  | .thash p k xs₀ => newPairs Honest c p k xs₀
  | .hmsg _ _ _ _ => ∅

open scoped Classical in
/-- The potential increment of a fresh entry at any query covers `newPairsAt`. -/
theorem encard_newPairsAt_add_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain) (hnone : c t = none)
    (u : (publicHashSpec core).Range t) :
    (newPairsAt Honest c t).encard + (honestPairs Honest c).encard ≤
      (honestPairs Honest (c.cacheQuery t u)).encard := by
  match t, hnone, u with
  | .thash p k xs₀, hnone, u => exact encard_newPairs_add_le hmonoH c p k xs₀ hnone u
  | .hmsg _ _ _ _, hnone, u =>
    rw [newPairsAt, Set.encard_empty, zero_add]
    exact Set.encard_le_encard (honestPairs_mono hmonoH (QueryCache.le_cacheQuery c hnone))

open scoped Classical in
/-- The key-weighted potential's increment at a fresh entry covers the `newPairsAt` charge. -/
theorem keyedPotential_add_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain) (hnone : c t = none)
    (u : (publicHashSpec core).Range t) :
    ((newPairsAt Honest c t).encard : ℝ≥0∞) / Nat.card core.Y + keyedPotential Honest c ≤
      keyedPotential Honest (c.cacheQuery t u) := by
  rw [keyedPotential, keyedPotential, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  exact_mod_cast encard_newPairsAt_add_le hmonoH c t hnone u

open scoped Classical in
/-- **The fresh-answer bad set is the key-weighted charge, at any query.**  At an `H_msg` query
the collision half of the bad set is empty: both colliding entries are `thash` entries, hence
already present, and the honest side is honest already. -/
theorem encard_badSetAt_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    {Aux : PublicHash.Cache core → Prop}
    (hhonest : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain)
      (u : (publicHashSpec core).Range t) (g : (publicHashSpec core).Domain), c t = none →
      ¬ Aux (c.cacheQuery t u) → Honest (c.cacheQuery t u) g → Honest c g)
    (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain) (hnone : c t = none)
    (hc : ¬ KeyCollision Honest c) :
    {u : (publicHashSpec core).Range t | KeyCollision Honest (c.cacheQuery t u) ∧
      ¬ Aux (c.cacheQuery t u)}.encard ≤ (newPairsAt Honest c t).encard := by
  match t, hnone with
  | .thash p k xs₀, hnone => exact encard_badSet_le hhonest c p k xs₀ hnone hc
  | .hmsg R pkSeed pkRoot msg, hnone =>
    rw [newPairsAt, Set.encard_empty, nonpos_iff_eq_zero, Set.encard_eq_zero]
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro u ⟨⟨p, k, xs, ys, v, hhon, hne, hxs, hys⟩, hnaux⟩
    refine absurd ⟨p, k, xs, ys, v,
      hhonest c _ u (.thash p k xs) hnone hnaux hhon, hne, ?_, ?_⟩ hc
    · rw [← QueryCache.cacheQuery_of_ne c u (by simp : (PublicHashQuery.thash p k xs :
        (publicHashSpec core).Domain) ≠ .hmsg R pkSeed pkRoot msg)]
      exact hxs
    · rw [← QueryCache.cacheQuery_of_ne c u (by simp : (PublicHashQuery.thash p k ys :
        (publicHashSpec core).Domain) ≠ .hmsg R pkSeed pkRoot msg)]
      exact hys

/-! ## The bound along a run -/

section Run

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]

open scoped Classical in
/-- **The key-weighted fresh-answer bound, with an auxiliary event.**  `Aux` is an auxiliary
event carrying its own monotone potential `Ψ` with budget `B`; it absorbs every firing that the
step's own fresh sample does not control.  Along a run of the shared lazy public-hash oracle from
the empty cache, a same-key collision on a settled honest input, or `Aux`, holds of the final
cache with mass at most `r * q / |core.Y| + B` on the paths whose final cache has at most `q`
entries.  The first summand is *linear* in the query budget: the charge a fresh answer pays is
the key-weighted potential's own increment, not a flat `ε`. -/
theorem evalDist_run_setOf_keyCollision_aux_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    (Aux : PublicHash.Cache core → Prop) (Ψ : PublicHash.Cache core → ℝ≥0∞)
    (hΨmono : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → Ψ c ≤ Ψ c')
    (hΨempty : Ψ ∅ = 0) (hAuxEmpty : ¬ Aux ∅)
    (hhonest : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain)
      (u : (publicHashSpec core).Range t) (g : (publicHashSpec core).Domain), c t = none →
      ¬ Aux (c.cacheQuery t u) → Honest (c.cacheQuery t u) g → Honest c g)
    (haux : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain), c t = none →
      ¬ (KeyCollision Honest c ∨ Aux c) →
      ∃ w' : ℝ≥0∞, (letI : MeasurableSpace ((publicHashSpec core).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core).Range t : ProbComp _)]
          {u | Aux (c.cacheQuery t u)} ≤ w') ∧
        ∀ u, w' + Ψ c ≤ Ψ (c.cacheQuery t u))
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest Honest c (.thash p k xs) → SettledHonest Honest c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (q : ℕ) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hBudget : ∀ c : PublicHash.Cache core, QueryCache.enncard c ≤ (q : ℝ≥0∞) → Ψ c ≤ B)
    {α : Type} (oa : OracleComp (unifSpec + publicHashSpec core) α) :
    (letI : MeasurableSpace (α × PublicHash.Cache core) := ⊤;
      𝒟[(simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) oa).run ∅]
        {z | (KeyCollision Honest z.2 ∨ Aux z.2) ∧ QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} ≤
        (r * q : ℝ≥0∞) / Nat.card core.Y + B) := by
  let _ : MeasurableSpace (α × PublicHash.Cache core) := ⊤
  have hNzero : Nat.card core.Y ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  -- the potential never decreases along a step
  have hmono : ∀ (t : (unifSpec + publicHashSpec core).Domain) (c : PublicHash.Cache core),
      ∀ z ∈ support (((unifFwdImpl (publicHashSpec core) +
        PublicHash.randomOracle core) t).run c),
        keyedPotential Honest c + Ψ c ≤ keyedPotential Honest z.2 + Ψ z.2 := by
    intro t c z hz
    have hle : c ≤ z.2 := le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl
      (liftM (OracleSpec.query t) :
        OracleComp (unifSpec + publicHashSpec core)
          ((unifSpec + publicHashSpec core).Range t)) (by simpa using hz)
    exact add_le_add (keyedPotential_mono hmonoH hle) (hΨmono hle)
  -- the charged step
  have hstep : ∀ (t : (unifSpec + publicHashSpec core).Domain) (c : PublicHash.Cache core),
      ¬ (KeyCollision Honest c ∨ Aux c) →
      (∃ a c', (((unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) t).run c) =
          pure (a, c') ∧ ¬ (KeyCollision Honest c' ∨ Aux c')) ∨
      (∃ (samp : ProbComp ((unifSpec + publicHashSpec core).Range t))
        (upd : (unifSpec + publicHashSpec core).Range t → PublicHash.Cache core) (w : ℝ≥0∞),
        (((unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) t).run c) =
          (fun u => (u, upd u)) <$> samp ∧
        (letI : MeasurableSpace ((unifSpec + publicHashSpec core).Range t) := ⊤;
          𝒟[samp] {u | KeyCollision Honest (upd u) ∨ Aux (upd u)} ≤ w) ∧
        ∀ u, w + (keyedPotential Honest c + Ψ c) ≤
          keyedPotential Honest (upd u) + Ψ (upd u)) := by
    rintro (i | t) c hc
    · obtain ⟨samp, hsamp⟩ :=
        exists_run_unifFwdImpl_add_randomOracle_inl (spec := publicHashSpec core) i c
      exact Or.inr ⟨samp, fun _ => c, 0, hsamp, by simp [hc], fun _ => by simp⟩
    rcases hcache : c t with _ | v
    swap
    · exact Or.inl ⟨v, c, run_unifFwdImpl_add_randomOracle_inr_some hcache, hc⟩
    -- the auxiliary charge is available at every fresh query
    obtain ⟨w', hw', hΨ⟩ := haux c t hcache hc
    have hcKC : ¬ KeyCollision Honest c := fun h => hc (Or.inl h)
    -- the collision half of the bad set, on the paths where `Aux` does not fire
    have hbadmeas : (letI : MeasurableSpace ((publicHashSpec core).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core).Range t : ProbComp _)]
          {u | KeyCollision Honest (c.cacheQuery t u) ∧ ¬ Aux (c.cacheQuery t u)} ≤
          ((newPairsAt Honest c t).encard : ℝ≥0∞) / Nat.card core.Y) := by
      match t, hcache, w', hw', hΨ with
      | .thash p k xs₀, hcache, w', hw', hΨ =>
        let _ : MeasurableSpace ((publicHashSpec core).Range
          (PublicHashQuery.thash p k xs₀)) := ⊤
        refine le_trans (SampleableType.evalDist_uniformSample_le_encard_div _)
          (ENNReal.div_le_div_right ?_ _)
        exact_mod_cast encard_badSet_le hhonest c p k xs₀ hcache hcKC
      | .hmsg R pkSeed pkRoot msg, hcache, w', hw', hΨ =>
        let _ : MeasurableSpace ((publicHashSpec core).Range
          (PublicHashQuery.hmsg R pkSeed pkRoot msg)) := ⊤
        have hz := encard_badSetAt_le hhonest c (.hmsg R pkSeed pkRoot msg) hcache hcKC
        rw [newPairsAt, Set.encard_empty, nonpos_iff_eq_zero, Set.encard_eq_zero] at hz
        simp [hz]
    refine Or.inr ⟨$ᵗ (publicHashSpec core).Range t, fun u => c.cacheQuery t u,
      ((newPairsAt Honest c t).encard : ℝ≥0∞) / Nat.card core.Y + w',
      run_unifFwdImpl_add_randomOracle_inr_none hcache, ?_, ?_⟩
    · let _ : MeasurableSpace ((publicHashSpec core).Range t) := ⊤
      have hsplit : {u : (publicHashSpec core).Range t |
          KeyCollision Honest (c.cacheQuery t u) ∨ Aux (c.cacheQuery t u)} ⊆
          {u | KeyCollision Honest (c.cacheQuery t u) ∧ ¬ Aux (c.cacheQuery t u)} ∪
          {u | Aux (c.cacheQuery t u)} := by
        rintro u (h | h)
        · by_cases ha : Aux (c.cacheQuery t u)
          · exact Or.inr ha
          · exact Or.inl ⟨h, ha⟩
        · exact Or.inr h
      exact le_trans (measure_mono hsplit)
        (le_trans (measure_union_le _ _) (add_le_add hbadmeas hw'))
    · intro u
      have harith : ((newPairsAt Honest c t).encard : ℝ≥0∞) / Nat.card core.Y + w' +
          (keyedPotential Honest c + Ψ c) =
          (((newPairsAt Honest c t).encard : ℝ≥0∞) / Nat.card core.Y + keyedPotential Honest c) +
            (w' + Ψ c) := by ring
      rw [harith]
      exact add_le_add (keyedPotential_add_le hmonoH c t hcache u) (hΨ u)
  -- run the engine and convert the budget clause
  have hzero : keyedPotential Honest (∅ : PublicHash.Cache core) +
      Ψ (∅ : PublicHash.Cache core) = 0 := by
    have h0 : (honestPairs Honest (∅ : PublicHash.Cache core)).encard = 0 := by
      rw [Set.encard_eq_zero]
      exact Set.eq_empty_iff_forall_notMem.mpr fun pq h => absurd h.2.1 (by simp)
    rw [keyedPotential, h0, ENat.toENNReal_zero, ENNReal.zero_div, hΨempty, add_zero]
  have key := evalDist_apply_setOf_and_le_of_potential
    (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core)
    (fun c => KeyCollision Honest c ∨ Aux c) (fun c => keyedPotential Honest c + Ψ c)
    hmono hstep oa
    ((r * q : ℝ≥0∞) / Nat.card core.Y + B)
    (ENNReal.add_ne_top.mpr
      ⟨ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (by exact_mod_cast hNzero),
        hB⟩)
    ∅ (by
      rintro (⟨p, k, xs, ys, v, -, -, h, -⟩ | h)
      · simp at h
      · exact hAuxEmpty h)
  rw [hzero, tsub_zero] at key
  have hincl : {z : α × PublicHash.Cache core | (KeyCollision Honest z.2 ∨ Aux z.2) ∧
      QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} ⊆
      {z : α × PublicHash.Cache core | (KeyCollision Honest z.2 ∨ Aux z.2) ∧
        keyedPotential Honest z.2 + Ψ z.2 ≤ (r * q : ℝ≥0∞) / Nat.card core.Y + B} := by
    rintro z ⟨h1, h2⟩
    refine ⟨h1, add_le_add (ENNReal.div_le_div_right ?_ _) (hBudget z.2 h2)⟩
    have hstep1 : ((honestPairs Honest z.2).encard : ℝ≥0∞) ≤
        (r : ℝ≥0∞) * QueryCache.enncard z.2 := by
      calc ((honestPairs Honest z.2).encard : ℝ≥0∞)
          ≤ (((r : ℕ∞) * z.2.toSet.encard : ℕ∞) : ℝ≥0∞) := by
            exact_mod_cast encard_honestPairs_le r ρ hρ z.2
        _ = (r : ℝ≥0∞) * QueryCache.enncard z.2 := by
            rw [QueryCache.enncard]; push_cast; ring
    refine hstep1.trans ?_
    gcongr
  exact le_trans (measure_mono hincl) key

open scoped Classical in
/-- **The key-weighted fresh-answer bound with no auxiliary event.**  With no retroactive honesty
at all (`hstable`) the auxiliary event is unnecessary and the bound is `r * q / |core.Y|`. -/
theorem evalDist_run_setOf_keyCollision_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    (hstable : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain)
      (u : (publicHashSpec core).Range t) (g : (publicHashSpec core).Domain), c t = none →
      Honest (c.cacheQuery t u) g → Honest c g)
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest Honest c (.thash p k xs) → SettledHonest Honest c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (q : ℕ) {α : Type} (oa : OracleComp (unifSpec + publicHashSpec core) α) :
    (letI : MeasurableSpace (α × PublicHash.Cache core) := ⊤;
      𝒟[(simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) oa).run ∅]
        {z | KeyCollision Honest z.2 ∧ QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} ≤
        (r * q : ℝ≥0∞) / Nat.card core.Y) := by
  let _ : MeasurableSpace (α × PublicHash.Cache core) := ⊤
  have key := evalDist_run_setOf_keyCollision_aux_le hmonoH (fun _ => False) (fun _ => 0)
    (fun _ => le_rfl) rfl (fun h => h)
    (fun c t u g hn _ hg => hstable c t u g hn hg)
    (fun c t _ _ => ⟨0, by simp, fun _ => by simp⟩) r ρ hρ q 0 (by simp)
    (fun _ _ => le_rfl) oa
  rw [add_zero] at key
  have hincl : {z : α × PublicHash.Cache core | KeyCollision Honest z.2 ∧
      QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} ⊆
      {z : α × PublicHash.Cache core | (KeyCollision Honest z.2 ∨ False) ∧
        QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} := fun z hz => ⟨Or.inl hz.1, hz.2⟩
  exact le_trans (measure_mono hincl) key

end Run

/-! ## The bound on the counted SLH-DSA run -/

section RomRun

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]

local notation "romSpec" => unifSpec + publicHashSpec core

open scoped Classical in
/-- **The linear same-key collision bound for the counted SLH-DSA run.**  Under a public-hash
query budget `q` and at most `r` separated settled honest entries per `thash` key, with no
retroactive honesty, a same-key collision on a settled honest input holds of the final cache
with mass at most `r * q / |core.Y|`. -/
theorem evalDist_romRunFull_keyCollision_le
    {Honest : PublicHash.Cache core → (publicHashSpec core).Domain → Prop}
    (hmonoH : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → ∀ t, Honest c t → Honest c' t)
    (hstable : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain)
      (u : (publicHashSpec core).Range t) (g : (publicHashSpec core).Domain), c t = none →
      Honest (c.cacheQuery t u) g → Honest c g)
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest Honest c (.thash p k xs) → SettledHonest Honest c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ)
    (hq : HasHashQueryBound core adv q) :
    (letI : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤;
      𝒟[romRunFull core adv] {z | KeyCollision Honest z.2} ≤
        (r * q : ℝ≥0∞) / Nat.card core.Y) := by
  let _ : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤
  have hae : ∀ᵐ z ∂𝒟[romRunFull core adv],
      z ∈ {z : RomOutcome vp core × PublicHash.Cache core | KeyCollision Honest z.2} →
        z ∈ {z : RomOutcome vp core × PublicHash.Cache core |
          KeyCollision Honest z.2 ∧ QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} :=
    evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete
      fun z hz hp => ⟨hp, enncard_le_of_hasHashQueryBound core adv q hq hz⟩
  refine (measure_mono_ae hae).trans ?_
  rw [romRunFull]
  exact evalDist_run_setOf_keyCollision_le hmonoH hstable r ρ hρ q (romGameCoreFull core adv)

open scoped Classical in
/-- **The linear target-collision bound for SLH-DSA.**  Under a public-hash query budget `q`, a
separator `ρ` bounding by `r` the settled honest entries per `thash` key, and a monotone
potential `Ψ` with budget `B` for the auxiliary event `Aux`, the same-address target collision of
`HashSig.SLHDSA.Security.RomDescent` — closed over the transcript — holds of the final cache of
`romRunFull` with mass at most `r * q / |core.Y| + B`. -/
theorem evalDist_romRunFull_targetCollision_le
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest HonestSome c (.thash p k xs) → SettledHonest HonestSome c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (Aux : PublicHash.Cache core → Prop) (Ψ : PublicHash.Cache core → ℝ≥0∞)
    (hΨmono : ∀ {c c' : PublicHash.Cache core}, c ≤ c' → Ψ c ≤ Ψ c') (hΨempty : Ψ ∅ = 0)
    (hAuxEmpty : ¬ Aux ∅)
    (hhonest : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain)
      (u : (publicHashSpec core).Range t) (g : (publicHashSpec core).Domain), c t = none →
      ¬ Aux (c.cacheQuery t u) → HonestSome (c.cacheQuery t u) g → HonestSome c g)
    (haux : ∀ (c : PublicHash.Cache core) (t : (publicHashSpec core).Domain), c t = none →
      ¬ (KeyCollision HonestSome c ∨ Aux c) →
      ∃ w' : ℝ≥0∞, (letI : MeasurableSpace ((publicHashSpec core).Range t) := ⊤;
        𝒟[($ᵗ (publicHashSpec core).Range t : ProbComp _)]
          {u | Aux (c.cacheQuery t u)} ≤ w') ∧
        ∀ u, w' + Ψ c ≤ Ψ (c.cacheQuery t u))
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ)
    (hq : HasHashQueryBound core adv q)
    (hBudget : ∀ c : PublicHash.Cache core, QueryCache.enncard c ≤ (q : ℝ≥0∞) → Ψ c ≤ B) :
    (letI : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤;
      𝒟[romRunFull core adv] {z | ∃ o, TargetCollision o z.2} ≤
        (r * q : ℝ≥0∞) / Nat.card core.Y + B) := by
  let _ : MeasurableSpace (RomOutcome vp core × PublicHash.Cache core) := ⊤
  have hae : ∀ᵐ z ∂𝒟[romRunFull core adv],
      z ∈ {z : RomOutcome vp core × PublicHash.Cache core | ∃ o, TargetCollision o z.2} →
        z ∈ {z : RomOutcome vp core × PublicHash.Cache core |
          (KeyCollision HonestSome z.2 ∨ Aux z.2) ∧
            QueryCache.enncard z.2 ≤ (q : ℝ≥0∞)} := by
    refine evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete ?_
    rintro z hz ⟨o, ho⟩
    exact ⟨Or.inl (keyCollision_of_targetCollision ho),
      enncard_le_of_hasHashQueryBound core adv q hq hz⟩
  refine (measure_mono_ae hae).trans ?_
  rw [romRunFull]
  exact evalDist_run_setOf_keyCollision_aux_le (fun h t => honestSome_mono h t)
    Aux Ψ hΨmono hΨempty hAuxEmpty hhonest haux r ρ hρ q B hB hBudget
    (romGameCoreFull core adv)

end RomRun

end Step

end SLHDSA.Security
