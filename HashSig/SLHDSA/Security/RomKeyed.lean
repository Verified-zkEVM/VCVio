/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.RandomOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# The key-weighted same-key collision bound

A same-key collision on a settled honest input (`KeyCollision`) is a pair of cached `thash`
entries at one key, one of them a settled honest input, with equal answers and different inputs;
the honest side is a relation `Honest` between a cache and a query, supplied by the caller.  This
module bounds the mass of that event over a run of the shared lazy public-hash oracle from the
empty cache, and the bound is **linear** in the cache size:

  `r * q / Nat.card core.Y + B`.

* `r` is a *separator bound*: a map `ρ` from public-hash queries to `Fin r` separates, at each
  `thash` key, the settled honest inputs — two settled honest inputs at one key with the same
  `ρ`-value are equal.  It gives `encard_honestPairs_le`, whose content is
  `Σ_K n_K · h_K ≤ r · Σ_K n_K`, and it is the source of the linearity: the charge a fresh answer
  pays is the increment of the key-weighted potential `keyedPotential`, not a flat per-step `ε`.
* `B` is the budget of an auxiliary event `Aux` carried by a monotone potential `Ψ`, both
  parameters of the main theorem.  `Aux` absorbs every firing the step's own fresh sample does not
  control, in particular a fresh answer that makes an entry honest retroactively (`hhonest`): a
  cache is a table of query-answer pairs and records no attribution, so an entry an honest party
  computed and an entry whose value was queried before the honest party reached it are the same
  entry.

The engine is `OracleComp.evalDist_apply_setOf_and_le_of_potential`, and the per-step uniform
charge is `SampleableType.evalDist_uniformSample_le_encard_div`.

## Scope

* The event is restricted to the paths whose final cache has at most `q` entries, honest entries
  included.  A bound in terms of the forger's own query count alone needs a potential that
  charges only the entries the forger's queries create.
* `evalDist_run_setOf_keyCollision_le` is the case with no auxiliary event, at the price of the
  hypothesis that no fresh answer makes an entry honest.
* `honestPairs` sees only `thash` entries, so an `H_msg` answer pays no charge; the step bound at
  such a query is that the collision half of its bad set is empty (`encard_badSetAt_le`).
* The bound is stated with the denominator `Nat.card core.Y`, and the measurable-space instances
  on the sampled and outcome types are pinned to `⊤` inside the statements, as in the engine.
* Nothing here is quantum.

## Labels

Twenty-four declarations.

*Settled honest entries, the key-weighted potential and the collision*: `SettledHonest`,
`keyDom`, `cachedAt`, `honestAt`, `honestPairs`, `keyedPotential`, `KeyCollision`.

*Per-key counting*: `thash_injective_right`, `encard_keyDom_and`, `encard_honestAt`,
`encard_cachedAt`, `encard_vals_le`.

*Monotonicity*: `honestPairs_mono`, `keyedPotential_mono`.

*The budget clause*: `encard_honestPairs_le`.

*The charged step*: `newPairs`, `encard_newPairs_add_le`, `encard_badSet_le`, `newPairsAt`,
`encard_newPairsAt_add_le`, `keyedPotential_add_le`, `encard_badSetAt_le`.

*The bound along a run*: `evalDist_run_setOf_keyCollision_aux_le`,
`evalDist_run_setOf_keyCollision_le`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec MeasureTheory
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

end Step

end SLHDSA.Security
