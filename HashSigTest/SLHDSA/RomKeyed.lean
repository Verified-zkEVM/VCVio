/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomKeyed

/-!
# SLH-DSA keyed-collision vacuity witnesses

The theorems below document why the scheme-facing theorems of
`HashSig.SLHDSA.Security.RomKeyed` are uninformative as stated.  The abstract bound of that
module is correct and its arithmetic is genuinely linear in the query budget; what these
witnesses establish is that its two instantiations at the scheme's own honest-entry relation
`SLHDSA.Security.HonestSome` — `evalDist_romRunFull_targetCollision_le` and
`evalDist_romRunFull_keyCollision_le` — carry no information.

## The separator constant cannot be small

`HonestSome` closes `SLHDSA.Security.HonestEntry` over the transcript, `SLHDSA.Security.RomOutcome`
is a plain structure with no invariant, and the `forsLeaf` constructor has no premises.  So at a
cache that settles every `thash` query, the FORS leaf secret of *every* secret seed is a settled
honest entry at its own key (`settledHonest_forsLeaf`).  Any `ρ` satisfying the separator
hypothesis must then take distinct values on those entries, so its `r` is at least the size of any
seed set on which the FORS leaf secret is injective (`card_le_of_separator`), and the bound's main
term `r * q / Nat.card core.Y` is already at least `1` at `q = 1`
(`one_le_bound_of_separator`).

## The trivial-auxiliary hypothesis fails

`hstable`, the hypothesis of the corollary with no auxiliary event, asks that no fresh answer
create an honest entry at another query.  Caching the WOTS+ chain entry at hash address `0` makes
the chain value one step further an honest entry, and the partial chain reading that certifies it
returns `none` before that entry is present (`honestSome_cacheQuery_of_chain`).

## Nothing here is runnable, and no positive witness is offered

Every statement is about a `Prop` over a cache or an `ℝ≥0∞` bound, so the file has no `main` and
is built by the `HashSigTest` library glob alone.  It deliberately carries no fixture exhibiting
satisfied hypotheses: the abstract hypothesis set is jointly satisfiable, but satisfiability
establishes nothing about whether a bound says anything, so a fixture of that kind would mislead.

## What the witnesses cannot catch

* **That no other constructor certifies the chain entry.**  `honestSome_cacheQuery_of_chain`
  exhibits the `wotsChain` reading and its absence beforehand; that no other `HonestEntry`
  constructor certifies the same query is not formalised.
* **A restructured honest relation.**  The witnesses are about `HonestSome` as written.  A
  relation that pins the run's own secret key is a different relation and nothing here speaks to
  it.
-/

public section

namespace SLHDSA.RomKeyedTest

open Security OracleComp OracleSpec
open scoped ENNReal

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The separator constant cannot be small -/

/-- A cache that settles every `thash` query at one value and no `H_msg` query. -/
def fullThash (y : core.Y) : PublicHash.Cache core :=
  QueryCache.ofFn fun q => match q with
    | .thash _ _ _ => some y
    | .hmsg _ _ _ _ => none

/-- Every FORS leaf secret, at every secret seed, is a settled honest entry of `fullThash`. -/
theorem settledHonest_forsLeaf (o₀ : RomOutcome vp core) (y : core.Y) (p : core.PkSeed)
    (adrs : Adrs) (t : ℕ) (s : core.SkSeed) :
    SettledHonest HonestSome (fullThash y) (.thash p (core.adrsToKey (forsNodeAdrs adrs 0 t))
      [forsSkGenCore core s p adrs t]) := by
  refine ⟨by simp [fullThash, QueryCache.ofFn], ⟨?_, ?_⟩⟩
  · exact RomOutcome.mk ⟨p, o₀.pk.pkRoot⟩ ⟨s, o₀.sk.skPrf, p, o₀.pk.pkRoot⟩ o₀.log o₀.msg
      o₀.sig o₀.verified
  · exact .forsLeaf adrs t

/-- The separator hypothesis forces `r` to be at least the number of secret seeds the FORS leaf
secret at one address distinguishes. -/
theorem card_le_of_separator (o₀ : RomOutcome vp core) (y : core.Y)
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest HonestSome c (.thash p k xs) → SettledHonest HonestSome c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (p : core.PkSeed) (adrs : Adrs) (t : ℕ) (S : Finset core.SkSeed)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, forsSkGenCore core s p adrs t = forsSkGenCore core s' p adrs t →
      s = s') :
    S.card ≤ r := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := S) (t := (Finset.univ : Finset (Fin r)))
    (f := fun s => ρ (.thash p (core.adrsToKey (forsNodeAdrs adrs 0 t))
      [forsSkGenCore core s p adrs t]))
    (fun _ _ => Finset.mem_univ _) ?_
  · simpa using h
  · intro s hs s' hs' h
    refine hinj s hs s' hs' ?_
    have := hρ (fullThash y) p (core.adrsToKey (forsNodeAdrs adrs 0 t))
      [forsSkGenCore core s p adrs t] [forsSkGenCore core s' p adrs t]
      (settledHonest_forsLeaf o₀ y p adrs t s) (settledHonest_forsLeaf o₀ y p adrs t s') h
    simpa using this

section Bound

variable [SampleableType core.Y]

/-- The main term of the bound exceeds `1` at a single query.  If the FORS leaf secret at one
address is injective in the secret seed over a set of at least `Nat.card core.Y` seeds, then any
`ρ` satisfying the separator hypothesis has `r ≥ Nat.card core.Y`. -/
theorem one_le_bound_of_separator (o₀ : RomOutcome vp core) (y : core.Y)
    (r : ℕ) (ρ : (publicHashSpec core).Domain → Fin r)
    (hρ : ∀ (c : PublicHash.Cache core) p k (xs ys : List core.Y),
      SettledHonest HonestSome c (.thash p k xs) → SettledHonest HonestSome c (.thash p k ys) →
      ρ (.thash p k xs) = ρ (.thash p k ys) → xs = ys)
    (p : core.PkSeed) (adrs : Adrs) (t : ℕ) (S : Finset core.SkSeed)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, forsSkGenCore core s p adrs t = forsSkGenCore core s' p adrs t →
      s = s')
    (hS : Nat.card core.Y ≤ S.card) (q : ℕ) (hq : 1 ≤ q) :
    1 ≤ (r * q : ℝ≥0∞) / Nat.card core.Y := by
  have hr : Nat.card core.Y ≤ r := hS.trans (card_le_of_separator o₀ y r ρ hρ p adrs t S hinj)
  have hN0 : (Nat.card core.Y : ℝ≥0∞) ≠ 0 := by
    simpa using Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl hN0) (Or.inl (by simp)), one_mul]
  calc (Nat.card core.Y : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by exact_mod_cast hr
    _ ≤ (r : ℝ≥0∞) * q := le_mul_of_one_le_right' (by exact_mod_cast hq)

end Bound

/-! ## The trivial-auxiliary hypothesis fails -/

section Stable

variable [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]

/-- A fresh answer creates an honest entry at another query: caching the WOTS+ chain entry at
hash address `0` makes the chain value one step further an honest entry, and the partial chain
reading that certifies it returns `none` before that entry is present. -/
theorem honestSome_cacheQuery_of_chain (o₀ : RomOutcome vp core) (c : PublicHash.Cache core)
    (p : core.PkSeed) (adrs : Adrs) (i : ℕ) (s : core.SkSeed) (v : core.Y)
    (hnone : c (.thash p (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress 0))
      [core.PRF p s (wotsSkAdrs adrs i)]) = none) :
    HonestSome (c.cacheQuery (.thash p
        (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress 0))
        [core.PRF p s (wotsSkAdrs adrs i)]) v)
      (.thash p (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress 1)) [v]) ∧
    chain? core c p (wotsChainAdrs adrs i) (core.PRF p s (wotsSkAdrs adrs i)) 0 1 = none := by
  set x := core.PRF p s (wotsSkAdrs adrs i) with hx
  set t : (publicHashSpec core).Domain :=
    .thash p (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress 0)) [x] with ht
  refine ⟨⟨RomOutcome.mk ⟨p, o₀.pk.pkRoot⟩ ⟨s, o₀.sk.skPrf, p, o₀.pk.pkRoot⟩ o₀.log o₀.msg
      o₀.sig o₀.verified, .wotsChain adrs i 1 v ?_⟩, ?_⟩
  · rw [chain?_succ_eq_some_iff]
    exact ⟨x, chain?_zero core _ p _ x 0, QueryCache.cacheQuery_self c t v⟩
  · rcases h : chain? core c p (wotsChainAdrs adrs i) x 0 1 with _ | y
    · rfl
    · rw [chain?_succ_eq_some_iff] at h
      obtain ⟨z, hz, hc⟩ := h
      rw [chain?_zero] at hz
      rw [← Option.some_inj.mp hz] at hc
      rw [Nat.add_zero] at hc
      rw [ht] at hnone
      rw [hnone] at hc
      exact absurd hc (by simp)

end Stable

end SLHDSA.RomKeyedTest
