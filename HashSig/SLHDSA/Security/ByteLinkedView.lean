/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedRun
public import HashSig.SLHDSA.Security.HonestTransfer

/-!
# The bad events of the verifying run, read through the linked redirect

At `n = 32`, for a fixed public seed and every `opt_rand` distribution, the strong advantage against
SLH-DSA over one SHAKE256 oracle is at most the probability of an event of the three-oracle run
of `romScheme` against the verifying adversary `verifyingAdv`
(`shakeStrongAdvantage_pure_le_viewEvents`), a disjunction of

* `RunTargetCollision`: a same-address target collision on the run's public-hash cache `C`;
* `RunHiddenHitMixed`: a hidden-value hit whose forger replay is read on the view
  `V = C.viewBy (linkedRedirect vp pk)` and whose honest values are read on `C`, with the hashed
  forger point not linked (`HiddenHitMixed`);
* `RunPrfKeyClash id pkSeed pkSeed`: the message-`PRF` key is hit at `opt_rand = PK.seed`;
* `VirtualHit`: an honest entry of `C` whose cached value is the first `n` bytes of a cached
  `H_msg` answer at the reading of a linked point at the same key;
* `LinkedHonestInput`: an honest input of `C` at a linked point (`HonestInputIn`);
* `RunItsrCovered`: interleaved-target coverage on `C`;

coverage conjoined with freshness of the forged `H_msg` point, as `RunItsrCovered` carries it. The
first and last are the events of `HashSig.SLHDSA.Security.RomSchemeUnion`, read on the cache
itself.

## The argument

When the honest replays settle off the linked points, the strong bridge on a settled cache
(`bad_event_or_logged_of_settled`) fires on the view `V`, its logged disjunct excluded by the
freshness of the forged pair, and unless `C` has an honest input at a linked point, `V` transfers
honestly to `C` off the linked points (`HonestTransfer`), which splits the bridge's events onto `C`
(`bad_event_of_redirectedWins`). When a replay fails off the linked points, the replays, settled on
`C` on the support of a run, show an honest input at a linked point
(`linkedHonestInput_of_not_honestOffLinked`).

## Scope

* No event probability is bounded here.
* Nothing here is quantum: the bound is a classical random-oracle statement.

## Labels

*The events*: `LinkedHonestInput`, `VirtualHit`, `RunHiddenHitMixed`.

*The splits*: `targetCollision_or_virtualHit_of_viewBy`, `bad_event_of_redirectedWins`,
`linkedHonestInput_of_not_honestOffLinked`.

*The headline*: `shakeStrongAdvantage_pure_le_viewEvents`.

*Weak seeds*: `not_virtualHit_and_not_linkedHonestInput`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security

open Concrete

variable {vp : ValidatedParams}

/-! ## The events -/

variable (vp) in
/-- An honest input of the run's public-hash cache at a linked point: an honest entry at a linked
point, or a ledger secret queried at a linked point. -/
@[expose] def LinkedHonestInput
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  HonestInputIn (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed (IsLinked vp z.1.pk) z.2.fst

variable (vp) in
/-- An honest entry of the run's public-hash cache at a key `k` whose cached value is the first
`n` bytes of the cached answer at the `H_msg` reading of a linked point at `k`. -/
@[expose] def VirtualHit
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  ∃ (k : (shakeCore vp).AdrsKey) (xs : List (shakeCore vp).Y) (r : (shakeCore vp).Y)
    (rest : List (shakeCore vp).Y) (u : Bytes vp.params.m),
    HonestEntry (oracleSecret (shakeCore vp) (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed)
      z.1.pk.pkSeed z.2.fst (.thash z.1.pk.pkSeed k xs) ∧
    IsLinked vp z.1.pk (.thash z.1.pk.pkSeed k (r :: rest)) ∧
    z.2.fst (linkedHmsg vp z.1.pk.pkSeed r rest) = some u ∧
    z.2.fst (.thash z.1.pk.pkSeed k xs) = some (prefixBytes vp.params.n u)

variable (vp) in
/-- A run point exhibits a hidden-value hit at its own oracle-backed provider whose forger replay
is read on its public-hash cache through the linked redirect and whose honest values are read on
the cache, with the hashed forger point not linked. -/
@[expose] def RunHiddenHitMixed
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache) : Prop :=
  HiddenHitMixed (IsLinked vp z.1.pk)
    (oracleSecret (shakeCore vp) (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed) z.1
    (z.2.fst.viewBy (linkedRedirect vp z.1.pk)) z.2.fst

/-! ## The splits -/

/-- If the view of the run's cache through the linked redirect transfers honestly to the cache off
the linked points, a target collision on the view is a target collision on the cache, or a virtual
hit. -/
theorem targetCollision_or_virtualHit_of_viewBy
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache)
    (ht : HonestTransfer (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed (IsLinked vp z.1.pk)
      (z.2.fst.viewBy (linkedRedirect vp z.1.pk)) z.2.fst)
    (h : TargetCollision (oracleSecret (shakeCore vp) (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed)
      z.1.pk.pkSeed (z.2.fst.viewBy (linkedRedirect vp z.1.pk))) :
    TargetCollision (oracleSecret (shakeCore vp) (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed)
      z.1.pk.pkSeed z.2.fst ∨ VirtualHit vp z := by
  obtain ⟨key, xs, ys, v, hhon, hne, hx, hy⟩ := h
  have hhon' := ht.honestEntry hhon
  rw [viewBy_linkedRedirect_of_not_isLinked _ fun hL => ht.not_honestInputIn (.inl ⟨_, hL, hhon'⟩)]
    at hx
  by_cases hyl : IsLinked vp z.1.pk (.thash z.1.pk.pkSeed key ys)
  · obtain ⟨r, rest, rfl⟩ : ∃ r rest, ys = r :: rest := by
      cases ys with
      | nil => exact hyl.elim
      | cons r rest => exact ⟨r, rest, rfl⟩
    rw [viewBy_linkedRedirect_of_isLinked _ hyl] at hy
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact .inr ⟨key, xs, r, rest, u, hhon', hyl, hu, hx⟩
  · rw [viewBy_linkedRedirect_of_not_isLinked _ hyl] at hy
    exact .inl ⟨key, xs, ys, v, hhon', hne, hx, hy⟩

/-- If the forgery wins on the redirected verification and the honest replays settle off the
linked points, the run point exhibits a target collision, a mixed hidden-value hit or coverage,
coverage at a fresh `H_msg` point, or a virtual hit, or an honest input at a linked point. -/
theorem bad_event_of_redirectedWins
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache)
    (hw : RedirectedWins vp z) (ho : HonestOffLinked vp z) :
    ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
      RunItsrCovered (shakeCore vp) z) ∨ VirtualHit vp z ∨ LinkedHonestInput vp z := by
  by_cases hz : LinkedHonestInput vp z
  · exact .inr (.inr hz)
  have hle : QueryCache.filter (¬IsLinked vp z.1.pk ·) z.2.fst ≤
      z.2.fst.viewBy (linkedRedirect vp z.1.pk) :=
    QueryCache.filter_le_viewBy _ fun _ ht => linkedRedirect_of_not_isLinked ht
  have hv : simulateQ (z.2.fst.viewBy (linkedRedirect vp z.1.pk)).toPartialImpl
      (GeneralScheme.verifyInternalM vp (shakeCore vp) z.1.msg z.1.sig z.1.pk) = some true := by
    rw [QueryCache.simulateQ_viewBy_toPartialImpl]
    exact hw.2
  have ht : HonestTransfer (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed (IsLinked vp z.1.pk)
      (z.2.fst.viewBy (linkedRedirect vp z.1.pk)) z.2.fst :=
    ⟨fun _ ht => viewBy_linkedRedirect_of_not_isLinked _ ht, hz⟩
  have hm : ∀ r s root msg, ¬IsLinked vp z.1.pk (.hmsg r s root msg) := fun _ _ _ _ => id
  rcases bad_event_or_logged_of_settled (shakePrimitives_byteLaws vp.params)
    (oracleSecret (shakeCore vp) (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed) z.1 _
    (QueryCache.simulateQ_toPartialImpl_mono hle _ ho.1)
    (fun x hx => QueryCache.simulateQ_toPartialImpl_mono hle _ (ho.2 x hx)) hv with
    htc | hhh | ⟨hit, hpt⟩ | hlog
  · rcases targetCollision_or_virtualHit_of_viewBy z ht htc with htc | hvh
    · exact .inl (.inl (.inl htc))
    · exact .inr (.inl hvh)
  · exact .inl (.inl (.inr (hiddenHitMixed_of_hiddenHit ht hm hhh)))
  · exact .inl (.inr ⟨(itsrCovered_congr fun r s root msg => ht.eqOn _ (hm r s root msg)).1 hit,
      hpt⟩)
  · exact absurd hlog hw.1

/-- On the support of the run of `romScheme` against any adversary, if an honest replay fails off
the linked points, the run's public-hash cache has an honest input at a linked point. -/
theorem linkedHonestInput_of_not_honestOffLinked
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeedDist : ProbComp (shakeCore vp).PkSeed}
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand pkSeedDist)}
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand pkSeedDist adv))
    (h : ¬HonestOffLinked vp z) : LinkedHonestInput vp z := by
  obtain ⟨-, -, hk, hl, -⟩ := settled_of_mem_support_romSchemeRun _ _ _ _ _ hz
  by_contra hn
  have hCF : ∀ t, ¬IsLinked vp z.1.pk t →
      z.2.fst t = QueryCache.filter (¬IsLinked vp z.1.pk ·) z.2.fst t := fun t ht => by
    simp only [QueryCache.filter_apply, ht, not_false_eq_true, ↓reduceIte]
  have ht : HonestTransfer (Equiv.refl _) z.1.pk.pkSeed z.1.sk.skSeed (IsLinked vp z.1.pk) z.2.fst
      (QueryCache.filter (¬IsLinked vp z.1.pk ·) z.2.fst) := by
    refine ⟨hCF, ?_⟩
    rintro (⟨t, hL, he⟩ | hs)
    · exact hn (.inl ⟨t, hL, (HonestTransfer.mk (fun t ht => (hCF t ht).symm) hn).honestEntry he⟩)
    · exact hn (.inr hs)
  exact h ⟨ht.keygen hk, fun x hx => ht.sign (fun _ _ _ _ => id) _ _ _ (hl x hx)⟩

/-! ## The headline -/

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, per public seed, by the events of the verifying
run.** At `n = 32` and `n ≤ m`, for every public seed `pkSeed` and every `opt_rand` distribution,
the strong advantage of an adversary against `shakeRomScheme` at `pkSeed` is at most the probability
that, in the three-oracle run of `romScheme` against the verifying adversary `verifyingAdv`, there
is a target collision on the public-hash cache or a mixed hidden-value hit on its view through the
linked redirect, the message-`PRF` key is hit at `opt_rand = PK.seed`, a virtual hit, an honest
input at a linked point, or interleaved-target coverage at a fresh `H_msg` point. -/
theorem shakeStrongAdvantage_pure_le_viewEvents
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    (h32 : vp.params.n = 32) (hnm : vp.params.n ≤ vp.params.m) (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
          (verifyingAdv vp h32.le hnm adv.toUnforgeableAdversary)}[
        ((RunTargetCollision (shakeCore vp) (Equiv.refl _) z ∨ RunHiddenHitMixed vp z) ∨
          (RunPrfKeyClash id pkSeed pkSeed z ∨ VirtualHit vp z ∨ LinkedHonestInput vp z)) ∨
        RunItsrCovered (shakeCore vp) z] := by
  refine (shakeStrongAdvantage_pure_le_verifyingAdv h32 hnm pkSeed adv).trans
    (prEvent_mono_of_support _ _ _ fun z hz h => ?_)
  by_cases ho : HonestOffLinked vp z
  · rcases h with (hw | hk) | hn
    · have := bad_event_of_redirectedWins z hw ho
      tauto
    · exact .inl (.inr (.inl hk))
    · exact absurd ho hn
  · exact .inl (.inr (.inr (.inr (linkedHonestInput_of_not_honestOffLinked hz ho))))

/-! ## Weak seeds -/

/-- If the address key held by the bytes of the public seed is not an honest key, a run point
has no virtual hit and no honest input at a linked point. -/
theorem not_virtualHit_and_not_linkedHonestInput
    (z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache)
    (hs : ¬IsHonestKey vp (shakeCore vp)
      (adrsKeyOfList vp (Vector.toList (z.1.pk.pkSeed : Bytes vp.params.n)))) :
    ¬VirtualHit vp z ∧ ¬LinkedHonestInput vp z := by
  have hkey : ∀ k : (shakeCore vp).AdrsKey, IsHonestKey vp (shakeCore vp) k →
      Vector.toList (k : Bytes 32) ≠ Vector.toList (z.1.pk.pkSeed : Bytes vp.params.n) :=
    fun k hk hks => hs (by rw [← hks]; convert hk using 1; exact bytesOfList_toList (k : Bytes 32))
  refine ⟨?_, ?_⟩
  · rintro ⟨k, xs, r, rest, u, hhon, ⟨-, hks, -⟩, -⟩
    exact hkey k (isHonestKey_of_honestEntry hhon) hks
  rintro (⟨⟨s, k, _ | ⟨r, rest⟩⟩ | _, hL, ht⟩ | ⟨a, b, ha, hab, hL⟩)
  · exact hL
  · obtain ⟨rfl, hks, -⟩ := hL
    exact hkey k (isHonestKey_of_honestEntry ht) hks
  · exact hL
  · exact hkey _ (isHonestKey_of_inl_mem_childAdrs ha hab) hL.2.1

end SLHDSA.Security
