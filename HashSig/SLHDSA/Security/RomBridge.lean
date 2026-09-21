/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CacheCoverage
public import HashSig.SLHDSA.Security.RomDescent
public import HashSig.SLHDSA.Security.SufResidual

/-!
# The random-oracle bad-event bridge

On the support of the instrumented counted random-oracle run (`romRunFull`), a winning forgery
exhibits one of the three events of `HashSig.SLHDSA.Security.RomDescent`, two read off the final
cache and one a property of the forgery's replay under it: a same-address target collision, a
hidden-value hit, or interleaved-target coverage — each conjoined with freshness of the forged
message for the signing log (`rom_bad_event_of_wins`), so that every term of a union bound over
the conclusion carries the conditioning.  The descent runs top-down from the cached public root:
key generation settles the honest root of the top tree at the value the forgery's verification
replay recovers there, `xmssLayer_cases` moves the descent one layer down for as long as the used
leaf's honest message is the one the replay presents, and `fors_cases` closes it at layer `0`.

Two facts feed the descent.  `exists_xmssSignM_eq_some_of_signFromPositionM` reads the honest
per-layer signing walk (FIPS 205 Algorithm 12) off the cache: a settled hypertree signing run has,
at every layer, a settled XMSS signature on some message and, below the top layer, a settled
recovery of the root from it.  `exists_honestMessage?_eq_some_of_usedLeaf` discharges the
hypothesis `xmssLayer_cases` leaves open: at a leaf some logged signature used, the honest message
is settled, because the logged signature signed there the root its own lower-layer XMSS signature
recovers — or, at layer `0`, the FORS public key its own recovery produced — and coverage
(`simulateQ_toPartialImpl_xmssRootM_eq_some_of_xmssSignM`,
`simulateQ_toPartialImpl_forsPkGenM_eq_some_of_forsSignM`) identifies that value with the settled
honest one.

`itsr_wins_of_itsrCovered` transports the coverage event: together with EUF-CMA freshness of the
forger's message it is a win in the interleaved-target subset-resilience game `hmsgItsrProblem`
against the targets embedded from the signing log, under every total answer function agreeing with
the cache.

## Scope

* Everything here is deterministic on the support of `romRunFull`: no probability is bounded, and
  the hash-query budget appears in no statement.
* The cache is a classical table, and the run is a classical random-oracle run; nothing here is
  quantum.
* No relation between the three events and a probability bound is proved here, and no
  tweakable-hash or ITSR advantage is bounded.
* The descent uses of a winning forgery only that its verification accepted; freshness of the
  forger's message for the signing log enters no step of it, and is conjoined to each of the three
  disjuncts once the descent has finished.
* `itsr_wins_of_itsrCovered` is not consumed by the bridge: it is stated against an arbitrary
  total answer function agreeing with the cache, and `rom_bad_event_of_wins` does not apply it.

## Labels

Four declarations.

*The honest signing walk*: `exists_xmssSignM_eq_some_of_signFromPositionM`.

*A used leaf's honest message*: `exists_honestMessage?_eq_some_of_usedLeaf`.

*The bridge*: `rom_bad_event_of_wins`.

*The ITSR transport*: `itsr_wins_of_itsrCovered`.

## References

- NIST FIPS 205, §7.1--§7.2 and §9.2--§9.3, Algorithms 12, 19 and 20
- Hülsing and Kudinov, “Recovering the Tight Security Proof of SPHINCS+”, for interleaved-target
  subset resilience
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec GeneralHypertree SignatureAlg CanonicalGames

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The honest signing walk -/

/-- From a settled Algorithm 12 run started at the layer-`n` position with `layers` layers left,
every layer `j ≥ n` has a settled XMSS signature at the layer-`j` position on some message, and
below the top layer the signer's own recovery of the root from it is settled. -/
theorem exists_xmssSignM_eq_some_of_signFromPositionM (c : PublicHash.Cache core)
    (sk : core.SkSeed) (pk : core.PkSeed) (parts : DigestParts vp.params) :
    ∀ (layers n : ℕ) (hnl : n + layers = vp.params.d) (hl : 0 < layers) (msg : core.Y)
      {sigs : Vector (XmssSig vp.params core) layers},
      simulateQ c.toPartialImpl (signFromPositionM vp core sk pk false
        (LayerPosition.atLayer vp parts ⟨n, by omega⟩) layers (by simp; omega) msg) =
          some sigs →
      ∀ j : Fin vp.params.d, n ≤ j.val → ∃ (m : core.Y) (sig : XmssSig vp.params core),
        simulateQ c.toPartialImpl (xmssSignM core m sk pk (LayerPosition.atLayer vp parts j).toAdrs
          (LayerPosition.atLayer vp parts j).leaf.val) = some sig ∧
        (j.val + 1 < vp.params.d → ∃ r, xmssPkFromSig? core c
          (LayerPosition.atLayer vp parts j).leaf.val sig m pk
          (LayerPosition.atLayer vp parts j).toAdrs = some r) := by
  intro layers
  induction layers with
  | zero => intro _ _ hl; omega
  | succ k ih =>
    intro n hnl _ msg sigs hsign j hj
    cases k with
    | zero =>
      rw [simulateQ_toPartialImpl_signFromPositionM_one_false_eq_some_iff] at hsign
      obtain ⟨sig, hsig, -⟩ := hsign
      obtain ⟨jv, hjlt⟩ := j
      obtain rfl : jv = n := by simp at hj; omega
      exact ⟨msg, sig, hsig, fun h => by omega⟩
    | succ k =>
      obtain ⟨sig, root, rest, hsig, hrec, hrest, -⟩ :=
        (simulateQ_toPartialImpl_signFromPositionM_add_two_eq_some_iff core c sk pk false _ k _
          msg).mp hsign
      rcases Nat.eq_or_lt_of_le hj with hjn | hjn
      · obtain ⟨jv, hjlt⟩ := j
        simp only at hjn
        subst hjn
        exact ⟨msg, sig, hsig, fun _ => ⟨root, hrec⟩⟩
      · have hrest' : simulateQ c.toPartialImpl (signFromPositionM vp core sk pk false
            (LayerPosition.atLayer vp parts ⟨n + 1, by omega⟩) (k + 1) (by simp; omega) root) =
              some rest := by
          have hnext := LayerPosition.atLayer_succ_eq_next vp parts ⟨n, by omega⟩
            (by simp; omega)
          simp only at hnext
          rw [signFromPositionM_pos_congr c sk pk false hnext]
          exact hrest
        exact ih (n + 1) (by omega) (Nat.succ_pos k) root hrest' j hjn

/-! ## A used leaf's honest message -/

/-- A used leaf's honest message is settled: the logged signature that passes through `pos` signed
there the root its own lower-layer XMSS signature recovers, which by coverage
(`simulateQ_toPartialImpl_xmssRootM_eq_some_of_xmssSignM`) is the settled honest root of the child
tree; at layer `0` it signed the FORS public key its own recovery produced, which by
`simulateQ_toPartialImpl_forsPkGenM_eq_some_of_forsSignM` is the settled honest FORS public key. -/
theorem exists_honestMessage?_eq_some_of_usedLeaf [SampleableType core.Y] [DecidableEq core.Y]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
    (adv : unforgeableAdv (generalAlgM (m := OracleComp (unifSpec + publicHashSpec core)) vp core))
    {z : RomOutcome vp core × PublicHash.Cache core} (hz : z ∈ support (romRunFull core adv))
    (j : Fin vp.params.d) (pos : LayerPosition vp) (hused : UsedLeaf z.1 z.2 j pos) :
    ∃ m, honestMessage? z.2 z.1.sk.skSeed z.1.pk.pkSeed pos = some m := by
  obtain ⟨e, he, digest, hd, rfl⟩ := hused
  obtain ⟨⟨skSeed, skPrf, pkSeed, hk⟩, hlog, -⟩ :=
    simulateQ_toPartialImpl_eq_some_of_mem_support_romRunFull core adv hz
  rw [simulateQ_toPartialImpl_keygenInternalM_eq_some_iff] at hk
  obtain ⟨pkRoot, -, hpkeq, hskeq⟩ := hk
  have hseed : z.1.sk.pkSeed = z.1.pk.pkSeed := by rw [← hpkeq, ← hskeq]
  have hroot : z.1.sk.pkRoot = z.1.pk.pkRoot := by rw [← hpkeq, ← hskeq]
  obtain ⟨addrnd, hs⟩ := hlog e he
  obtain ⟨-, digest', forsPk, hd', hfs, hfp, hht⟩ :=
    components_of_simulateQ_toPartialImpl_signInternalM core z.2 _ _ _ hs
  rw [hseed, hroot] at hd'
  rw [hseed] at hfs hfp hht
  obtain rfl : digest = digest' := Option.some.inj (hd.symm.trans hd')
  set parts := splitDigest vp.params digest
  unfold honestMessage?
  split_ifs with h0
  · obtain rfl : j = ⟨0, vp.valid.d_pos⟩ := Fin.ext (by simpa using h0)
    rw [LayerPosition.atLayer_zero_eq_initial, forsInstanceAdrs_initial]
    exact ⟨forsPk,
      simulateQ_toPartialImpl_forsPkGenM_eq_some_of_forsSignM core z.2 _ _ _ _ hfs hfp⟩
  · obtain ⟨jv, hjlt⟩ := j
    simp only [LayerPosition.atLayer_layer_val] at h0
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hd1 : (vp.params.d == 1) = false := by simp; omega
    simp only [GeneralHypertree.signM, hd1] at hht
    have hht' : simulateQ z.2.toPartialImpl (signFromPositionM vp core z.1.sk.skSeed
        z.1.pk.pkSeed false (LayerPosition.atLayer vp parts ⟨0, vp.valid.d_pos⟩) vp.params.d
        (by simp) forsPk) = some e.2.hypertree := hht
    obtain ⟨m, sig, hsign, hrec⟩ := exists_xmssSignM_eq_some_of_signFromPositionM z.2 _ _ parts
      vp.params.d 0 (by simp) vp.valid.d_pos forsPk hht' ⟨j', by omega⟩ (Nat.zero_le _)
    obtain ⟨r, hr⟩ := hrec (by omega)
    refine ⟨r, ?_⟩
    rw [LayerPosition.atLayer_succ_eq_next vp parts ⟨j', by omega⟩ (by simpa using hjlt),
      childTreeAdrs_next]
    exact simulateQ_toPartialImpl_xmssRootM_eq_some_of_xmssSignM core z.2 m _ _ _ _ hsign
      (LayerPosition.atLayer vp parts ⟨j', by omega⟩).leaf.isLt hr

/-! ## The bridge -/

section Bridge

variable [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] [SampleableType core.PkSeed]

/-- **The random-oracle bad-event bridge.**  On the support of the instrumented run, a winning
forgery exhibits a same-address target collision, or a hidden-value hit, or interleaved-target
coverage — the first and the last read off the final cache, the hidden-value hit a property of the
forgery's replay under it — and in each case the forged message is fresh for the signing log.  The
descent runs top-down: key generation settles the top tree at the forger's recovered value,
`xmssLayer_cases` moves one layer down as long as the used leaf's honest message is the forger's,
and `fors_cases` closes at layer `0`.  Freshness is carried by all three disjuncts so that a union
bound over the conclusion is conditioned term by term.  It is indispensable for the coverage
disjunct, which without it holds over the whole support: an adversary that replays a logged
signature on the message it was issued for covers every coordinate of its own digest while not
winning.  For that disjunct it is also exactly the hypothesis `itsr_wins_of_itsrCovered` takes. -/
theorem rom_bad_event_of_wins (laws : core.ByteLaws)
    (adv : unforgeableAdv (generalAlgM (m := OracleComp (unifSpec + publicHashSpec core)) vp core))
    {z : RomOutcome vp core × PublicHash.Cache core} (hz : z ∈ support (romRunFull core adv))
    (hw : z.1.wins = true) :
    (TargetCollision z.1 z.2 ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)) ∨
      (HiddenHit z.1 z.2 ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)) ∨
      (ItsrCovered z.1 z.2 ∧ z.1.msg ∉ z.1.log.map (fun e => e.1)) := by
  obtain ⟨hfresh, hv⟩ := (RomOutcome.wins_eq_true_iff z.1).mp hw
  suffices h : TargetCollision z.1 z.2 ∨ HiddenHit z.1 z.2 ∨ ItsrCovered z.1 z.2 by
    exact h.imp (⟨·, hfresh⟩) (Or.imp (⟨·, hfresh⟩) (⟨·, hfresh⟩))
  obtain ⟨⟨skSeed, skPrf, pkSeed, hk⟩, -, hver⟩ :=
    simulateQ_toPartialImpl_eq_some_of_mem_support_romRunFull core adv hz
  rw [hv, simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff] at hver
  obtain ⟨digest, forsPk, hd, hfors, hpk⟩ := hver
  rw [simulateQ_toPartialImpl_pkFromSigM_eq] at hpk
  set parts := splitDigest vp.params digest
  rw [simulateQ_toPartialImpl_keygenInternalM_eq_some_iff] at hk
  obtain ⟨pkRoot, hroot, hpkeq, hskeq⟩ := hk
  have hlayers := forgerLayers_of_recoverFromPositionM z.2 z.1.pk.pkSeed parts z.1.sig.hypertree
    forsPk vp.params.d 0 (by simp) vp.valid.d_pos forsPk z.1.sig.hypertree rfl
    (fun k hk => by simp) hpk
  -- one layer of the descent: from the settled honest root at the forger's recovered value
  have hstep : ∀ (j : Fin vp.params.d) (m r : core.Y),
      forgerMessage? z.2 z.1.pk.pkSeed parts z.1.sig.hypertree forsPk j j.isLt = some m →
      xmssPkFromSig? core z.2 (LayerPosition.atLayer vp parts j).leaf.val z.1.sig.hypertree[j] m
        z.1.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs = some r →
      xmssRoot? core z.2 z.1.sk.skSeed z.1.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs =
        some r →
      TargetCollision z.1 z.2 ∨ HiddenHit z.1 z.2 ∨
        honestMessage? z.2 z.1.sk.skSeed z.1.pk.pkSeed (LayerPosition.atLayer vp parts j) =
          some m := by
    intro j m r hm hf hh
    exact (xmssLayer_cases laws z.1 z.2 j _ m ⟨digest, forsPk, hd, hfors, rfl, hm⟩ hf hh
      (exists_honestMessage?_eq_some_of_usedLeaf adv hz j _)).imp id (Or.imp id And.right)
  have bind3 : ∀ {P Q : Prop}, (TargetCollision z.1 z.2 ∨ HiddenHit z.1 z.2 ∨ P) →
      (P → TargetCollision z.1 z.2 ∨ HiddenHit z.1 z.2 ∨ Q) →
      TargetCollision z.1 z.2 ∨ HiddenHit z.1 z.2 ∨ Q :=
    fun h f => h.elim Or.inl fun h => h.elim (Or.inr ∘ Or.inl) f
  -- downward induction from the top tree: the honest root at layer `j` is settled at the
  -- forger's recovered value there
  have key : ∀ (i : ℕ) (j : Fin vp.params.d), j.val + i + 1 = vp.params.d →
      TargetCollision z.1 z.2 ∨ HiddenHit z.1 z.2 ∨ ∃ m r,
        forgerMessage? z.2 z.1.pk.pkSeed parts z.1.sig.hypertree forsPk j j.isLt = some m ∧
        xmssPkFromSig? core z.2 (LayerPosition.atLayer vp parts j).leaf.val z.1.sig.hypertree[j]
          m z.1.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs = some r ∧
        xmssRoot? core z.2 z.1.sk.skSeed z.1.pk.pkSeed
          (LayerPosition.atLayer vp parts j).toAdrs = some r := by
    intro i
    induction i with
    | zero =>
      intro j hj
      obtain ⟨m, r, hm, hf, hr⟩ := hlayers j (Nat.zero_le _)
      obtain rfl := hr (by omega)
      refine Or.inr (Or.inr ⟨m, _, hm, hf, ?_⟩)
      rw [LayerPosition.toAdrs_eq_layerAdrs_of_isFinal _ (by simp; omega), ← hpkeq, ← hskeq]
      exact hroot
    | succ i ih =>
      intro j hj
      refine bind3 (ih ⟨j.val + 1, by omega⟩ (by simp; omega)) fun ⟨m', r', hm', hf', hh'⟩ => ?_
      obtain ⟨m, r, hm, hf, -⟩ := hlayers j (Nat.zero_le _)
      have hnext : forgerMessage? z.2 z.1.pk.pkSeed parts z.1.sig.hypertree forsPk (j.val + 1)
          (by omega) = some r := by
        change (forgerMessage? z.2 z.1.pk.pkSeed parts z.1.sig.hypertree forsPk j.val _).bind _ =
          some r
        rw [hm, Option.bind_some]
        exact hf
      rw [hnext] at hm'
      obtain rfl := Option.some.inj hm'
      refine bind3 (hstep ⟨j.val + 1, by omega⟩ r r' hnext hf' hh') fun h => ?_
      refine Or.inr (Or.inr ⟨m, r, hm, hf, ?_⟩)
      simp only [honestMessage?, LayerPosition.atLayer_layer_val, Nat.add_one_ne_zero,
        ↓reduceIte] at h
      rwa [LayerPosition.atLayer_succ_eq_next vp parts j (by omega), childTreeAdrs_next] at h
  refine bind3 (key (vp.params.d - 1) ⟨0, vp.valid.d_pos⟩
    (by have := vp.valid.d_pos; simp; omega)) fun ⟨m, r, hm, hf, hh⟩ => ?_
  refine bind3 (hstep ⟨0, vp.valid.d_pos⟩ m r hm hf hh) fun h => ?_
  obtain rfl : forsPk = m := Option.some.inj hm
  simp only [honestMessage?, LayerPosition.atLayer_zero_eq_initial,
    LayerPosition.initial_layer_val, forsInstanceAdrs_initial, ↓reduceIte] at h
  exact fors_cases z.1 z.2 digest hd forsPk hfors h

end Bridge

/-! ## The ITSR transport -/

/-- `ItsrCovered` together with the EUF-CMA freshness of the forger's message is the ITSR win
against the logged targets under every total answer function agreeing with the cache;
`emptyContextMessage_injective` supplies the candidate-fresh conjunct. -/
theorem itsr_wins_of_itsrCovered [SampleableType core.Y] [DecidableEq core.PkSeed]
    [DecidableEq core.Y] (o : RomOutcome vp core) (c : PublicHash.Cache core)
    {f : QueryImpl (publicHashSpec core) Id} (hf : c.AgreesWithFn f) (hcov : ItsrCovered o c)
    (hfresh : o.msg ∉ o.log.map (fun e => e.1)) :
    (hmsgItsrProblem (PublicHash.withPublicHash core f)).Wins
      (embedTargets (PublicHash.withPublicHash core f) o.pk.pkSeed o.pk.pkRoot
        (logQueries (prims := PublicHash.withPublicHash core f) (internalLog o.log)))
      (o.sig.randomness, ⟨o.pk.pkSeed, o.pk.pkRoot, emptyContextMessage o.msg⟩) := by
  obtain ⟨digest, hd, hcov⟩ := hcov
  unfold KeyedHash.ITSRProblem.Wins
  refine ⟨notMem_embedTargets_of_notMem _ _ fun hmem => hfresh ?_, fun i hi => ?_⟩
  · rw [logQueries_eq, internalLog_eq, List.map_map, List.mem_map] at hmem
    obtain ⟨e, he, heq⟩ := hmem
    simp only [Function.comp, Prod.mk.injEq] at heq
    exact List.mem_map.mpr ⟨e, he, emptyContextMessage_injective heq.2⟩
  · simp only [KeyedHash.ITSRProblem.indexSet, hmsgItsrProblem_indices, hmsgItsrProblem_hash,
      hf hd] at hi
    obtain ⟨e, he, digest', hd', hi'⟩ := hcov i hi
    simp only [KeyedHash.ITSRProblem.targetIndexSet, List.mem_flatMap]
    refine ⟨(e.2.randomness, ⟨o.pk.pkSeed, o.pk.pkRoot, emptyContextMessage e.1⟩), ?_, ?_⟩
    · rw [mem_embedTargets_iff, logQueries_eq, internalLog_eq, List.map_map, List.mem_map]
      exact ⟨e, he, rfl⟩
    · simpa only [KeyedHash.ITSRProblem.indexSet, hmsgItsrProblem_indices, hmsgItsrProblem_hash,
        hf hd'] using hi'

end SLHDSA.Security
