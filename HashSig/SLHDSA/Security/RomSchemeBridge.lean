/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomSchemeRun

/-!
# The random-oracle bad-event bridge for SLH-DSA with both PRFs inside the oracle

A cache on which key generation, every logged signature and the forgery's accepting
verification replay exhibits one of the three events of `HashSig.SLHDSA.Security.RomDescentSecret`:
a same-address target collision, a hidden-value hit or interleaved-target coverage
(`bad_event_of_settled`).  Under the same hypotheses, coverage can be required at an `H_msg` point
(randomizer and message) that is the point of no logged signature, at the price of a fourth
disjunct, the forged pair of message and signature being logged (`bad_event_or_logged_of_settled`).
On the support of `romSchemeRun` the final cache settles all three replays at the run's own provider
`oracleSecret core e o.pk.pkSeed o.sk.skSeed` and public seed, so a forgery whose pair of message
and signature was never returned by the signing oracle exhibits a target collision, a hidden-value
hit, or coverage at a fresh `H_msg` point there (`bad_event_of_strongWins_romSchemeRun`).  The
provider and the seed are fixed by the run, not chosen by the caller.

The descent runs top-down from the cached public root (`bad_event_or_honest_descent_of_settled`):
key generation settles the honest root of the top tree at the value the forgery's verification
recovers there, `xmssLayer_cases` moves the descent one layer down for as long as the used leaf's
honest message is the one the verification presents, and at layer `0` it reaches the honest FORS
public key.  There `fors_cases` closes it.  If instead the forgery's `H_msg` point is that of a
logged signature, the digest is that signature's, so every layer is at the logged position and
every message on the way down is the honest one:
`targetCollision_or_xmssSignWithSecret_eq_some` and `targetCollision_or_eq_of_forsSignWithSecret`
identify each layer and the FORS signature with the logged ones unless a target collision occurs.
Two facts feed the descent: `exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret` reads
the honest per-layer signing walk (FIPS 205 Algorithm 12) off the cache, from which
`exists_honestMessage?_xmssSignWithSecret_of_loggedDigest` identifies every layer of a logged
signature with the honest XMSS signature on the honest message there, and
`exists_honestMessage?_eq_some_of_usedLeaf` settles the honest message at every leaf a logged
signature used.

## Scope

* Everything here is deterministic: no probability is bounded, and no query budget appears.
* Coverage cannot be dropped: a fresh message whose digest selects a FORS instance and indices
  all revealed by logged signatures there is forged, with no collision and no hit, from the
  revealed FORS values and a logged hypertree signature for that instance.
* Coverage at a logged `H_msg` point is free: replaying a logged randomizer on its own message
  covers every coordinate of its digest.  So the coverage disjunct of the strong bridge carries
  freshness of the point, and the same-point case is closed by target collisions alone.
* Nothing here is quantum.

## Labels

*The honest signing walk*: `exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret`.

*The layers of a logged signature*: `exists_honestMessage?_xmssSignWithSecret_of_loggedDigest`,
`exists_honestMessage?_eq_some_of_usedLeaf`.

*The descent*: `bad_event_or_honest_descent_of_settled`.

*The bridges on a settled cache*: `bad_event_of_settled`, `bad_event_or_logged_of_settled`.

*The bridge on the run*: `bad_event_of_strongWins_romSchemeRun`.

## References

- NIST FIPS 205, §7.1--§7.2 and §9.2--§9.3, Algorithms 12, 19 and 20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec GeneralHypertree SignatureAlg CanonicalGames

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-! ## The honest signing walk -/

/-- A settled one-layer Algorithm 12 run over a provider is a settled XMSS signature on its
message at its position. -/
private theorem exists_xmssSignWithSecret_of_signFromPositionWithSecret_one
    (c : PublicHash.Cache core) (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (pk : core.PkSeed) (recoverFinal : Bool) (pos : LayerPosition vp)
    (h : pos.layer.val + 1 = vp.params.d) (msg : core.Y)
    {sigs : Vector (XmssSig vp.params core) 1}
    (hsign : simulateQ c.toPartialImpl (GeneralHypertree.signFromPositionWithSecret core
      (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) secret recoverFinal
      pos 1 h msg) = some sigs) :
    ∃ sig : XmssSig vp.params core,
      simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) secret msg pos.toAdrs pos.leaf.val) =
          some sig ∧ #v[sig] = sigs := by
  cases recoverFinal
  · exact (simulateQ_toPartialImpl_signFromPositionWithSecret_one_false_eq_some_iff core c secret
      pk _ _ msg).mp hsign
  · revert hsign
    simp only [GeneralHypertree.signFromPositionWithSecret_one, simulateQ_bind_eq_some_iff,
      simulateQ_pure_eq_some_iff, ↓reduceIte]
    rintro ⟨sig, hsig, _, _, rfl⟩
    exact ⟨sig, hsig, rfl⟩

/-- From a settled Algorithm 12 run over a provider, started at the layer-`n` position with
`layers` layers left and signing `msg`, the `i`-th returned XMSS signature is the settled XMSS
signature over the provider at the layer-`(n + i)` position on some message: `msg` at `i = 0`,
and above it the root the signer's own recovery from the signature one layer below returns. -/
theorem exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret
    (c : PublicHash.Cache core) (secret : Adrs → OracleComp (publicHashSpec core) core.Y)
    (pk : core.PkSeed) (parts : DigestParts vp.params) :
    ∀ (layers n : ℕ) (hnl : n + layers = vp.params.d) (hl : 0 < layers) (msg : core.Y)
      (recoverFinal : Bool) {sigs : Vector (XmssSig vp.params core) layers},
      simulateQ c.toPartialImpl (signFromPositionWithSecret core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) secret recoverFinal
        (LayerPosition.atLayer vp parts ⟨n, by omega⟩) layers (by simp; omega) msg) =
          some sigs →
      ∀ (i : ℕ) (hi : i < layers), ∃ m : core.Y,
        simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
          (PublicHash.tl core pk) (PublicHash.h core pk) secret m
          (LayerPosition.atLayer vp parts ⟨n + i, by omega⟩).toAdrs
          (LayerPosition.atLayer vp parts ⟨n + i, by omega⟩).leaf.val) = some sigs[i] ∧
        (i = 0 → m = msg) ∧
        (∀ i' (hi' : i = i' + 1), ∃ m₀ : core.Y,
          simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core pk)
            (PublicHash.tl core pk) (PublicHash.h core pk) secret m₀
            (LayerPosition.atLayer vp parts ⟨n + i', by omega⟩).toAdrs
            (LayerPosition.atLayer vp parts ⟨n + i', by omega⟩).leaf.val) =
              some (sigs[i']'(by omega)) ∧
          xmssPkFromSig? core c (LayerPosition.atLayer vp parts ⟨n + i', by omega⟩).leaf.val
            (sigs[i']'(by omega)) m₀ pk
            (LayerPosition.atLayer vp parts ⟨n + i', by omega⟩).toAdrs = some m) := by
  intro layers
  induction layers with
  | zero => intro _ _ hl; omega
  | succ k ih =>
    intro n hnl _ msg rf sigs hsign i hi
    cases k with
    | zero =>
      obtain ⟨sig, hsig, rfl⟩ :=
        exists_xmssSignWithSecret_of_signFromPositionWithSecret_one c secret pk rf _ _ msg hsign
      obtain rfl : i = 0 := by omega
      exact ⟨msg, by simpa using hsig, fun _ => rfl, fun i' h => by omega⟩
    | succ k =>
      obtain ⟨sig, root, rest, hsig, hrec, hrest, rfl⟩ :=
        (simulateQ_toPartialImpl_signFromPositionWithSecret_add_two_eq_some_iff core c secret pk
          rf _ k _ msg).mp hsign
      have hrest' : simulateQ c.toPartialImpl (signFromPositionWithSecret core
          (PublicHash.f core pk) (PublicHash.tl core pk) (PublicHash.h core pk) secret false
          (LayerPosition.atLayer vp parts ⟨n + 1, by omega⟩) (k + 1) (by simp; omega) root) =
            some rest := by
        have hnext := LayerPosition.atLayer_succ_eq_next vp parts ⟨n, by omega⟩ (by simp; omega)
        simp only at hnext
        rw [signFromPositionWithSecret_pos_congr secret c pk false hnext]
        exact hrest
      have hpos : ∀ j (h₁ : n + 1 + j < vp.params.d) (h₂ : n + (j + 1) < vp.params.d),
          LayerPosition.atLayer vp parts ⟨n + 1 + j, h₁⟩ =
            LayerPosition.atLayer vp parts ⟨n + (j + 1), h₂⟩ :=
        fun j _ _ => congrArg _ (Fin.ext (by simp only; omega))
      rcases i with _ | i
      · exact ⟨msg, by simpa using hsig, fun _ => rfl, fun i' h => by omega⟩
      obtain ⟨m, hm, hm0, hmi⟩ := ih (n + 1) (by omega) (by omega) root false hrest' i (by omega)
      refine ⟨m, ?_, fun h => by omega, fun i' hi' => ?_⟩
      · rw [Vector.getElem_insertIdx_of_gt (by omega) (by omega), ← hpos i (by omega)]
        simpa using hm
      obtain rfl : i = i' := by omega
      rcases i with _ | i
      · obtain rfl := hm0 rfl
        exact ⟨msg, by simpa using hsig, by simpa [xmssPkFromSig?] using hrec⟩
      obtain ⟨m₀, hm₀, hpk⟩ := hmi i rfl
      refine ⟨m₀, ?_, ?_⟩ <;>
        rw [Vector.getElem_insertIdx_of_gt (by omega) (by omega), ← hpos i (by omega)]
      · simpa using hm₀
      · simpa using hpk

/-! ## The layers of a logged signature -/

/-- Every layer `j` of a signature replayed on `c` at its own randomizer is the settled honest
XMSS signature at its layer-`j` position on the settled honest message there. -/
theorem exists_honestMessage?_xmssSignWithSecret_of_loggedDigest
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    {x : (t : (List Byte →ₒ GeneralScheme.SignatureCore vp core).Domain) ×
      (List Byte →ₒ GeneralScheme.SignatureCore vp core).Range t}
    (hx : simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    {digest : Bytes vp.params.m} (hd : LoggedDigest o c x digest) (j : Fin vp.params.d) :
    ∃ m, honestMessage? c secret o.pk.pkSeed
        (LayerPosition.atLayer vp (splitDigest vp.params digest) j) = some m ∧
      simulateQ c.toPartialImpl (xmssSignWithSecret core (PublicHash.f core o.pk.pkSeed)
        (PublicHash.tl core o.pk.pkSeed) (PublicHash.h core o.pk.pkSeed) secret m
        (LayerPosition.atLayer vp (splitDigest vp.params digest) j).toAdrs
        (LayerPosition.atLayer vp (splitDigest vp.params digest) j).leaf.val) =
          some x.2.hypertree[j] := by
  obtain ⟨-, digest', forsPk, hd', hfs, hfp, hht⟩ :=
    components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM core c _ _ _ _ _ hx
  obtain rfl : digest = digest' := Option.some.inj (hd.symm.trans hd')
  set parts := splitDigest vp.params digest
  simp only [GeneralHypertree.signWithSecretM, GeneralHypertree.signWithSecret] at hht
  rw [signFromPositionWithSecret_pos_congr secret c _ _
    (LayerPosition.atLayer_zero_eq_initial vp parts).symm] at hht
  obtain ⟨jv, hjlt⟩ := j
  obtain ⟨m, hm, hm0, hmi⟩ := exists_xmssSignWithSecret_eq_some_of_signFromPositionWithSecret c
    secret o.pk.pkSeed parts vp.params.d 0 (by simp) vp.valid.d_pos forsPk _ hht jv hjlt
  simp only [Nat.zero_add] at hm hmi
  refine ⟨m, ?_, hm⟩
  rcases jv with _ | j'
  · obtain rfl := hm0 rfl
    simp only [honestMessage?, LayerPosition.atLayer_zero_eq_initial,
      LayerPosition.initial_layer_val, forsInstanceAdrs_initial, ↓reduceIte]
    exact forsPkGenWithSecret?_eq_some_of_forsSignWithSecret core c _ _ _ _ hfs hfp
  obtain ⟨m₀, hm₀, hpk⟩ := hmi j' rfl
  simp only [honestMessage?, LayerPosition.atLayer_layer_val, Nat.add_one_ne_zero, ↓reduceIte]
  rw [LayerPosition.atLayer_succ_eq_next vp parts ⟨j', by omega⟩ (by simpa using hjlt),
    childTreeAdrs_next]
  exact xmssRootWithSecret?_eq_some_of_xmssSignWithSecret core c _ m₀ _ _ _ hm₀
    (LayerPosition.atLayer vp parts ⟨j', by omega⟩).leaf.isLt hpk

/-- If every logged signature of `o` replays on `c` at its own randomizer, a used leaf's honest
message is settled. -/
theorem exists_honestMessage?_eq_some_of_usedLeaf
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    (hlog : ∀ x ∈ o.log, simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    (j : Fin vp.params.d) (pos : LayerPosition vp) (hused : UsedLeaf o c j pos) :
    ∃ m, honestMessage? c secret o.pk.pkSeed pos = some m := by
  obtain ⟨x, hx, digest, hd, rfl⟩ := hused
  obtain ⟨m, hm, -⟩ :=
    exists_honestMessage?_xmssSignWithSecret_of_loggedDigest secret o c (hlog x hx) hd j
  exact ⟨m, hm⟩

/-! ## The descent from the cached root -/

/-- **The descent from the cached root.**  If key generation at `secret` replays on `c` to the
public root of `o`, every logged signature of `o` replays on `c` at its own randomizer, and the
verification of the forgery replays on `c` to `true`, then `c` exhibits a same-address target
collision or a hidden-value hit, or the forgery's digest and recovered FORS public key are settled
and at every layer the message the verification presents is the settled honest message at the
layer's position, and the forgery's XMSS signature there recovers the settled honest root. -/
theorem bad_event_or_honest_descent_of_settled [DecidableEq core.Y] (laws : core.ByteLaws)
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    (hroot : simulateQ c.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM core secret o.pk.pkSeed) = some o.pk.pkRoot)
    (hlog : ∀ x ∈ o.log, simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    (hver : simulateQ c.toPartialImpl
      (GeneralScheme.verifyInternalM vp core o.msg o.sig o.pk) = some true) :
    TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨
      ∃ digest forsPk, ForgerDigest o c digest ∧
        forsPkFromSig? core c o.sig.fors (splitDigest vp.params digest).md.toList o.pk.pkSeed
          (splitDigest vp.params digest).forsAdrs = some forsPk ∧
        ∀ j : Fin vp.params.d, ∃ m r,
          forgerMessage? c o.pk.pkSeed (splitDigest vp.params digest) o.sig.hypertree forsPk j
            j.isLt = some m ∧
          xmssPkFromSig? core c (LayerPosition.atLayer vp (splitDigest vp.params digest) j).leaf.val
            o.sig.hypertree[j] m o.pk.pkSeed
            (LayerPosition.atLayer vp (splitDigest vp.params digest) j).toAdrs = some r ∧
          xmssRootWithSecret? core c secret o.pk.pkSeed
            (LayerPosition.atLayer vp (splitDigest vp.params digest) j).toAdrs = some r ∧
          honestMessage? c secret o.pk.pkSeed
            (LayerPosition.atLayer vp (splitDigest vp.params digest) j) = some m := by
  rw [simulateQ_toPartialImpl_verifyInternalM_eq_some_true_iff] at hver
  obtain ⟨digest, forsPk, hd, hfors, hpk⟩ := hver
  rw [simulateQ_toPartialImpl_pkFromSigM_eq] at hpk
  set parts := splitDigest vp.params digest
  refine or_iff_not_imp_left.mpr fun hTC => or_iff_not_imp_left.mpr fun hHH => ?_
  have hlayers := forgerLayers_of_recoverFromPositionM c o.pk.pkSeed parts o.sig.hypertree
    forsPk vp.params.d 0 (by simp) vp.valid.d_pos forsPk o.sig.hypertree rfl
    (fun k hk => by simp) hpk
  have hstep : ∀ (j : Fin vp.params.d) (m r : core.Y),
      forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk j j.isLt = some m →
      xmssPkFromSig? core c (LayerPosition.atLayer vp parts j).leaf.val o.sig.hypertree[j] m
        o.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs = some r →
      xmssRootWithSecret? core c secret o.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs =
        some r →
      honestMessage? c secret o.pk.pkSeed (LayerPosition.atLayer vp parts j) = some m :=
    fun j m r hm hf hh => (((xmssLayer_cases secret laws o c j _ m
      ⟨digest, forsPk, hd, hfors, rfl, hm⟩ hf hh
      (exists_honestMessage?_eq_some_of_usedLeaf secret o c hlog j _)).resolve_left
        hTC).resolve_left hHH).2
  have key : ∀ (i : ℕ) (j : Fin vp.params.d), j.val + i + 1 = vp.params.d → ∃ m r,
      forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk j j.isLt = some m ∧
      xmssPkFromSig? core c (LayerPosition.atLayer vp parts j).leaf.val o.sig.hypertree[j]
        m o.pk.pkSeed (LayerPosition.atLayer vp parts j).toAdrs = some r ∧
      xmssRootWithSecret? core c secret o.pk.pkSeed
        (LayerPosition.atLayer vp parts j).toAdrs = some r := by
    intro i
    induction i with
    | zero =>
      intro j hj
      obtain ⟨m, r, hm, hf, hr⟩ := hlayers j (Nat.zero_le _)
      obtain rfl := hr (by omega)
      refine ⟨m, _, hm, hf, ?_⟩
      rw [LayerPosition.toAdrs_eq_layerAdrs_of_isFinal _ (by simp; omega)]
      exact hroot
    | succ i ih =>
      intro j hj
      obtain ⟨m', r', hm', hf', hh'⟩ := ih ⟨j.val + 1, by omega⟩ (by simp; omega)
      obtain ⟨m, r, hm, hf, -⟩ := hlayers j (Nat.zero_le _)
      have hnext : forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk (j.val + 1)
          (by omega) = some r := by
        change (forgerMessage? c o.pk.pkSeed parts o.sig.hypertree forsPk j.val _).bind _ =
          some r
        rw [hm, Option.bind_some]
        exact hf
      rw [hnext] at hm'
      obtain rfl := Option.some.inj hm'
      have h := hstep ⟨j.val + 1, by omega⟩ r r' hnext hf' hh'
      refine ⟨m, r, hm, hf, ?_⟩
      simp only [honestMessage?, LayerPosition.atLayer_layer_val, Nat.add_one_ne_zero,
        ↓reduceIte] at h
      rwa [LayerPosition.atLayer_succ_eq_next vp parts j (by omega), childTreeAdrs_next] at h
  refine ⟨digest, forsPk, hd, hfors, fun j => ?_⟩
  obtain ⟨m, r, hm, hf, hh⟩ := key (vp.params.d - 1 - j.val) j (by have := j.isLt; omega)
  exact ⟨m, r, hm, hf, hh, hstep j m r hm hf hh⟩

/-! ## The bridges on a settled cache -/

/-- **The random-oracle bad-event bridge on a settled cache.**  If key generation at `secret`
replays on `c` to the public root of `o`, every logged signature of `o` replays on `c` at its own
randomizer, and the verification of the forgery replays on `c` to `true`, then `c` exhibits a
same-address target collision, or a hidden-value hit, or interleaved-target coverage. -/
theorem bad_event_of_settled [DecidableEq core.Y] (laws : core.ByteLaws)
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    (hroot : simulateQ c.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM core secret o.pk.pkSeed) = some o.pk.pkRoot)
    (hlog : ∀ x ∈ o.log, simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    (hver : simulateQ c.toPartialImpl
      (GeneralScheme.verifyInternalM vp core o.msg o.sig o.pk) = some true) :
    TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨ ItsrCovered o c := by
  rcases bad_event_or_honest_descent_of_settled laws secret o c hroot hlog hver with
    h | h | ⟨digest, forsPk, hd, hfors, hall⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  obtain ⟨m, r, hm, -, -, h⟩ := hall ⟨0, vp.valid.d_pos⟩
  obtain rfl : forsPk = m := Option.some.inj hm
  simp only [honestMessage?, LayerPosition.atLayer_zero_eq_initial,
    LayerPosition.initial_layer_val, forsInstanceAdrs_initial, ↓reduceIte] at h
  exact fors_cases secret o c digest hd forsPk hfors h

/-- **The strong bridge on a settled cache.**  Under the hypotheses of `bad_event_of_settled`,
`c` exhibits a same-address target collision, or a hidden-value hit, or interleaved-target
coverage while the forgery's `H_msg` point (randomizer and message) is the point of no logged
signature; or the forged pair of message and signature is logged. -/
theorem bad_event_or_logged_of_settled [DecidableEq core.Y] (laws : core.ByteLaws)
    (secret : Adrs → OracleComp (publicHashSpec core) core.Y) (o : RomOutcome vp core)
    (c : PublicHash.Cache core)
    (hroot : simulateQ c.toPartialImpl
      (GeneralScheme.keygenInternalWithSecretM core secret o.pk.pkSeed) = some o.pk.pkRoot)
    (hlog : ∀ x ∈ o.log, simulateQ c.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core secret x.1 o.pk.pkSeed o.pk.pkRoot
        x.2.randomness) = some x.2)
    (hver : simulateQ c.toPartialImpl
      (GeneralScheme.verifyInternalM vp core o.msg o.sig o.pk) = some true) :
    TargetCollision secret o.pk.pkSeed c ∨ HiddenHit secret o c ∨
      (ItsrCovered o c ∧
        (o.sig.randomness, o.msg) ∉ o.log.map (fun e => (e.2.randomness, e.1))) ∨
      ⟨o.msg, o.sig⟩ ∈ o.log := by
  by_cases hpt : (o.sig.randomness, o.msg) ∈ o.log.map (fun e => (e.2.randomness, e.1))
  swap
  · exact (bad_event_of_settled laws secret o c hroot hlog hver).imp id
      (Or.imp id fun h => Or.inl ⟨h, hpt⟩)
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hpt
  obtain ⟨hR, hM⟩ := Prod.mk.inj hxe
  rcases bad_event_or_honest_descent_of_settled laws secret o c hroot hlog hver with
    h | h | ⟨digest, forsPk, hd, hfors, hall⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  by_cases hTC : TargetCollision secret o.pk.pkSeed c
  · exact Or.inl hTC
  refine Or.inr (Or.inr (Or.inr ?_))
  have hdx : LoggedDigest o c x digest := by
    change c (.hmsg x.2.randomness o.pk.pkSeed o.pk.pkRoot x.1) = some digest
    rw [hR, hM]
    exact hd
  obtain ⟨-, digest', forsPk', hd', hfs, -, -⟩ :=
    components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM core c _ _ _ _ _
      (hlog x hx)
  obtain rfl : digest' = digest := Option.some.inj (hd'.symm.trans hdx)
  have hht : o.sig.hypertree = x.2.hypertree := Vector.ext fun j hj => by
    obtain ⟨m, r, -, hf, hh, hmsg⟩ := hall ⟨j, hj⟩
    obtain ⟨m₀, hm₀, hs₀⟩ :=
      exists_honestMessage?_xmssSignWithSecret_of_loggedDigest secret o c (hlog x hx) hdx ⟨j, hj⟩
    obtain rfl := Option.some.inj (hm₀.symm.trans hmsg)
    exact Option.some.inj (((targetCollision_or_xmssSignWithSecret_eq_some secret _ c _ _ _ hf
      hh).resolve_left hTC).symm.trans hs₀)
  have hfs' : o.sig.fors = x.2.fors := by
    obtain ⟨m, r, hm, -, -, h⟩ := hall ⟨0, vp.valid.d_pos⟩
    obtain rfl : forsPk = m := Option.some.inj hm
    simp only [honestMessage?, LayerPosition.atLayer_zero_eq_initial,
      LayerPosition.initial_layer_val, forsInstanceAdrs_initial, ↓reduceIte] at h
    exact (targetCollision_or_eq_of_forsSignWithSecret secret _ c _ _ _ forsPk hfors h
      hfs).resolve_left hTC
  have hsig : o.sig = x.2 := calc
    o.sig = ⟨o.sig.randomness, o.sig.fors, o.sig.hypertree⟩ := rfl
    _ = ⟨x.2.randomness, x.2.fors, x.2.hypertree⟩ := by rw [← hR, hfs', hht]
  rw [← hM, hsig]
  exact hx

section Run

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-! ## The bridge on the run -/

/-- **The random-oracle bad-event bridge.**  On the support of `romSchemeRun`, a strongly winning
forgery exhibits, at the run's own oracle-backed provider and public seed and in the public-hash
part of the final cache, a same-address target collision, or a hidden-value hit, or
interleaved-target coverage at an `H_msg` point that is the point of no logged signature. -/
theorem bad_event_of_strongWins_romSchemeRun (laws : core.ByteLaws) (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    {z : RomOutcome vp core × (hashSpec core).QueryCache}
    (hz : z ∈ support (romSchemeRun core e optRand pkSeedDist adv))
    (hw : z.1.strongWins = true) :
    TargetCollision (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1.pk.pkSeed z.2.fst ∨
      HiddenHit (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1 z.2.fst ∨
      (ItsrCovered z.1 z.2.fst ∧
        (z.1.sig.randomness, z.1.msg) ∉ z.1.log.map (fun e => (e.2.randomness, e.1))) := by
  obtain ⟨hfresh, hv⟩ := (UnforgeableTranscript.strongWins_eq_true_iff z.1).mp hw
  obtain ⟨-, -, hroot, hlog, hver⟩ :=
    settled_of_mem_support_romSchemeRun core e optRand pkSeedDist adv hz
  rcases bad_event_or_logged_of_settled laws _ z.1 z.2.fst hroot hlog (hv ▸ hver) with
    h | h | h | h
  exacts [.inl h, .inr (.inl h), .inr (.inr h), absurd h hfresh]

end Run

end SLHDSA.Security
