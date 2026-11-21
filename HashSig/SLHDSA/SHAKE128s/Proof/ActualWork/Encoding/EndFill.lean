/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
public import HashSig.SLHDSA.Security.PrfKeyBound
import HashSig.SLHDSA.Security.Transport
import VCVio.OracleComp.Constructions.SampleableType.Measure
public import HashSig.SLHDSA.Security.ByteClash
import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings

/-! # Encoding clashes in the completed random oracle cache -/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.FIPS205

/-- A typed query read back from its encoding by the router at the public seed. -/
@[expose] def IsRouteFixed (s : core.PkSeed) (q : (hashSpec core).Domain) : Prop :=
  shakeRoute params (IsHonestKey params core) s (encode params q) = some q

/-- Filling makes a cell available exactly when it was drawn already or pending. -/
theorem endFill_cell_isSome_iff (st₀ : LabState core)
    (pending : List (DeriveQuery core ⊕ NodeKey core)) (filled : LabState core)
    (hfilled : filled ∈ support (RelabelState.endFill (st₀, pending)))
    (cell : DeriveQuery core ⊕ NodeKey core) :
    (filled.2 cell).isSome ↔ (st₀.2 cell).isSome ∨ cell ∈ pending := by
  rw [RelabelState.endFill_eq, support_map] at hfilled
  obtain ⟨w, hw, rfl⟩ := hfilled
  exact (QueryImpl.withCaching_queryAll_le_and_isSome_iff _ hw).2 cell

/-- Public-query and private-cell provenance pass through deferred filling and both merges.
Every message-digest lookup reads the exact public cache from before filling. -/
theorem fill_provenance_transfer
    (s : core.PkSeed) (initialPK : PublicKeyCore core) (admittedS : Nat)
    (st₀ : LabState core) (pending : List (DeriveQuery core ⊕ NodeKey core))
    (filled : LabState core) (secret : core.SkSeed × core.SkPrf)
    (hpk : initialPK.pkSeed = s)
    (hpublic : ∀ q, (st₀.1 q).isSome → IsRouteFixed s q ∨
      ∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg))
    (hsecret : ∀ k : PrfKey core,
      (st₀.2 (.inl (.inl k))).isSome ∨ .inl (.inl k) ∈ pending →
        IsHonestKey params core k.1)
    (hactive : ∀ (o : core.Y) (msg : List Byte),
      (st₀.2 (.inl (.inr (o, msg)))).isSome ∨ .inl (.inr (o, msg)) ∈ pending →
        1 ≤ admittedS)
    (hfilled : filled ∈ support (RelabelState.endFill (st₀, pending))) :
    let typed := (secretEncoding core (Equiv.refl _) s).merge secret
      ((slhGraph core s).toSplitCache filled)
    (∀ q, (typed q).isSome → IsRouteFixed s q ∨
      (∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg)) ∨
      (∃ o msg, q = .inr ⟨secret.2, o, msg⟩ ∧ 1 ≤ admittedS)) ∧
    (∀ (r root : core.Y) (seed : core.PkSeed) (msg : List Byte),
      typed (.inl (.hmsg r seed root msg)) = st₀.1 (.inl (.hmsg r seed root msg))) := by
  classical
  subst s
  let G := slhGraph core initialPK.pkSeed
  let E := secretEncoding core (Equiv.refl _) initialPK.pkSeed
  have hC : filled.1 = st₀.1 := RelabelState.fst_eq_of_mem_support_endFill hfilled
  have hcell := endFill_cell_isSome_iff st₀ pending filled hfilled
  constructor
  · intro q hq
    change (E.merge secret (G.toSplitCache filled) q).isSome at hq
    by_cases hx : ∃ x, E.enc secret x = q
    · obtain ⟨x, rfl⟩ := hx
      rw [SecretEncoding.merge_toSplitCache_apply_enc, Option.isSome_map] at hq
      rcases x with k | ⟨o, msg⟩
      · left
        change shakeRoute params (IsHonestKey params core) initialPK.pkSeed
          (encode params (.inl (.thash initialPK.pkSeed k.1 [secret.1]))) =
            some (.inl (.thash initialPK.pkSeed k.1 [secret.1]))
        exact shakeRoute_encode_thash k.1 [secret.1]
          (hsecret k ((hcell (.inl (.inl k))).1 hq))
      · exact Or.inr (Or.inr ⟨o, msg, rfl,
          hactive o msg ((hcell (.inl (.inr (o, msg)))).1 hq)⟩)
    · rw [E.merge_apply_of_not_exists secret _ hx] at hq
      change (G.merge filled q).isSome at hq
      by_cases hg : ∃ κ vs, G.childVals filled κ = some vs ∧ G.pt κ vs = q
      · obtain ⟨κ, vs, _, rfl⟩ := hg
        left
        change shakeRoute params (IsHonestKey params core) initialPK.pkSeed
          (encode params (.inl (.thash initialPK.pkSeed κ.1 vs))) =
            some (.inl (.thash initialPK.pkSeed κ.1 vs))
        exact shakeRoute_encode_thash κ.1 vs (isHonestKey_nodeKey κ)
      · rw [G.merge_apply_of_not_exists hg, hC] at hq
        rcases hpublic q hq with hfix | hhmsg
        · exact Or.inl hfix
        · exact Or.inr (Or.inl hhmsg)
  · intro r root seed msg
    change E.merge secret (G.toSplitCache filled) (.inl (.hmsg r seed root msg)) = _
    rw [E.merge_apply_of_not_exists secret _
      (by rintro ⟨x | ⟨o, m⟩, hx⟩ <;> cases hx)]
    change G.merge filled (.inl (.hmsg r seed root msg)) = _
    rw [G.merge_apply_of_not_exists
      (by rintro ⟨κ, vs, _, hpoint⟩; cases hpoint), hC]

/-- A clash in a partitioned cache gives an admitted message-PRF alias or a weak initial key.
Message-digest lookups are transported to the supplied public cache exactly. -/
theorem activated_clash_of_cache_provenance
    (s : core.PkSeed) (initialPK : PublicKeyCore core) (skPrf : core.SkPrf)
    (admittedS : Nat) (typed C : (hashSpec core).QueryCache)
    (hpk : initialPK.pkSeed = s)
    (hc : ∀ q, (typed q).isSome → IsRouteFixed s q ∨
      (∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg)) ∨
      (∃ o msg, q = .inr ⟨skPrf, o, msg⟩ ∧ 1 ≤ admittedS))
    (hhmsg : ∀ (r root : core.Y) (seed : core.PkSeed) (msg : List Byte),
      typed (.inl (.hmsg r seed root msg)) = C (.inl (.hmsg r seed root msg)))
    (clash : (shakeEncoding params (by decide) (by decide) s).Clash typed) :
    ((HmsgAtPrfKey id skPrf C ∨ skPrf = s) ∧ 1 ≤ admittedS) ∨
      IsWeakKey params initialPK := by
  have hc₀ : ∀ q, (typed q).isSome →
      shakeRoute params (IsHonestKey params core) s (encode params q) = some q ∨
        (∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg)) ∨
        ∃ o msg, q = .inr ⟨skPrf, o, msg⟩ := by
    intro q hq
    rcases hc q hq with hfix | hh | ⟨o, msg, heq, _⟩
    · exact Or.inl hfix
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr ⟨o, msg, heq⟩)
  obtain ⟨q, other, distinct, cached, otherCached, equal, nonfixed⟩ := clash.exists_route_ne
  change encode params q = encode params other at equal
  change ¬IsRouteFixed s q at nonfixed
  rcases hc q cached with hfix | ⟨r, msg, rfl⟩ | ⟨o, msg, rfl, active⟩
  · exact (nonfixed hfix).elim
  · have ht : IsThashString params (IsHonestKey params core) s
        (encode params (.inl (.hmsg r s initialPK.pkRoot msg))) := by
      by_contra ht
      exact nonfixed (shakeRoute_encode_hmsg r initialPK.pkRoot msg ht)
    have hr : r = s :=
      Vector.toList_inj.1 (toList_eq_of_isThashString_encode_hmsg _ ht)
    have hw : HmsgAtWeakKey s initialPK.pkRoot typed :=
      ⟨msg, hr ▸ cached, hr ▸ ht⟩
    have weak := isWeakKey_of_hmsgAtWeakKey (vp := params) (by decide) hw
    right
    simpa only [← hpk] using weak
  · rcases hmsgAtPrfKey_and_prfMsgAt_or_eq_of_shakeRoute_ne_prfMsg
        hc₀ cached otherCached distinct equal nonfixed with hit | key
    · obtain ⟨⟨seed, root, message, hhit⟩, _⟩ := hit
      have hC : (C (.inl (.hmsg skPrf seed root message))).isSome := by
        have htyped : (typed (.inl (.hmsg skPrf seed root message))).isSome := hhit
        rwa [hhmsg skPrf root seed message] at htyped
      exact Or.inl ⟨Or.inl ⟨seed, root, message, hC⟩, active⟩
    · exact Or.inl ⟨Or.inr key, active⟩

/-- Exact cache-level application to deferred filling and a supplied ideal secret.
The message-digest hit is read on the public cache before deferred filling. -/
theorem activated_clash_of_endFill
    (s : core.PkSeed) (initialPK : PublicKeyCore core) (admittedS : Nat)
    (st₀ : LabState core) (pending : List (DeriveQuery core ⊕ NodeKey core))
    (filled : LabState core) (secret : core.SkSeed × core.SkPrf)
    (hpk : initialPK.pkSeed = s)
    (hpublic : ∀ q, (st₀.1 q).isSome → IsRouteFixed s q ∨
      ∃ r msg, q = .inl (.hmsg r s initialPK.pkRoot msg))
    (hsecret : ∀ k : PrfKey core,
      (st₀.2 (.inl (.inl k))).isSome ∨ .inl (.inl k) ∈ pending →
        IsHonestKey params core k.1)
    (hactive : ∀ (o : core.Y) (msg : List Byte),
      (st₀.2 (.inl (.inr (o, msg)))).isSome ∨ .inl (.inr (o, msg)) ∈ pending →
        1 ≤ admittedS)
    (hfilled : filled ∈ support (RelabelState.endFill (st₀, pending)))
    (clash : (shakeEncoding params (by decide) (by decide) s).Clash
      ((secretEncoding core (Equiv.refl _) s).merge secret
        ((slhGraph core s).toSplitCache filled))) :
    ((HmsgAtPrfKey id secret.2 st₀.1 ∨ secret.2 = s) ∧ 1 ≤ admittedS) ∨
      IsWeakKey params initialPK := by
  obtain ⟨hc, hhmsg⟩ := fill_provenance_transfer s initialPK admittedS st₀ pending filled
    secret hpk hpublic hsecret hactive hfilled
  exact activated_clash_of_cache_provenance s initialPK secret.2 admittedS _ st₀.1
    hpk hc hhmsg clash

end SLHDSA.SHAKE128s.FIPS205

end
