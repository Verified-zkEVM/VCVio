/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteRouter
import HashSig.SLHDSA.Security.AddressKeys
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# The weak-key event of the SHAKE256 router

`HashSig.SLHDSA.Security.ByteRouter` reads a byte string as a typed query of the three SLH-DSA
oracles, rule 1 first: a string `PK.seed ‖ ADRS ‖ M_1 ‖ … ‖ M_ℓ` whose address key `ADRS` is an
honest key (`IsHonestKey`) is read as a tweakable-hash query. The encoding
`R ‖ PK.seed ‖ PK.root ‖ M` of an honest `H_msg` query is read by rule 1 only when `R = PK.seed`
and its bytes `n` to `n + 32`, the first `32` bytes of `PK.seed ‖ PK.root` for `16 ≤ n`, are an
honest key. This module bounds the probability of the second condition, the weak-key event
`IsWeakKey vp pk` of `HashSig.SLHDSA.Security.ByteRouter`, a predicate of the public key alone
(`isWeakKey_of_isThashString_encode_hmsg`).

## The honest keys

The honest addresses `IsHonestAdrs` are the addresses of the union ledger `constructionAddresses`
and their secret children, which are the `WOTS_PRF` addresses of the WOTS+ chains and the
`FORS_PRF` addresses of the FORS leaves (`mem_secretChildren_of_inl_mem_childAdrs`). So there are
at most `honestAdrsCount vp = |constructionAddresses vp| + wotsInstanceCount · len + 2^h · k · 2^a`
of them, and at most as many honest keys (`encard_setOf_isHonestKey_le`). The count is a bound
on `Set.encard`; the honest addresses are a predicate and are never enumerated.

## The public root is uniform

In the run `romSchemeRun` of `romScheme` at a fixed public seed, the public root is the answer of
the top-layer root query `H(PK.seed, ADRS*, l, r)` of key generation. Every earlier query of key
generation is at an address of type `WOTS_HASH`, `WOTS_PK` or `WOTS_PRF`, or at an XMSS node below
the top height (`PerfectMerkleTree.merkleRootM_pred_of_subtree`), so where the oracle key of
`ADRS*` differs from the keys of all of those, the root query is fresh and its answer is uniform
(`prEvent_run_keygenInternalWithSecretM_le`). The adversary runs after key generation and leaves
the public key unchanged, so the public key of the run is `(PK.seed, r)` with `r` uniform, against
every adversary (`prEvent_romSchemeRun_pk_le`). For the SHAKE key, the 32-byte serialization of the
address, this key condition, `CorePrimitives.RootKeySeparated`, holds under the FIPS 205 address
widths (`rootKeySeparated_shakeCore`).

## The bound

At a public seed `PK.seed`, the weak-key event has probability at most
`weakKeyMass vp PK.seed = Pr_r[IsWeakKey vp (PK.seed, r)]` over a uniform node `r`
(`prEvent_romSchemeRun_isWeakKey_le`), independently of the adversary. Averaged over a uniform
public seed, for `16 ≤ n`, `PK.seed ‖ r` is a uniform string of `2n` bytes and its first `32`
bytes a uniform address key, so the average is at most `|A_hon| / 2^256` with
`|A_hon| = honestAdrsCount vp` (`lintegral_weakKeyMass_le`, and `lintegral_add_weakKeyMass_mul_le`
for a per-seed bound `C + weakKeyMass vp PK.seed * D`). At `n = 32` the key read is `PK.seed`
itself, so the event is a property of the public seed: a seed that is not an honest key has
weak-key mass zero and the run at it has no weak public key (`weakKeyMass_eq_zero_of_n_eq_32`,
`prEvent_romSchemeRun_isWeakKey_eq_zero_of_n_eq_32`), and every other seed has mass one
(`weakKeyMass_eq_zero_or_eq_one_of_n_eq_32`). So at `n = 32` the smaller of a bound
`C + weakKeyMass vp PK.seed` and a bound `D` is at most `C + weakKeyMass vp PK.seed * min 1 D`
(`min_add_weakKeyMass_le_of_n_eq_32`). At `n = 16` and `n = 24` the root is
needed: the first `32` bytes of `PK.seed ‖ PK.root` include `32 - n` bytes of `PK.root`.

## Main statements

* `encard_setOf_isHonestKey_le`: `|{k | IsHonestKey vp core k}| ≤ honestAdrsCount vp`.
* `prEvent_romSchemeRun_pk_le`: the public key of the run is `(PK.seed, uniform)`.
* `prEvent_romSchemeRun_isWeakKey_le`: the weak-key event at a public seed.
* `lintegral_weakKeyMass_le`, `lintegral_add_weakKeyMass_mul_le`: the average over the seed.
* `weakKeyMass_eq_zero_or_eq_one_of_n_eq_32`, `min_add_weakKeyMass_le_of_n_eq_32`: the weak seeds
  at `n = 32`.

## References

* NIST FIPS 205, §4.2 (ADRS), Algorithms 9 and 18 (XMSS node, key generation), §11.1 (SHAKE).
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

/-! ## Counting the honest keys -/

section Count

variable (vp : ValidatedParams)

/-- The number of entries of the union ledger and of the secret children: the
`|constructionAddresses vp|` entries of the union ledger, the `wotsInstanceCount · len` WOTS+
secret-key addresses and the `2^h · k · 2^a` FORS secret-key addresses. It bounds the number of
honest addresses (`IsHonestAdrs`, `encard_setOf_isHonestAdrs_le`). -/
@[expose] def honestAdrsCount : ℕ :=
  (constructionAddresses vp).length + wotsInstanceCount vp.params * vp.params.len +
    targetCount vp.params .forsF

/-- `honestAdrsCount` in closed form. -/
theorem honestAdrsCount_eq :
    honestAdrsCount vp =
      targetCount vp.params .forsF + targetCount vp.params .forsH + targetCount vp.params .forsTl +
        wotsInstanceCount vp.params * vp.params.len * (vp.params.w - 1) +
        targetCount vp.params .wotsTl + targetCount vp.params .xmssH +
        wotsInstanceCount vp.params * vp.params.len + targetCount vp.params .forsF := by
  rw [honestAdrsCount, constructionAddresses_length]

variable {vp}

/-- The secret children of the union ledger: the `WOTS_PRF` addresses of the WOTS+ chains and the
`FORS_PRF` addresses of the FORS leaves. -/
theorem mem_secretChildren_of_inl_mem_childAdrs {a b : Adrs} (hb : b ∈ constructionAddresses vp)
    (h : .inl a ∈ childAdrs vp b) :
    a ∈ (allWotsChains vp).map (fun c => wotsSkAdrs (wotsInstanceAdrs c.1) c.2.val) ++
      (forsLeafAddresses vp).map fun b => forsSkAdrs b b.word3 := by
  rcases (mem_constructionAddresses_iff b).1 hb with hm | hm | hm | hm | hm | hm
  · obtain ⟨⟨⟨pos, tree⟩, j⟩, -, rfl⟩ := List.mem_map.1 hm
    rw [childAdrs_forsNodeAdrs_zero, List.mem_singleton, Sum.inl.injEq] at h
    subst h
    refine List.mem_append_right _ (List.mem_map.2 ⟨_, hm, ?_⟩)
    rw [forsNodeAdrs_eq, forsSkAdrs_eq, forsSkAdrs_eq]
  · obtain ⟨⟨_, z, j⟩, hmem, rfl⟩ := List.mem_map.1 hm
    rw [childAdrs_forsNodeAdrs vp (mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2).1]
      at h
    simp at h
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hm
    simp [childAdrs_forsPkAdrs] at h
  · obtain ⟨⟨c, ⟨t, ht⟩⟩, hmem, rfl⟩ := List.mem_map.1 hm
    simp only [wotsStepAdrs] at h
    rcases t with _ | t
    · rw [childAdrs_wotsChainAdrs_setHashAddress_zero, List.mem_singleton, Sum.inl.injEq] at h
      subst h
      exact List.mem_append_left _
        (List.mem_map.2 ⟨c, (List.mem_product.1 hmem).1, rfl⟩)
    · simp [childAdrs_wotsChainAdrs_setHashAddress_succ] at h
  · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hm
    simp [childAdrs_wotsPkAdrs] at h
  · obtain ⟨⟨_, z, j⟩, hmem, rfl⟩ := List.mem_map.1 hm
    have hz := (mem_perfectInternalCoords.1 (List.mem_product.1 hmem).2).1
    rcases (by omega : z = 1 ∨ 1 < z) with rfl | hz1
    · simp [childAdrs_xmssNodeAdrs_one] at h
    · simp [childAdrs_xmssNodeAdrs vp hz1] at h

/-- The members of a list are at most as many as its entries. -/
private theorem encard_setOf_mem_le_length {α : Type} (l : List α) :
    {a | a ∈ l}.encard ≤ l.length := by
  classical
  have h : {a | a ∈ l} = (l.toFinset : Set α) := by ext; simp
  rw [h, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast l.toFinset_card_le

/-- **The honest addresses are at most `honestAdrsCount vp`.** -/
theorem encard_setOf_isHonestAdrs_le : {a | IsHonestAdrs vp a}.encard ≤ honestAdrsCount vp := by
  have hsub : {a | IsHonestAdrs vp a} ⊆ {a | a ∈ constructionAddresses vp ++
      ((allWotsChains vp).map (fun c => wotsSkAdrs (wotsInstanceAdrs c.1) c.2.val) ++
        (forsLeafAddresses vp).map fun b => forsSkAdrs b b.word3)} := by
    rintro a (ha | ⟨b, hb, hab⟩)
    · exact List.mem_append_left _ ha
    · exact List.mem_append_right _ (mem_secretChildren_of_inl_mem_childAdrs hb hab)
  refine (Set.encard_le_encard hsub).trans ((encard_setOf_mem_le_length _).trans ?_)
  simp [honestAdrsCount, allWotsChains_length, Nat.add_assoc]

/-- **The honest keys are at most `honestAdrsCount vp`.** They are the keys of the honest
addresses, of which there are at most `honestAdrsCount vp`, the number of entries of the union
ledger plus the numbers of WOTS+ and FORS secret-key addresses. -/
theorem encard_setOf_isHonestKey_le (core : CorePrimitives vp.params) :
    {k | IsHonestKey vp core k}.encard ≤ honestAdrsCount vp := by
  have h : {k | IsHonestKey vp core k} = core.adrsToKey '' {a | IsHonestAdrs vp a} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_image, IsHonestKey]
  rw [h]
  exact Set.encard_image_le _ _ |>.trans encard_setOf_isHonestAdrs_le

end Count

/-! ## The public root is uniform -/

section Root

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- A tweakable-hash query at an address whose key is not `k` is not a query at the key `k`. -/
private theorem allQueriesSatisfy_thash {k : core.AdrsKey} (pkSeed : core.PkSeed) {a : Adrs}
    (xs : List core.Y) (h : core.adrsToKey a ≠ k) :
    (liftM ((publicHashSpec core).query (.thash pkSeed (core.adrsToKey a) xs)) :
      OracleComp (publicHashSpec core) core.Y).AllQueriesSatisfy
        fun t => ¬∃ s ys, t = .thash s k ys := by
  rw [allQueriesSatisfy_query_iff]
  rintro ⟨s, ys, hq⟩
  injection hq with _ hk
  exact h hk

/-- An XMSS subtree of height `z < h'` at the oracle-backed provider makes no tweakable-hash query
at the key `k` when `k` is the key of no address of type `WOTS_HASH`, `WOTS_PK` or `WOTS_PRF` and
of no XMSS node below height `h'`: those are the addresses the subtree queries. -/
private theorem allQueriesSatisfy_xmssNodeWithSecret_not_thash (e : core.SkSeed ≃ core.Y)
    (pkSeed : core.PkSeed) (skSeed : core.SkSeed) {k : core.AdrsKey}
    (hkey : ∀ a : Adrs, (a.type = 0 ∨ a.type = 1 ∨ a.type = 5 ∨
      a.type = 2 ∧ a.word2 < vp.params.hp) → core.adrsToKey a ≠ k)
    (base : Adrs) {z : ℕ} (hz : z < vp.params.hp) (t : ℕ) :
    (xmssNodeWithSecret core (PublicHash.f core pkSeed) (PublicHash.tl core pkSeed)
      (PublicHash.h core pkSeed) (oracleSecret core e pkSeed skSeed) base z t :
        OracleComp (publicHashSpec core) core.Y).AllQueriesSatisfy
      fun t => ¬∃ s ys, t = .thash s k ys := by
  have hb : ∀ {α β : Type} (oa : OracleComp (publicHashSpec core) α)
      (ob : α → OracleComp (publicHashSpec core) β),
      oa.AllQueriesSatisfy (fun t => ¬∃ s ys, t = .thash s k ys) →
      (∀ x, (ob x).AllQueriesSatisfy (fun t => ¬∃ s ys, t = .thash s k ys)) →
      (oa >>= ob).AllQueriesSatisfy (fun t => ¬∃ s ys, t = .thash s k ys) :=
    fun _ _ h₁ h₂ => allQueriesSatisfy_bind h₁ h₂
  have hp : ∀ {α : Type} (x : α), (pure x : OracleComp (publicHashSpec core) α).AllQueriesSatisfy
      (fun t => ¬∃ s ys, t = .thash s k ys) := fun x => allQueriesSatisfy_pure x _
  refine PerfectMerkleTree.merkleRootM_pred_of_subtree
    (fun {α} (oa : OracleComp (publicHashSpec core) α) =>
      oa.AllQueriesSatisfy (fun t => ¬∃ s ys, t = .thash s k ys)) hb _ _ z t (fun i _ => ?_)
    fun h i _ hh _ l r => allQueriesSatisfy_thash (a := xmssNodeAdrs base h i) pkSeed [l, r]
      (hkey _ (Or.inr (Or.inr (Or.inr ⟨rfl, show h < vp.params.hp by omega⟩))))
  refine hb _ _ (Vector.ofFnM_pred
    (fun {α} (oa : OracleComp (publicHashSpec core) α) =>
      oa.AllQueriesSatisfy (fun t => ¬∃ s ys, t = .thash s k ys)) hp hb _ fun j => ?_) fun tops =>
    allQueriesSatisfy_thash (a := wotsPkAdrs (wotsLeafAdrs base i)) pkSeed _
      (hkey _ (Or.inr (Or.inl (by rw [wotsPkAdrs_eq]))))
  refine hb _ _ (allQueriesSatisfy_thash (a := wotsSkAdrs (wotsLeafAdrs base i) j.val) pkSeed _
    (hkey _ (Or.inr (Or.inr (Or.inl (by rw [wotsSkAdrs_eq])))))) fun x => ?_
  exact chainWith_pred (fun {α} (oa : OracleComp (publicHashSpec core) α) =>
      oa.AllQueriesSatisfy (fun t => ¬∃ s ys, t = .thash s k ys)) hp hb x 0 _ fun jj _ y =>
    allQueriesSatisfy_thash pkSeed [y] (hkey _ (Or.inl (by rw [wotsChainAdrs_setHashAddress_eq])))

variable (vp core) in
/-- The oracle key of the top-layer root's address, `xmssNodeAdrs (layerAdrs (d - 1) 0) h' 0`, is
not the key of any address of type `WOTS_HASH`, `WOTS_PK` or `WOTS_PRF`, nor of any XMSS node below
height `h'`. -/
@[expose] def _root_.SLHDSA.CorePrimitives.RootKeySeparated : Prop :=
  ∀ a : Adrs, (a.type = 0 ∨ a.type = 1 ∨ a.type = 5 ∨ a.type = 2 ∧ a.word2 < vp.params.hp) →
    core.adrsToKey a ≠
      core.adrsToKey (xmssNodeAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0) vp.params.hp 0)

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] [DecidableEq core.Y]

/-- **The root of key generation is uniform.** Under `RootKeySeparated`, key generation at the
oracle-backed provider, run in the random oracle model from the empty cache, returns a uniform
root: the root is the answer of a query at a key no earlier query of key generation has. -/
theorem prEvent_run_keygenInternalWithSecretM_le
    (hkey : core.RootKeySeparated vp)
    (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed) (skSeed : core.SkSeed)
    (Q : core.Y → Prop) :
    Pr{let z ← (simulateQ (hashSpec core).romImpl (simulateQ (HasQuery.toQueryImpl
        (spec := publicHashSpec core) (m := OracleComp (unifSpec + hashSpec core)))
        (GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pkSeed skSeed)
          pkSeed))).run ∅}[Q z.1] ≤
      Pr{let y ← $ᵗ core.Y}[Q y] := by
  unfold CorePrimitives.RootKeySeparated at hkey
  obtain ⟨hp', hhp⟩ : ∃ hp', vp.params.hp = hp' + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos vp.valid.hp_pos).symm⟩
  generalize hbase : GeneralHypertree.layerAdrs (vp.params.d - 1) 0 = base at hkey
  generalize hk : core.adrsToKey (xmssNodeAdrs base vp.params.hp 0) = k at hkey
  let M := fun t => (xmssNodeWithSecret core (PublicHash.f core pkSeed)
    (PublicHash.tl core pkSeed) (PublicHash.h core pkSeed) (oracleSecret core e pkSeed skSeed)
    base hp' t : OracleComp (publicHashSpec core) core.Y)
  have hK : (GeneralScheme.keygenInternalWithSecretM core (oracleSecret core e pkSeed skSeed)
      pkSeed : OracleComp (publicHashSpec core) core.Y) =
      (do let l ← M 0; let r ← M 1; pure (l, r)) >>= fun lr =>
        liftM ((publicHashSpec core).query (.thash pkSeed k [lr.1, lr.2])) := by
    simp only [GeneralScheme.keygenInternalWithSecretM, GeneralHypertree.rootWithSecretM,
      GeneralHypertree.rootWithSecret, xmssRootWithSecret, bind_assoc, pure_bind]
    rw [xmssNodeWithSecret, hbase, ← hk, hhp]
    rfl
  have hpre : (do let l ← M 0; let r ← M 1; pure (l, r) :
      OracleComp (publicHashSpec core) (core.Y × core.Y)).AllQueriesSatisfy
        fun t => ¬∃ s ys, t = .thash s k ys :=
    allQueriesSatisfy_bind
      (allQueriesSatisfy_xmssNodeWithSecret_not_thash e pkSeed skSeed hkey base (by omega) 0)
      fun _ => allQueriesSatisfy_bind
        (allQueriesSatisfy_xmssNodeWithSecret_not_thash e pkSeed skSeed hkey base (by omega) 1)
        fun _ => allQueriesSatisfy_pure _ _
  rw [hK, simulateQ_bind, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
  have hnone := snd_apply_inl_eq_none_of_mem_support_run_romImpl
    (K := fun t => ∃ s ys, t = .thash s k ys) _ hpre (fun _ _ => rfl) hz _
    ⟨pkSeed, [z.1.1, z.1.2], rfl⟩
  rw [simulateQ_spec_query, show (HasQuery.toQueryImpl (spec := publicHashSpec core)
      (m := OracleComp (unifSpec + hashSpec core)) (.thash pkSeed k [z.1.1, z.1.2])) =
      liftM ((unifSpec + hashSpec core).query (.inr (.inl (.thash pkSeed k [z.1.1, z.1.2]))))
        from rfl, simulateQ_spec_query]
  rw [OracleSpec.romImpl_apply_inr, randomOracle.run_eq]
  simp only [hnone]
  simp only [prEvent_norm]
  exact le_of_eq (SampleableType.prEvent_uniformSample_inst_irrel _ _ Q)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- **The public key of the run is `(PK.seed, uniform root)`.** In the run of `romScheme` at the
public seed `pkSeed`, against any adversary, an event of the public key is at most as likely as the
same event of `(pkSeed, r)` for a uniform node `r`, under `RootKeySeparated`. -/
theorem prEvent_romSchemeRun_pk_le
    (hkey : core.RootKeySeparated vp)
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeed : core.PkSeed) (adv : UnforgeableAdversary (romScheme core e optRand (pure pkSeed)))
    (P : PublicKeyCore core → Prop) :
    Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[P z.1.pk] ≤
      Pr{let r ← $ᵗ core.Y}[P ⟨pkSeed, r⟩] := by
  calc Pr{let z ← romSchemeRun core e optRand (pure pkSeed) adv}[P z.1.pk]
      ≤ Pr{let z ← (simulateQ (hashSpec core).romImpl
          (romScheme core e optRand (pure pkSeed)).keygen).run ∅}[P z.1.1] := by
        unfold romSchemeRun
        rw [unforgeableTranscriptExperiment_def, simulateQ_bind, StateT.run_bind]
        refine prEvent_bind_le_prEvent_of_support _ _
          (fun a : (PublicKeyCore core × SecretKeyCore core) × (hashSpec core).QueryCache =>
            P a.1.1) _ fun a _ ha => ?_
        refine prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => ?_
        obtain ⟨⟨pk, sk⟩, st⟩ := a
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨_, -, _, -, rfl⟩ := hz
        exact ha
    _ ≤ Pr{let r ← $ᵗ core.Y}[P ⟨pkSeed, r⟩] := by
        rw [romScheme_keygen]
        simp only [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run, map_pure,
          pure_bind, bind_map_left, simulateQ_pure, StateT.run_pure]
        refine prEvent_bind_le_of_forall_le _ _ _ fun skSeed =>
          prEvent_bind_le_of_forall_le _ _ _ fun _ => ?_
        rw [keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ,
          HasQuery.QueryHom.ofSimulateQ_apply]
        simpa only [prEvent_norm] using
          prEvent_run_keygenInternalWithSecretM_le hkey e pkSeed skSeed fun r => P ⟨pkSeed, r⟩

end Root

/-! ## The SHAKE key of the top-layer root -/

/-- **The SHAKE key separates the top-layer root.** Under the FIPS 205 address widths the SHAKE
key, the full 32-byte serialization, of the top-layer root's address differs from that of every
address of type `WOTS_HASH`, `WOTS_PK` or `WOTS_PRF` (the type words differ) and of every XMSS
node below height `h'` (the tree-height words differ). -/
theorem rootKeySeparated_shakeCore {vp : ValidatedParams} (hb : CanonicalAddressBounds vp.params) :
    (shakeCore vp).RootKeySeparated vp := by
  intro a ha h
  have hbytes : a.toBytes = (xmssNodeAdrs (GeneralHypertree.layerAdrs (vp.params.d - 1) 0)
      vp.params.hp 0).toBytes := by
    have h' : Adrs.toVector a = Adrs.toVector (xmssNodeAdrs (GeneralHypertree.layerAdrs
        (vp.params.d - 1) 0) vp.params.hp 0) := h
    simpa [Adrs.toVector] using congrArg Vector.toList h'
  obtain ⟨-, -, hty, -, hw, -⟩ := toBytes_blocks hbytes
  have hty' := congrArg toInt hty
  have hw' := congrArg toInt hw
  simp only [Adrs.toBytesBE, toInt_toByte_mod, xmssNodeAdrs_eq] at hty' hw'
  have hhp := hb.hp_le
  rcases ha with ha | ha | ha | ⟨ha, hw2⟩ <;> rw [ha] at hty' <;> norm_num at hty'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hw'
  omega

/-! ## The weak-key bound -/

section Bound

variable (vp : ValidatedParams)

/-- **The weak-key mass of a public seed**: the probability that `(PK.seed, r)` is a weak public
key (`IsWeakKey`) for a uniform node `r`. -/
@[expose] noncomputable def weakKeyMass (pkSeed : (shakeCore vp).PkSeed) : ℝ≥0∞ :=
  Pr{let r ← $ᵗ (shakeCore vp).Y}[IsWeakKey vp ⟨pkSeed, r⟩]

variable {vp}

/-- **The weak-key event, per public seed.** In the run of `romScheme` over the SHAKE carriers at
the public seed `pkSeed`, against any adversary, the public key is weak with probability at most
`weakKeyMass vp pkSeed`: the public root is uniform (`prEvent_romSchemeRun_pk_le`). -/
theorem prEvent_romSchemeRun_isWeakKey_le (hb : CanonicalAddressBounds vp.params)
    (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))) :
    Pr{let z ← romSchemeRun (shakeCore vp) e optRand (pure pkSeed) adv}[IsWeakKey vp z.1.pk] ≤
      weakKeyMass vp pkSeed :=
  prEvent_romSchemeRun_pk_le (rootKeySeparated_shakeCore hb) e optRand pkSeed adv _

/-- `Bytes 32` has `2 ^ 256` elements. -/
private theorem natCard_bytes_32 : Nat.card (Bytes 32) = 2 ^ 256 := by
  change Nat.card (Vector UInt8 32) = 2 ^ 256
  rw [Nat.card_congr (arrayVectorEquivFin UInt8 32), Nat.card_fun, Nat.card_eq_fintype_card,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- For `32 ≤ 2n`, reading `s ‖ r` as its first `32` bytes and the rest is a bijection
`Bytes n × Bytes n → Bytes 32 × Bytes (2n - 32)`. -/
private theorem bijective_splitKey {n : ℕ} (hn : 32 ≤ 2 * n) :
    Function.Bijective (Function.uncurry fun (s r : Bytes n) =>
      (bytesOfList 32 (s.toList ++ r.toList),
        bytesOfList (2 * n - 32) ((s.toList ++ r.toList).drop 32))) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun kt =>
    (bytesOfList n (kt.1.toList ++ kt.2.toList),
      bytesOfList n ((kt.1.toList ++ kt.2.toList).drop n)), fun ⟨s, r⟩ => ?_, fun ⟨k, t⟩ => ?_⟩
  · have hl : (s.toList ++ r.toList).length = 2 * n := by simp; omega
    have hl' : (bytesOfList 32 (s.toList ++ r.toList)).toList ++
        (bytesOfList (2 * n - 32) ((s.toList ++ r.toList).drop 32)).toList =
          s.toList ++ r.toList := by
      rw [toList_bytesOfList_of_le (k := 32) (by rw [hl]; omega),
        toList_bytesOfList_of_le (k := 2 * n - 32) (by rw [List.length_drop, hl]),
        List.take_of_length_le (l := (s.toList ++ r.toList).drop 32)
          (by rw [List.length_drop, hl]), List.take_append_drop]
    simp only [Function.uncurry_apply_pair, hl']
    refine Prod.ext ?_ ?_
    · rw [bytesOfList_append_of_length_eq (by simp), bytesOfList_toList]
    · rw [List.drop_left' (by simp), bytesOfList_toList]
  · have hl : (k.toList ++ t.toList).length = 2 * n := by simp; omega
    have hl' : (bytesOfList n (k.toList ++ t.toList)).toList ++
        (bytesOfList n ((k.toList ++ t.toList).drop n)).toList = k.toList ++ t.toList := by
      rw [toList_bytesOfList_of_le (k := n) (by rw [hl]; omega),
        toList_bytesOfList_of_le (k := n) (l := (k.toList ++ t.toList).drop n)
          (by rw [List.length_drop, hl]; omega),
        List.take_of_length_le (l := (k.toList ++ t.toList).drop n)
          (by rw [List.length_drop, hl]; omega), List.take_append_drop]
    simp only [Function.uncurry_apply_pair, hl']
    refine Prod.ext ?_ ?_
    · rw [bytesOfList_append_of_length_eq (by simp), bytesOfList_toList]
    · rw [List.drop_left' (by simp), bytesOfList_toList]

/-- **The weak-key mass, averaged over the public seed.** For `16 ≤ n`, the weak-key mass of a
uniform public seed is at most `|A_hon| / 2^256`, with `|A_hon| = honestAdrsCount vp`: the first
`32` bytes of `PK.seed ‖ r` are a uniform address key when both halves are uniform. -/
theorem lintegral_weakKeyMass_le (hn : 16 ≤ vp.params.n)
    [MeasurableSpace (shakeCore vp).PkSeed] [DiscreteMeasurableSpace (shakeCore vp).PkSeed] :
    ∫⁻ pkSeed, weakKeyMass vp pkSeed ∂𝒟[($ᵗ (shakeCore vp).PkSeed : ProbComp _)] ≤
      honestAdrsCount vp / 2 ^ 256 := by
  calc ∫⁻ pkSeed, weakKeyMass vp pkSeed ∂𝒟[($ᵗ (shakeCore vp).PkSeed : ProbComp _)]
      = Pr{let s ← $ᵗ (shakeCore vp).PkSeed; let r ← $ᵗ (shakeCore vp).Y}[
          IsWeakKey vp ⟨s, r⟩] := by
        rw [prEvent_bind _ _ Measurable.of_discrete]
        rfl
    _ = Pr{let kt ← $ᵗ (Bytes 32 × Bytes (2 * vp.params.n - 32))}[
          IsHonestKey vp (shakeCore vp) kt.1] :=
        SampleableType.prEvent_uniformSample_pair_of_bijective
          (g := fun (s : (shakeCore vp).PkSeed) (r : (shakeCore vp).Y) =>
            (bytesOfList 32 (Vector.toList (s : Bytes vp.params.n) ++
              Vector.toList (r : Bytes vp.params.n)),
            bytesOfList (2 * vp.params.n - 32) ((Vector.toList (s : Bytes vp.params.n) ++
              Vector.toList (r : Bytes vp.params.n)).drop 32)))
          (bijective_splitKey (by omega)) fun kt => IsHonestKey vp (shakeCore vp) kt.1
    _ = Pr{let k ← $ᵗ (Bytes 32)}[IsHonestKey vp (shakeCore vp) k] :=
        SampleableType.prEvent_uniformSample_fst _
    _ ≤ honestAdrsCount vp / 2 ^ 256 := ?_
  let _ : MeasurableSpace (Bytes 32) := ⊤
  have _ : DiscreteMeasurableSpace (Bytes 32) := ⟨fun _ => trivial⟩
  refine (le_of_eq (prEvent_eq_evalDist_of_discrete ($ᵗ (Bytes 32))
    (IsHonestKey vp (shakeCore vp)))).trans
      ((SampleableType.evalDist_uniformSample_le_encard_div _).trans ?_)
  rw [natCard_bytes_32, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact_mod_cast encard_setOf_isHonestKey_le (shakeCore vp)

/-- **The averaged bound with a seed-independent part.** For `16 ≤ n`, averaging `C` plus the
weak-key mass times `D` over a uniform public seed gives at most `C + |A_hon| / 2^256 · D`. This is
the shape in which a per-seed bound `C + weakKeyMass vp pkSeed * D` averages through
`shakeStrongAdvantage_le_lintegral`. -/
theorem lintegral_add_weakKeyMass_mul_le (hn : 16 ≤ vp.params.n)
    [MeasurableSpace (shakeCore vp).PkSeed] [DiscreteMeasurableSpace (shakeCore vp).PkSeed]
    (C D : ℝ≥0∞) :
    ∫⁻ pkSeed, (C + weakKeyMass vp pkSeed * D) ∂𝒟[($ᵗ (shakeCore vp).PkSeed : ProbComp _)] ≤
      C + honestAdrsCount vp / 2 ^ 256 * D := by
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_mul_const _ Measurable.of_discrete]
  gcongr
  · exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)
  · exact lintegral_weakKeyMass_le hn

/-- For `16 ≤ n`, averaging `C` plus the weak-key mass over a uniform public seed gives at most
`C + |A_hon| / 2^256`. -/
theorem lintegral_add_weakKeyMass_le (hn : 16 ≤ vp.params.n)
    [MeasurableSpace (shakeCore vp).PkSeed] [DiscreteMeasurableSpace (shakeCore vp).PkSeed]
    (C : ℝ≥0∞) :
    ∫⁻ pkSeed, (C + weakKeyMass vp pkSeed) ∂𝒟[($ᵗ (shakeCore vp).PkSeed : ProbComp _)] ≤
      C + honestAdrsCount vp / 2 ^ 256 := by
  simpa only [mul_one] using lintegral_add_weakKeyMass_mul_le hn C 1

/-! ### At `n = 32` -/

/-- At `n = 32`, a public key is weak exactly when its public seed is an honest address key: the
first `32` bytes of `PK.seed ‖ PK.root` are `PK.seed`. -/
theorem isWeakKey_iff_of_n_eq_32 (hn : vp.params.n = 32) (pk : PublicKeyCore (shakeCore vp)) :
    IsWeakKey vp pk ↔
      IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pk.pkSeed : Bytes _))) := by
  unfold IsWeakKey
  rw [adrsKeyOfList, adrsKeyOfList, bytesOfList_append_of_length_eq
    (by rw [Vector.length_toList (xs := (pk.pkSeed : Bytes vp.params.n)), hn])]

/-- At `n = 32`, a public seed that is not an honest address key has weak-key mass zero. -/
theorem weakKeyMass_eq_zero_of_n_eq_32 (hn : vp.params.n = 32) {pkSeed : (shakeCore vp).PkSeed}
    (h : ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _)))) :
    weakKeyMass vp pkSeed = 0 :=
  prEvent_eq_zero_of_forall_not _ _ fun r hr => h ((isWeakKey_iff_of_n_eq_32 hn ⟨pkSeed, r⟩).1 hr)

/-- At `n = 32`, a public seed that is an honest address key has weak-key mass one. -/
theorem weakKeyMass_eq_one_of_n_eq_32 (hn : vp.params.n = 32) {pkSeed : (shakeCore vp).PkSeed}
    (h : IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _)))) :
    weakKeyMass vp pkSeed = 1 :=
  (SampleableType.prEvent_uniformSample_eq_one_iff _).2 fun r =>
    (isWeakKey_iff_of_n_eq_32 hn ⟨pkSeed, r⟩).2 h

/-- At `n = 32`, a public seed has weak-key mass zero exactly when it is not an honest address key;
otherwise its mass is one. -/
theorem weakKeyMass_eq_zero_iff_of_n_eq_32 (hn : vp.params.n = 32)
    (pkSeed : (shakeCore vp).PkSeed) :
    weakKeyMass vp pkSeed = 0 ↔
      ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _))) :=
  ⟨fun h0 hk => zero_ne_one (h0.symm.trans (weakKeyMass_eq_one_of_n_eq_32 hn hk)),
    weakKeyMass_eq_zero_of_n_eq_32 hn⟩

/-- At `n = 32`, the weak-key mass of every public seed is zero or one. -/
theorem weakKeyMass_eq_zero_or_eq_one_of_n_eq_32 (hn : vp.params.n = 32)
    (pkSeed : (shakeCore vp).PkSeed) :
    weakKeyMass vp pkSeed = 0 ∨ weakKeyMass vp pkSeed = 1 := by
  by_cases hk : IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _)))
  · exact .inr (weakKeyMass_eq_one_of_n_eq_32 hn hk)
  · exact .inl (weakKeyMass_eq_zero_of_n_eq_32 hn hk)

/-- **The weak seeds, pointwise, at `n = 32`.** At `n = 32`, for every public seed, the smaller of
`C` plus the weak-key mass and `D` is at most `C` plus the weak-key mass times `min 1 D`: the mass
is zero or one. -/
theorem min_add_weakKeyMass_le_of_n_eq_32 (hn : vp.params.n = 32)
    (pkSeed : (shakeCore vp).PkSeed) (C D : ℝ≥0∞) :
    min (C + weakKeyMass vp pkSeed) D ≤ C + weakKeyMass vp pkSeed * min 1 D := by
  rcases weakKeyMass_eq_zero_or_eq_one_of_n_eq_32 hn pkSeed with h | h <;> rw [h]
  · simp
  · rw [one_mul, ← min_add_add_left]
    exact min_le_min le_rfl le_add_self

/-- **No weak-key term off the weak seeds at `n = 32`.** At `n = 32`, in the run at a public seed
that is not an honest address key, the public key is never weak. -/
theorem prEvent_romSchemeRun_isWeakKey_eq_zero_of_n_eq_32 (hb : CanonicalAddressBounds vp.params)
    (hn : vp.params.n = 32) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    {pkSeed : (shakeCore vp).PkSeed}
    (h : ¬IsHonestKey vp (shakeCore vp) (adrsKeyOfList vp (Vector.toList (pkSeed : Bytes _))))
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))) :
    Pr{let z ← romSchemeRun (shakeCore vp) e optRand (pure pkSeed) adv}[IsWeakKey vp z.1.pk] = 0 :=
  le_antisymm ((prEvent_romSchemeRun_isWeakKey_le hb e optRand pkSeed adv).trans
    (weakKeyMass_eq_zero_of_n_eq_32 hn h).le) bot_le

end Bound

end SLHDSA.Security
