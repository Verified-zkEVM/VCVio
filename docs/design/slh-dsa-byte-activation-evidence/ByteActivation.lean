/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.ByteClash
public import HashSig.SLHDSA.Security.JointBound
import HashSig.SLHDSA.AddressDiscipline

/-! # Signing activation of byte aliases and independent terminal keys -/

public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
namespace SLHDSA.Security

private theorem keygen_no_prf (vp : ValidatedParams)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed) :
    AllQueriesSatisfy ((romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)).keygen)
      (Sum.elim (fun _ => True) fun q => q.isLeft = true) := by
  let allowed : (unifSpec + hashSpec (shakeCore vp)).Domain → Prop :=
    Sum.elim (fun _ => True) fun q => q.isLeft = true
  unfold romScheme romKeygenAt
  refine allQueriesSatisfy_bind (allQueriesSatisfy_liftM_sum_elim _ _) fun seed => ?_
  refine allQueriesSatisfy_bind (allQueriesSatisfy_liftM_sum_elim _ _) fun skSeed => ?_
  refine allQueriesSatisfy_bind (allQueriesSatisfy_liftM_sum_elim _ _) fun _ => ?_
  apply allQueriesSatisfy_bind
  · exact GeneralScheme.keygenInternalWithSecretM_pred
      (m := OracleComp (unifSpec + hashSpec (shakeCore vp)))
      (fun {α : Type} (body : OracleComp (unifSpec + hashSpec (shakeCore vp)) α) =>
        AllQueriesSatisfy body allowed)
      (fun _ => allQueriesSatisfy_pure _ _) (fun _ _ => allQueriesSatisfy_bind)
      (shakeCore vp) (fun address _ => by
        unfold oracleSecret
        change AllQueriesSatisfy
          (liftM ((unifSpec + hashSpec (shakeCore vp)).query
            (.inr (.inl (.thash seed ((shakeCore vp).adrsToKey address) [skSeed]))))) allowed
        exact (allQueriesSatisfy_query_iff _ _).2 rfl) seed
      fun _ _ _ => (allQueriesSatisfy_query_iff _ _).2 rfl
  · intro _
    exact allQueriesSatisfy_pure _ _

private theorem verify_no_prf (vp : ValidatedParams)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed) (pk : PublicKeyCore (shakeCore vp))
    (message : List Byte) (signature : GeneralScheme.SignatureCore vp (shakeCore vp)) :
    AllQueriesSatisfy
      ((romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)).verify pk message signature)
      (Sum.elim (fun _ => True) fun q => q.isLeft = true) := by
  exact GeneralScheme.verifyInternalM_pred (AllQueriesSatisfy · _)
    (fun _ => allQueriesSatisfy_pure _ _) (fun _ _ => allQueriesSatisfy_bind) (shakeCore vp)
    message signature pk (fun _ _ _ => (allQueriesSatisfy_query_iff _ _).2 rfl)
    ((allQueriesSatisfy_query_iff _ _).2 rfl)

private theorem route_eq_or_signed_of_prf_cached
    (vp : ValidatedParams) (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed)))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
      (routeAdv vp hn hnm adv))) (query : PrfMsgQuery (shakeCore vp).SkPrf (shakeCore vp).Y)
    (cached : (z.2 (.inr query)).isSome) :
    shakeRoute vp (IsHonestKey vp (shakeCore vp)) z.1.pk.pkSeed
      (encode vp (.inr query)) = some (.inr query) ∨ z.1.log ≠ [] := by
  classical
  let P : (hashSpec (shakeCore vp)).Domain → Prop := fun q =>
    q.isLeft = true ∨ shakeRoute vp (IsHonestKey vp (shakeCore vp)) z.1.pk.pkSeed
      (encode vp q) = some q
  obtain ⟨first, last, hkeygen, hclient, hverify⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment
      (hashSpec (shakeCore vp)).romImpl (routeAdv vp hn hnm adv) hz
  have hstart : ∀ q, (first q).isSome → P q := by
    intro q hq
    exact Or.inl (forall_isSome_of_mem_support_run_simulateQ_romImpl
      (keygen_no_prf vp optRand pkSeed) (fun _ h => by simp at h) hkeygen q hq)
  let I := fun (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp (shakeCore vp)))
      (cache : (hashSpec (shakeCore vp)).QueryCache) =>
    log = [] → ∀ q, (cache q).isSome → P q
  have hstage : I z.1.log last := by
    refine holds_of_mem_support_run_runWithSigningOracle
      (hashSpec (shakeCore vp)).romImpl
      (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)) z.1.pk z.1.sk I
      (allowed := Sum.elim (fun _ => True) fun q =>
        (shakeEncoding vp hn hnm z.1.pk.pkSeed).route (encode vp q) = some q)
      ?_ ?_ (allQueriesSatisfy_routeAdv_main hn hnm adv z.1.pk) (fun _ => hstart) hclient
    · intro input allowed log cache held result hresult empty
      apply forall_isSome_of_mem_support_run_romImpl _ (held empty) hresult
      rcases input with n | q
      · exact trivial
      · exact Or.inr allowed
    · intro message log cache _ result _ empty
      have impossible := (List.append_eq_nil_iff.mp empty).2
      simp at impossible
  by_cases hempty : z.1.log = []
  · left
    have hall : ∀ q, (z.2 q).isSome → P q :=
      forall_isSome_of_mem_support_run_simulateQ_romImpl
        ((verify_no_prf vp optRand pkSeed z.1.pk z.1.msg z.1.sig).mono (by
          rintro (n | q) h
          · exact trivial
          · exact Or.inl h))
        (hstage hempty) hverify
    exact (hall (.inr query) cached).resolve_left (by simp)
  · exact Or.inr hempty

private theorem activated_clash_cases
    (vp : ValidatedParams) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed)))
    {z : RomOutcome vp (shakeCore vp) × (hashSpec (shakeCore vp)).QueryCache}
    (hz : z ∈ support (romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
      (routeAdv vp hn hnm adv))) (clash : (shakeEncoding vp hn hnm pkSeed).Clash z.2) :
    ((HmsgAtPrfKey id z.1.sk.skPrf z.2 ∨ z.1.sk.skPrf = pkSeed) ∧ z.1.log ≠ []) ∨
      IsWeakKey vp z.1.pk := by
  have hpk : z.1.pk.pkSeed = pkSeed := by
    simpa using pkSeed_mem_support_of_mem_support_romSchemeRun _ optRand _ hz
  have hc := route_eq_some_or_of_mem_support_romSchemeRun_routeAdv hn hnm adv hz
  rw [hpk] at hc
  obtain ⟨q, other, distinct, cached, otherCached, equal, nonfixed⟩ := clash.exists_route_ne
  rcases hc q cached with fixed | ⟨R, message, rfl⟩ | ⟨randomizer, message, rfl⟩
  · exact (nonfixed fixed).elim
  · right
    have ht : IsThashString vp (IsHonestKey vp (shakeCore vp)) pkSeed
        (encode vp (.inl (.hmsg R pkSeed z.1.pk.pkRoot message))) := by
      by_contra ht
      exact nonfixed (shakeRoute_encode_hmsg _ _ _ ht)
    have hr : R = pkSeed :=
      Vector.toList_inj.1 (toList_eq_of_isThashString_encode_hmsg _ ht)
    have hw : HmsgAtWeakKey pkSeed z.1.pk.pkRoot z.2 :=
      ⟨message, hr ▸ cached, hr ▸ ht⟩
    simpa only [← hpk] using isWeakKey_of_hmsgAtWeakKey hn16 hw
  · have signed : z.1.log ≠ [] := by
      rcases route_eq_or_signed_of_prf_cached vp hn hnm optRand pkSeed adv hz _ cached
        with fixed | signed
      · apply False.elim
        apply nonfixed
        simpa only [shakeEncoding_route, shakeEncoding_encode, hpk] using fixed
      · exact signed
    rcases hmsgAtPrfKey_and_prfMsgAt_or_eq_of_shakeRoute_ne_prfMsg
      hc cached otherCached distinct equal nonfixed with hit | key
    · exact Or.inl ⟨Or.inl hit.1, signed⟩
    · exact Or.inl ⟨Or.inr key, signed⟩

/-- Byte aliases involving the signing PRF require an actual signing callback. -/
theorem shakeStrongAdvantage_pure_le_activated_key_clash
    (vp : ValidatedParams) (hn16 : 16 ≤ vp.params.n)
    (hn : vp.params.n ≤ 32) (hnm : vp.params.n ≤ vp.params.m)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : StrongUnforgeableAdversary
      (shakeRomScheme vp optRand (pure pkSeed))) :
    shakeStrongAdvantage vp adv ≤
      Pr{let z ← romSchemeRun (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed)
          (routeAdv vp hn hnm adv.toUnforgeableAdversary)}[
        (z.1.strongWins = true ∨
          ((HmsgAtPrfKey id z.1.sk.skPrf z.2 ∨ z.1.sk.skPrf = pkSeed) ∧ z.1.log ≠ [])) ∨
            IsWeakKey vp z.1.pk] := by
  refine (shakeStrongAdvantage_pure_le hn hnm pkSeed adv).trans
    (prEvent_mono_of_support _ _ _ fun z hz event => ?_)
  rcases event with win | clash
  · exact Or.inl (Or.inl win)
  · rcases activated_clash_cases vp hn16 hn hnm optRand pkSeed
      adv.toUnforgeableAdversary hz clash with activated | weak
    exacts [Or.inl (Or.inr activated), Or.inr weak]

/-- An independent terminal key draw factors from any retained seed-free activation event. -/
theorem prEvent_deferredFillDraw_skPrf_eq_and_event_eq
    {vp : ValidatedParams} (core : CorePrimitives vp.params)
    [SampleableType core.Y] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
    [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (pkSeed : core.PkSeed) {α : Type}
    (program : OracleComp (labSpec core) α) (active : α → Prop)
    (key : core.SkPrf) :
    Pr{let w ← (slhGraph core pkSeed).deferredFillDraw
        ($ᵗ (core.SkSeed × core.SkPrf)) program}[
      w.2.2.2 = key ∧ active w.1.1] =
    Pr{let w ← (slhGraph core pkSeed).deferredFillDraw
        ($ᵗ (core.SkSeed × core.SkPrf)) program}[
      active w.1.1] / Nat.card core.SkPrf := by
  classical
  let beforeSeeds := do
    let z ← (simulateQ (slhGraph core pkSeed).deferredImpl program).run ((∅, ∅), [])
    let filled ← RelabelState.endFill z.2
    pure (z, filled)
  have hkey : Pr{let s ← ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _)}[s.2 = key] =
      (Nat.card core.SkPrf : ℝ≥0∞)⁻¹ := by
    rw [SampleableType.prEvent_uniformSample_prod]
    calc
      _ = Pr{let y ← ($ᵗ core.SkPrf : ProbComp _)}[y = key] := by
        simpa only [map_bind] using OracleComp.prEvent_bind_const
          ($ᵗ core.SkSeed : ProbComp _)
          ((fun y : core.SkPrf => y = key) <$> ($ᵗ core.SkPrf : ProbComp _))
      _ = _ := SampleableType.prEvent_uniformSample_eq_singleton_natCard key
  have h := prEvent_bind_bind_and beforeSeeds ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _)
    (fun z => active z.1.1) (fun s => s.2 = key)
  have htrue := prEvent_bind_bind_and beforeSeeds ($ᵗ (core.SkSeed × core.SkPrf) : ProbComp _)
    (fun z => active z.1.1) (fun _ => True)
  simp only [and_true, prEvent_true_eq_one, mul_one] at htrue
  rw [hkey] at h
  simpa only [beforeSeeds, CanonicalGraph.deferredFillDraw, bind_assoc, prEvent_norm,
    and_comm, div_eq_mul_inv] using h.trans (congrArg (· * (Nat.card core.SkPrf : ℝ≥0∞)⁻¹)
      htrue.symm)

#print axioms shakeStrongAdvantage_pure_le_activated_key_clash
#print axioms prEvent_deferredFillDraw_skPrf_eq_and_event_eq
end SLHDSA.Security
