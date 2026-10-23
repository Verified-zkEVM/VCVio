/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareClaims
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget

/-!
# The real event raises the lenient flag

At the end of the coupling, the shared half's event on the real side — a sensitive claim, a
`PRF_msg` guess at `SK.prf` in the record, or the signer's randomiser hitting `SK.prf` — has
raised the lenient game's flag. This file proves it in pieces.

This first part is about the real cache, which the coupling says is the view of the lenient
state: it is the table's union cache over the lenient entries, so the key it generates is the
setup's, and the digits its replay reveals are at most the table's (`ShareCells.revealedOf`) —
which is what makes the real game's availability contain the lenient game's.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareEvent

variable {α : Type}

open Security CanonicalGraph ShareGame ShareCouple ShareInv

/-! ## The real cache is the table's union cache -/

theorem realView_eq_unionCache (setup : Setup) (state : St) :
    realView setup state = RedrawCell.unionCache setup.publicSeed setup.table (merged setup state) := by
  ext input : 1
  rw [realView, RedrawCell.unionCache, QueryCache.ofFn_apply, QueryCache.ofFn_apply,
    RedrawCell.openCache_total]
  rfl

/-- **The key the real cache generates is the setup's.** -/
theorem generatedKey_realView (setup : Setup) (state : St) :
    SplitCharged.generatedKey (setup.table.1 Node.secretSeed) setup.prf setup.publicSeed
      (realView setup state) = setup.pk := by
  rw [realView_eq_unionCache]
  show (⟨setup.publicSeed, @Scheme.keygenInternal Id Id.instMonad
      (CacheReplay.replayQuery (RedrawCell.unionCache setup.publicSeed setup.table
        (merged setup state))) (setup.table.1 Node.secretSeed) setup.prf setup.publicSeed |>.2.root⟩ :
      PublicKey) = ⟨setup.publicSeed, setup.table.1 (.structural topRoot)⟩
  rw [@keygen_root_cell (CacheReplay.replayQuery (RedrawCell.unionCache setup.publicSeed
    setup.table (merged setup state))), RedrawCell.value_unionCache]

/-! ## The real digits are at most the table's -/

/-- **The message a hypertree key signs, replayed at a union cache, is the table's cell.** -/
theorem honestMessage_unionCache (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (key : WotsKey) (node : StructuralNode)
    (hnode : ShareCells.messageNode key = some node) :
    @GraphStakes.honestMessage (CacheReplay.replayQuery (RedrawCell.unionCache publicSeed table cache))
        (table.1 Node.secretSeed) publicSeed key = table.1 (.structural node) := by
  unfold ShareCells.messageNode at hnode
  split at hnode
  · rename_i hlayer
    cases hnode
    simp only [GraphStakes.honestMessage, hlayer]
    exact RedrawCell.value_unionCache publicSeed table cache _
  · rename_i layer hlayer
    split_ifs at hnode with hl ht
    cases hnode
    simp only [GraphStakes.honestMessage, hlayer]
    show @Merkle.node Id _ (CacheReplay.replayQuery (RedrawCell.unionCache publicSeed table cache))
        (table.1 Node.secretSeed) publicSeed
        (⟨⟨layer, hl⟩, ⟨_, ht⟩⟩ : Tree).address subtreeHeight 0 = _
    rw [HonestProbes.subtree_root_cell, RedrawCell.replayCells_unionCache]

theorem honestRevealed_le_revealedOf (publicSeed : Digest) (table : Cells × Padding)
    (cache : QueryCache HashSpec) (key : WotsKey) (chain : Fin chains) :
    @GraphStakes.honestRevealed (CacheReplay.replayQuery (RedrawCell.unionCache publicSeed table cache))
        (table.1 Node.secretSeed) publicSeed key chain ≤
      ShareCells.revealedOf table.1 key chain := by
  unfold ShareCells.revealedOf
  split
  · rename_i node hnode
    unfold GraphStakes.honestRevealed
    rw [honestMessage_unionCache publicSeed table cache key node hnode]
  · exact @GraphStakes.honestRevealed_le
      (CacheReplay.replayQuery (RedrawCell.unionCache publicSeed table cache)) _ _ key chain

/-- **Availability is monotone in both the digits and the disclosed set.** -/
theorem available_mono (revealed revealed' : WotsKey → Fin chains → Nat)
    (signed signed' : ForsKey → Finset (Fin (forsTrees * 2 ^ forsHeight)))
    (hrevealed : ∀ key chain, revealed' key chain ≤ revealed key chain)
    (hsigned : ∀ key, signed key ⊆ signed' key) (node : Node)
    (havailable : Available revealed signed node) : Available revealed' signed' node := by
  cases node with
  | secretSeed => exact havailable
  | structural parent =>
    cases parent with
    | wotsPrf key chain =>
      have h : revealed key chain = 0 := havailable
      show revealed' key chain = 0
      have := hrevealed key chain
      omega
    | wotsHash key chain step =>
      have h : revealed key chain ≤ step.val + 1 := havailable
      show revealed' key chain ≤ step.val + 1
      exact (hrevealed key chain).trans h
    | forsPrf key index => exact hsigned key havailable
    | wotsPk key => exact True.intro
    | tree location height index => exact True.intro
    | forsTree key height index => exact True.intro
    | forsRoots key => exact True.intro

/-! ## The lenient disclosed set is inside the real one -/

/-- The assembled signature carries the randomiser it was given. -/
theorem cellSig_randomizer (cache : QueryCache HashSpec) (sk : SecretKey) (randomizer : Digest)
    (digest : HashOutput) :
    (ShareSigner.cellSig cache sk randomizer digest).randomizer = randomizer := rfl

/-- **What the lenient game says was served, the real log says was served.** -/
theorem disclosed_subset (setup : Setup) (p : St × Bool) (hinv : Inv setup p)
    (result : (Outcome × Nat) × QueryCache HashSpec) (hlog : result.1.1.signed = p.1.log)
    (hcache : result.2 = realView setup p.1) (key : ForsKey) :
    disclosed p.1.served key ⊆ ServedLog.disclosedByLog setup.pk result key := by
  classical
  intro index hindex
  simp only [disclosed, Finset.mem_filter, Finset.mem_univ, true_and] at hindex
  obtain ⟨digest, hdigest, hkey, tree, htree⟩ := hindex
  obtain ⟨entry, hentry, framed, hframe, value, -, hbytes, hview⟩ := hinv.served digest hdigest
  rw [ServedLog.mem_disclosedByLog]
  refine ⟨Hashing.messageInput (Hashing.truncate value) setup.pk framed, digest, ?_,
    by rw [hcache]; exact hview, hkey, tree, htree⟩
  exact ⟨entry, by rw [hlog]; exact hentry, framed, _, _, hframe, hbytes,
    Signature.fromBytes_toBytes _, by rw [cellSig_randomizer]⟩

/-! ## On the verifier's probes, the real cache is the visible one -/

/-- **Off the flag, a filed probe reads the same in the real cache and in the visible one.** -/
theorem realView_eq_visible (setup : Setup) (p : St × Bool) (hinv : Inv setup p)
    (hflag : p.2 = false) (input : Bytes)
    (hfiled : ∃ entry ∈ p.1.record, entry.1 = input ∧ entry.2 = p.1.served) :
    realView setup p.1 input = visible setup p.1 input := by
  classical
  obtain ⟨entry, hentry, hinput, hsnap⟩ := hfiled
  have hnot : ¬ Guess setup p.1.served input := fun hguess => by
    have := hinv.closed entry hentry (by rw [hinput, hsnap]; exact hguess)
    rw [hflag] at this
    cases this
  unfold visible
  rw [QueryCache.ofFn_apply]
  cases hwarm : setup.warm input with
  | some answer =>
    rw [realView_of_warm setup p.1 input answer hwarm]
    cases hopen : openAt setup p.1.served input with
    | some b =>
      have := ShareUntilBad.openAt_le_warm setup p.1.served input b hopen
      rw [hwarm] at this
      exact this
    | none =>
      exact absurd (Or.inl (ShareUntilBad.sens_of_closed setup p.1.served input answer hwarm hopen))
        hnot
  | none =>
    rw [realView_of_not_warm setup p.1 input hwarm, merged, QueryCache.ofFn_apply]
    have hprf : ¬ IsPrfInput setup input := fun h =>
      hnot (Or.inr (ShareUntilBad.prfClass_of_isPrfInput setup input h))
    rw [ite_eq_right hprf]
    cases hopen : openAt setup p.1.served input with
    | none => rfl
    | some b =>
      have := ShareUntilBad.openAt_le_warm setup p.1.served input b hopen
      rw [hwarm] at this
      cases this

/-! ## The verifier's probes are in its record -/

/-- The flattened verifier at a hash input. -/
noncomputable def realHashImpl :
    QueryImpl HashSpec (StateT SharePresent.VerifyState ProbComp) :=
  fun input => SharePresent.realWorldImpl (Sum.inr input)

/-- The flattened verifier at a coin. -/
noncomputable def realCoinImpl :
    QueryImpl unifSpec (StateT SharePresent.VerifyState ProbComp) :=
  fun coin => SharePresent.realWorldImpl (Sum.inl coin)

theorem realWorldImpl_eq_add :
    SharePresent.realWorldImpl = realCoinImpl + realHashImpl := by
  funext queried
  rcases queried with coin | input <;> rfl

theorem realHashImpl_run (input : Bytes) (state : SharePresent.VerifyState) :
    (realHashImpl input).run state =
      (fun z => (z.1, (state.1 * Multiplicative.ofAdd (RecordedQueries.verifierCost (Sum.inr input)),
        z.2))) <$>
        (KeygenUniform.rom (Sum.inr input)).run state.2 := rfl

/-- One flattened verifier step at a hash input: charged, stored, and nothing lost. -/
theorem realHash_step (input : Bytes) (tally : Multiplicative RecordedQueries.Tally)
    (cache : QueryCache HashSpec) (z : HashOutput × SharePresent.VerifyState)
    (hz : z ∈ support ((realHashImpl input).run (tally, cache))) :
    z.2.1 = tally * Multiplicative.ofAdd (RecordedQueries.verifierCost (Sum.inr input)) ∧
      z.2.2 input = some z.1 ∧ ∀ other value, cache other = some value → z.2.2 other = some value := by
  rw [realHashImpl_run] at hz
  obtain ⟨inner, hinner, rfl⟩ := ShareRealCap.exists_of_mem_support_map _ _ _ hz
  refine ⟨rfl, ?_⟩
  cases hc : cache input with
  | some v =>
    rw [CoverageCount.rom_run_inr_some input cache v hc, support_pure,
      Set.mem_singleton_iff] at hinner
    subst hinner
    exact ⟨hc, fun _ _ h => h⟩
  | none =>
    rw [CoverageCount.rom_run_inr_none input cache hc] at hinner
    obtain ⟨v, -, rfl⟩ := ShareRealCap.exists_of_mem_support_map _ _ _ hinner
    refine ⟨QueryCache.cacheQuery_self _ _ _, fun other w h => ?_⟩
    show cache.cacheQuery input v other = some w
    by_cases ho : other = input
    · subst ho; rw [hc] at h; cases h
    · rw [QueryCache.cacheQuery_of_ne _ _ ho]; exact h

/-- Along a flattened verifier run the record and the cache only grow. -/
theorem realHash_run_mono {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (tally : Multiplicative RecordedQueries.Tally) (cache : QueryCache HashSpec),
      ∀ z ∈ support ((simulateQ realHashImpl computation).run (tally, cache)),
        (Multiplicative.toAdd tally).2 ≤ (Multiplicative.toAdd z.2.1).2 ∧
          ∀ other value, cache other = some value → z.2.2 other = some value := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro tally cache z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_refl _, fun _ _ h => h⟩
  | query_bind input next ih =>
    intro tally cache z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    obtain ⟨htally, -, hpersist⟩ := realHash_step input tally cache step hstep
    obtain ⟨hle, hpersist'⟩ := ih step.1 step.2.1 step.2.2 z hrest
    refine ⟨le_trans ?_ hle, fun other v h => hpersist' other v (hpersist other v h)⟩
    rw [htally]
    simp

/-- **Every probe a replay of the verified computation makes at the final cache is recorded.** -/
theorem probe_recorded {α : Type} (computation : OracleComp HashSpec α) (probe : Bytes)
    (finalTally : Multiplicative RecordedQueries.Tally) (finalCache : QueryCache HashSpec)
    (hquery : CacheReplay.QueriesUnder finalCache computation probe) :
    ∀ (tally : Multiplicative RecordedQueries.Tally) (cache : QueryCache HashSpec) (result : α),
      (result, (finalTally, finalCache)) ∈
        support ((simulateQ realHashImpl computation).run (tally, cache)) →
      probe ∈ (Multiplicative.toAdd finalTally).2 := by
  induction hquery with
  | head input next =>
    intro tally cache result hmem
    rw [simulateQ_bind, show simulateQ realHashImpl (query (spec := HashSpec) input) =
        realHashImpl input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨htally, -, -⟩ := realHash_step input tally cache step hstep
    obtain ⟨hle, -⟩ := realHash_run_mono (next step.1) step.2.1 step.2.2 _ hrest
    refine Multiset.mem_of_le hle ?_
    rw [htally]
    simp [RecordedQueries.verifierCost, RecordedQueries.recordOf]
  | tail input probe next _ ih =>
    intro tally cache result hmem
    rw [simulateQ_bind, show simulateQ realHashImpl (query (spec := HashSpec) input) =
        realHashImpl input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨-, hstored, -⟩ := realHash_step input tally cache step hstep
    obtain ⟨-, hpersist⟩ := realHash_run_mono (next step.1) step.2.1 step.2.2 _ hrest
    have hfinal : finalCache input = some step.1 := hpersist input step.1 hstored
    have hreplay : CacheReplay.replay finalCache input = step.1 := by
      simp [CacheReplay.replay, hfinal]
    exact ih step.2.1 step.2.2 result (by rw [hreplay]; exact hrest)

/-- **At the real game's verifier**: every probe of the replayed verifier at the final cache is in
the verifier's record. -/
theorem verify_probes_recorded (pk : PublicKey) (request : Message) (signature : Bytes)
    (cache : QueryCache HashSpec)
    (w : Bool × SharePresent.VerifyState)
    (hw : w ∈ support ((simulateQ SharePresent.realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) pk request signature)).run (1, cache)))
    (probe : Bytes)
    (hprobe : CacheReplay.QueriesUnder w.2.2
      (Scheme.verify (m := OracleComp HashSpec) pk request signature) probe) :
    probe ∈ (Multiplicative.toAdd w.2.1).2 := by
  rw [VerificationBudget.verify_lift, realWorldImpl_eq_add,
    QueryImpl.simulateQ_add_liftComp_right] at hw
  exact probe_recorded _ probe w.2.1 w.2.2 hprobe 1 cache w.1 hw

/-! ## The event, read at the coupling's two ends -/

/-- The real game's recorded pair, at a setup's walk. -/
noncomputable def realPair (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec) : SharedJoin.RecordedPair :=
  (WalkTable.walkOfTable setup.prf setup.publicSeed setup.table,
    ((LinkedGame.outcomeOf real.1, 0), real.2))

/-- A filed `PRF_msg` guess raises the flag. -/
theorem flag_of_filed_prf (setup : Setup) (p : St × Bool) (hinv : Inv setup p) (input : Bytes)
    (hfiled : ∃ entry ∈ p.1.record, entry.1 = input)
    (hclass : RandomizerGate.PrfClass setup.prf input) : p.2 = true := by
  obtain ⟨entry, hentry, rfl⟩ := hfiled
  exact hinv.closed entry hentry (Or.inr hclass)

/-- **The record's `PRF_msg` guess raises the flag.** -/
theorem flag_of_prfHit (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec)
    (p : St × Bool) (hinv : Inv setup p)
    (hadv : ∀ input ∈ (Multiplicative.toAdd real.1.1.1.2).2,
      ∃ entry ∈ p.1.record, entry.1 = input)
    (hver : ∀ input ∈ real.1.1.2.2.2, ∃ entry ∈ p.1.record, entry.1 = input ∧ entry.2 = p.1.served)
    (hhit : Target127.PrfHit (realPair setup real)) : p.2 = true := by
  obtain ⟨input, hinput, hclass⟩ := hhit
  have hmem : input ∈ (Multiplicative.toAdd real.1.1.1.2).2 + real.1.1.2.2.2 :=
    Multiset.mem_toFinset.mp hinput
  rcases Multiset.mem_add.mp hmem with hleft | hright
  · exact flag_of_filed_prf setup p hinv input (hadv input hleft) hclass
  · obtain ⟨entry, hentry, hx, -⟩ := hver input hright
    exact flag_of_filed_prf setup p hinv input ⟨entry, hentry, hx⟩ hclass

/-- **The signer's coincidence raises the flag.** -/
theorem flag_of_signerHit (setup : Setup) (hgood : setup.Good)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec)
    (p : St × Bool) (hinv : Inv setup p) (hcache : real.2 = realView setup p.1)
    (hlog : real.1.2 = p.1.log)
    (hhit : Target127.SignerHit (realPair setup real)) : p.2 = true := by
  obtain ⟨entry, hentry, framed, answer, hframe, hanswer, htruncate⟩ := hhit
  have hentry' : entry ∈ p.1.log := by rw [← hlog]; exact hentry
  obtain ⟨value, hvalue, filed, hfiled, hfiledEq⟩ := hinv.signer entry hentry' framed hframe
  have hprfs : p.1.prfs framed = some answer := by
    have h : realView setup p.1 (Hashing.randomizerInput setup.prf setup.publicSeed framed) =
        some answer := by
      rw [← hcache]
      exact hanswer
    exact prfs_of_realView setup hgood p.1 framed answer h
  rw [hprfs] at hvalue
  cases hvalue
  refine hinv.closed filed hfiled (Or.inr ?_)
  rw [hfiledEq, htruncate, RandomizerGate.messageInput_eq_randomizerInput]
  exact ⟨_, _, rfl⟩

/-- The key the real trace generates is the setup's. -/
theorem keyOf_realPair (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec)
    (p : St × Bool) (hcache : real.2 = realView setup p.1) :
    RoutedSplit.keyOf (SharedJoin.recordedTraceOf (realPair setup real)) = setup.pk := by
  show SplitCharged.generatedKey (setup.table.1 Node.secretSeed) setup.prf setup.publicSeed real.2 =
    setup.pk
  rw [hcache]
  exact generatedKey_realView setup p.1

set_option maxHeartbeats 2000000 in
open scoped Classical in
/-- **A sensitive claim of the real game raises the lenient flag at the claims.** The real output
is assembled from a phase state `zs` and a verifier run `w` from the phase's cache; the phase
itself is not read, so the verifier run need not be capped. -/
theorem flag_of_inputBad (setup : Setup)
    (real : (((Forgery × Multiplicative RecordedQueries.Tally) × (Bool × RecordedQueries.Tally)) ×
      SigningLog) × QueryCache HashSpec)
    (zs : SharePresent.RealState) (w : Bool × SharePresent.VerifyState)
    (hw : w ∈ support ((simulateQ SharePresent.realWorldImpl
      (Scheme.verify (m := OracleComp OracleWorld) setup.pk real.1.1.1.1.message
        real.1.1.1.1.signature)).run (1, zs.2.2)))
    (hreal : real = ((((real.1.1.1.1, zs.1), (w.1, Multiplicative.toAdd w.2.1)), zs.2.1), w.2.2))
    (p : St × Bool) (hinv : Inv setup p) (hflag : p.2 = false)
    (hcache : real.2 = realView setup p.1) (hlog : real.1.2 = p.1.log)
    (hver : ∀ input ∈ real.1.1.2.2.2, ∃ entry ∈ p.1.record, entry.1 = input ∧ entry.2 = p.1.served)
    (hbad : RoutedSplit.InputBad (SharedJoin.recordedTraceOf (realPair setup real))) :
    (ShareWhole.claimsStep setup p real.1.1.1.1).2 = true := by
  classical
  obtain ⟨message, parsed, hframe, hparsed, candidate, hcand, hsens⟩ := hbad
  have hkey := keyOf_realPair setup real p hcache
  rw [hkey] at hcand hsens
  -- The real run's verifier, and its probes.
  have hwCache : real.2 = w.2.2 := congrArg Prod.snd hreal
  have hwTally : real.1.1.2.2 = Multiplicative.toAdd w.2.1 :=
    congrArg (fun r => r.1.1.2.2) hreal
  have hcacheW : w.2.2 = realView setup p.1 := hwCache.symm.trans hcache
  rw [hwTally] at hver
  have hcand' : candidate ∈ @ClaimedProbes.claimedCandidatesOf (CacheReplay.replayQuery w.2.2)
      setup.publicSeed w.2.2 setup.pk message parsed := by
    rw [← hwCache]
    exact hcand
  have hframe' : real.1.1.1.1.message.frame = some message := hframe
  have hparsed' : Signature.fromBytes? real.1.1.1.1.signature = some parsed := hparsed
  have hagree : ∀ probe, CacheReplay.QueriesUnder w.2.2
      (Scheme.verify (m := OracleComp HashSpec) setup.pk real.1.1.1.1.message
        real.1.1.1.1.signature) probe →
        w.2.2 probe = visible setup p.1 probe := by
    intro probe hprobe
    have hrec := verify_probes_recorded setup.pk real.1.1.1.1.message real.1.1.1.1.signature
      zs.2.2 w hw probe hprobe
    obtain ⟨entry, hentry, hx, hsnap⟩ := hver probe hrec
    rw [hcacheW]
    exact realView_eq_visible setup p hinv hflag probe ⟨entry, hentry, hx, hsnap⟩
  have hclaims : claimsOf setup p.1 real.1.1.1.1 =
      @ClaimedProbes.claimedCandidatesOf (CacheReplay.replayQuery w.2.2) setup.publicSeed w.2.2
        setup.pk message parsed := by
    unfold claimsOf
    rw [hframe', hparsed']
    exact (ShareClaims.claimedCandidatesOf_congr setup.publicSeed w.2.2 (visible setup p.1)
      setup.pk real.1.1.1.1.message real.1.1.1.1.signature message parsed hframe' hparsed' rfl
      hagree).symm
  have hguess : Guess setup p.1.served candidate := by
    left
    obtain ⟨node, hunavailable, hinput⟩ := hsens
    refine ⟨node, fun havailable => hunavailable ?_, hinput⟩
    refine available_mono _ _ _ _ (fun key chain => ?_) (fun key => ?_) _ havailable
    · show @GraphStakes.honestRevealed (CacheReplay.replayQuery real.2)
          (setup.table.1 Node.secretSeed) setup.publicSeed key chain ≤ _
      rw [hcache, realView_eq_unionCache]
      exact honestRevealed_le_revealedOf setup.publicSeed setup.table _ key chain
    · exact disclosed_subset setup p hinv _ hlog hcache key
  show (p.2 || decide (¬ setup.Good ∨
    ∃ candidate ∈ claimsOf setup p.1 real.1.1.1.1, Guess setup p.1.served candidate)) = true
  rw [hclaims]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (Or.inr ⟨candidate, hcand', hguess⟩)

end SlhDsaSecurity.ShareEvent
