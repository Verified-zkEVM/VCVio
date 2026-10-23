/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.AnswerFired
public import HashSig.SLHDSA.SHAKE128s.Proof.LateProvenance
public import HashSig.SLHDSA.SHAKE128s.Proof.FreshExpectation
public import HashSig.SLHDSA.SHAKE128s.Proof.BySourceBridge

/-!
# The answer half, with the signer's calls free

The answer half pays for two things out of one budget: the structural faults and the coverage
of the target record. The structural charge is paid per **fresh entry** (`FreshExpectation`), so
the signer's calls are free except where they install an entry, and the fresh entries are counted
where they come from. `LateProvenance.provenance_recordedAfterSeeds`
says an entry the run installed is the adversary's or the verifier's own query, key
generation's, or a signing request's; `HonestProbes` says what each honest party asks: key
generation only canonical inputs, which the walk already holds, and a request only canonical
inputs, its own `PRF_msg` input and its own digest input. A canonical input is never a fault
and never a message input, and a `PRF_msg` input at the real seed is neither either. So the
fresh entries the two charges read — faults and target-class message inputs — are the record's
and at most one digest per request:

  `fresh faults + target entries ≤ |record| + |requests| = work + requests`,

which is inside the work budget, with key generation's top tree to spare.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BySourceAnswer

open Security CacheReplay CanonicalGraph BracketedRun CarrierTail CarrierThin FreshExpectation
  BySourceBridge

/-! ## The two classes -/

/-- An input a structural fault can be read at: one whose canonical target exists. -/
def Deviating (walk : Walk) (input : Bytes) : Prop :=
  CanonicalTarget.canonicalTarget walk.1.1.2.2 walk.1.2 input ≠ none

/-- An input the target record can file: a message input at the walk's key that is not a
`PRF_msg` input at the walk's seed. -/
def Targeted (walk : Walk) (input : Bytes) : Prop :=
  CombinedCharge.IsMessageInput (keyAt walk) input ∧
    ¬ RandomizerGate.PrfClass walk.1.1.2.1 input

theorem targeted_of_keep127 (walk : Walk) (input : Bytes) (view : HandlerCarrier.State)
    (hkeep : keep127 walk input view) : Targeted walk input :=
  ⟨AnswerFired.keep127_class walk input view hkeep, hkeep.2⟩

theorem not_targeted_canonical (walk : Walk)
    (hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root))
    (publicSeed : Digest) (cells : Cells) (parent : StructuralNode) :
    ¬ Targeted walk (canonicalInput publicSeed cells parent) := by
  rintro ⟨⟨randomizer, message, hmessage⟩, -⟩
  exact HashSeparation.message_tweakable_ne hpublic (withinBounds_structural parent)
    hmessage.symm

theorem not_deviating_of_targeted (walk : Walk)
    (hpublic : ¬ HashSeparation.Possible ((keyAt walk).seed, (keyAt walk).root))
    (input : Bytes) (htargeted : Targeted walk input) : ¬ Deviating walk input :=
  fun hdeviating => hdeviating (CombinedCharge.separated_of_not_possible walk.1.1.2.2 (keyAt walk)
    walk.1.2 hpublic withinBounds_structural input htargeted.1)

theorem not_deviating_randomizerInput (walk : Walk) (hgood : Target.GoodWalk walk)
    (seed : Digest) (message : Bytes) :
    ¬ Deviating walk (Hashing.randomizerInput walk.1.1.2.1 seed message) := by
  intro hdeviating
  apply hdeviating
  have hparse : parseInput walk.1.1.2.2 (Hashing.randomizerInput walk.1.1.2.1 seed message) =
      none := by
    rw [parseInput_none_iff]
    rintro ⟨parsed, hparsed⟩
    exact RandomizerGate.canonicalInput_ne_randomizerInput walk.1.1.2.2 walk.1.1.2.1 seed
      parsed.candidates parsed.parent message hgood.1 hparsed
  simp [CanonicalTarget.canonicalTarget, hparse]

/-! ## The honest cells, read at a later cache -/

/-- **Replaying the graph at any cache that extends the walk's gives the walk's cells.** -/
theorem replayCells_of_extends {walk : Walk} (hwalk : walk ∈ support WarmedGame.graphWalk)
    (final : QueryCache HashSpec)
    (hextends : ∀ (input : Bytes) (output : HashOutput), walk.2 input = some output →
      final input = some output) :
    HonestProbes.replayCells final walk.1.1.1 walk.1.1.2.2 = walk.1.2 := by
  obtain ⟨outputs, hcells, hcache⟩ := WarmedGame.mem_support_graphWalk hwalk
  rw [HonestProbes.replayCells, hcells]
  refine @Programming.value_eq_of_cache_agreement (replayQuery final) walk.1.1.2.2 walk.1.1.1
    outputs fun input output hentry => hash_replayQuery final input output
      (hextends input output ?_)
  rw [hcache, hcells]
  exact hentry

theorem not_deviating_canonical {walk : Walk} (hwalk : walk ∈ support WarmedGame.graphWalk)
    (final : QueryCache HashSpec)
    (hextends : ∀ (input : Bytes) (output : HashOutput), walk.2 input = some output →
      final input = some output) (parent : StructuralNode) :
    ¬ Deviating walk (canonicalInput walk.1.1.2.2
      (HonestProbes.replayCells final walk.1.1.1 walk.1.1.2.2) parent) := by
  rw [replayCells_of_extends hwalk final hextends]
  exact fun hdeviating => hdeviating (CanonicalTarget.canonicalTarget_canonical _ _ parent)

/-- The key a replayed key generation produces carries its own seeds. -/
theorem keygen_seeds (cache : QueryCache HashSpec) (secretSeed prfSeed publicSeed : Digest) :
    (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).1.prf = prfSeed ∧
      (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).1.seed = secretSeed ∧
      (@Scheme.keygenInternal Id Id.instMonad (replayQuery cache)
        secretSeed prfSeed publicSeed).1.publicKey.seed = publicSeed :=
  ⟨rfl, rfl, rfl⟩

/-! ## The fresh entries of the two classes, at the recorded tail -/

attribute [local irreducible] Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries RecordedTail.recordedAfterSeeds

set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The fresh faults and target-class entries are the record's and one digest per request.** -/
theorem freshMass_le_work_add_signed (adversary : Adversary) {walk : Walk}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support (RecordedTail.recordedTail adversary walk)) :
    freshMass (fun input => Deviating walk input ∨ Targeted walk input) walk.2 result.2 ≤
      ((result.1.1.1.counts.work + result.1.1.1.signed.length : Nat) : ℝ≥0∞) := by
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) :=
    hresult
  have hextends : ∀ (input : Bytes) (output : HashOutput), walk.2 input = some output →
      result.2 input = some output := fun input output hentry =>
    GrowthCharge.cache_value_persists _ walk.2 result.2 result.1 hrun input output hentry
  obtain ⟨keys, hkeys, hsource⟩ :=
    LateProvenance.provenance_recordedAfterSeeds adversary walk.1.1 walk.2 result hrun
  obtain ⟨hprf, hsecret, hpublicSeed⟩ : keys.1.prf = walk.1.1.2.1 ∧ keys.1.seed = walk.1.1.1 ∧
      keys.1.publicKey.seed = walk.1.1.2.2 := by
    rw [hkeys]
    exact keygen_seeds result.2 walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2
  let digests : List Bytes := result.1.1.1.signed.filterMap fun entry =>
    entry.1.frame.map fun framed =>
      Hashing.messageInput (HonestProbes.replayRandomizer result.2 keys.1 framed)
        keys.1.publicKey framed
  let holder : Finset Bytes := result.1.1.2.toFinset ∪ digests.toFinset
  have hcard : holder.card ≤ result.1.1.1.counts.work + result.1.1.1.signed.length := by
    show (result.1.1.2.toFinset ∪ digests.toFinset).card ≤ _
    have hrecord := RecordedTail.card_toFinset_le_count adversary hresult
    have hunion := Finset.card_union_le result.1.1.2.toFinset digests.toFinset
    have hdigests : digests.toFinset.card ≤ result.1.1.1.signed.length :=
      le_trans (List.toFinset_card_le _) (List.length_filterMap_le _ _)
    omega
  refine le_trans (freshMass_le_card _ walk.2 result.2 holder ?_) (by exact_mod_cast hcard)
  intro input hclass hnone hfinal
  -- A canonical input is in neither class.
  have hcanonical : ∀ parent : StructuralNode, input ≠ canonicalInput walk.1.1.2.2
      (HonestProbes.replayCells result.2 walk.1.1.1 walk.1.1.2.2) parent := by
    intro parent heq
    rcases hclass with hdeviating | htargeted
    · exact not_deviating_canonical hwalk result.2 hextends parent (heq ▸ hdeviating)
    · exact not_targeted_canonical walk hpublic _ _ parent (heq ▸ htargeted)
  rcases hsource input hnone hfinal with hrecord | hkeygen | ⟨entry, hentry, hmade⟩
  · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hrecord)
  · obtain ⟨parent, hparent⟩ := HonestProbes.probes_keygenInternal result.2 walk.1.1.1
      walk.1.1.2.1 walk.1.1.2.2 input hkeygen
    exact absurd hparent (hcanonical parent)
  · cases hframe : entry.1.frame with
    | none =>
      exact absurd (HonestProbes.probes_sign_none result.2 keys.1 entry.1 hframe (fun _ => False)
        input hmade.1) id
    | some framed =>
      rcases HonestProbes.probes_sign result.2 keys.1 entry.1 framed hframe input hmade.1 with
        ⟨parent, hparent⟩ | hrandomizer | hdigest
      · rw [hpublicSeed, hsecret] at hparent
        exact absurd hparent (hcanonical parent)
      · exfalso
        rw [hprf] at hrandomizer
        rcases hclass with hdeviating | htargeted
        · exact not_deviating_randomizerInput walk hgood _ framed (hrandomizer ▸ hdeviating)
        · exact htargeted.2 ⟨_, framed, hrandomizer⟩
      · refine Finset.mem_union_right _ (List.mem_toFinset.mpr ?_)
        refine List.mem_filterMap.mpr ⟨entry, hentry, ?_⟩
        rw [hframe, hdigest]
        rfl

/-! ## At the split tail -/

attribute [local irreducible] WarmedGame.afterSeeds

set_option maxHeartbeats 2000000 in
set_option linter.constructorNameAsVariable false in
open scoped Classical in
/-- **The fresh faults and the target record together are within the work and the requests**,
on every run of the split tail. -/
theorem fresh_add_right_le (adversary : Adversary) {walk : Walk}
    (hwalk : walk ∈ support WarmedGame.graphWalk) (hgood : Target.GoodWalk walk)
    (z : (((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) × Counts)
    (hz : z ∈ support (SplitTail.splitCarrierTail
      (CombinedCharge.IsMessageInput (keyAt walk)) QueryKind.hash QueryKind.verification
      keep127 adversary walk)) :
    freshMass (Deviating walk) walk.2 z.1.2.1 + (z.1.2.2.2.length : ℝ≥0∞) ≤
      ((z.1.1.1.1.counts.work + z.1.1.1.1.counts .signing : Nat) : ℝ≥0∞) := by
  have hpublic := AnswerSide.not_possible_generatedKey hwalk hgood.2
  -- The run, read at the recorded tail.
  have hcounted : ((z.1.1.1, z.2), z.1.2.1) ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (ClassGrowth.splitCost (CombinedCharge.IsMessageInput (keyAt walk))
        QueryKind.hash QueryKind.verification)
        (RecordedTail.recordedAfterSeeds adversary walk.1.1))).run walk.2) := by
    rw [← SplitCarrierTail.forget_splitCarrierTail _ _ _ keep127 adversary walk, support_map]
    exact ⟨z, hz, rfl⟩
  have hrecorded := ClassGrowth.mem_support_countAllHashes_of_splitCost _
    AnswerFired.hash_ne_verification _ walk.2 _ hcounted
  have hfresh := freshMass_le_work_add_signed adversary hwalk hgood _ hrecorded
  have htail := RecordedTail.mem_support_tail_of_recorded adversary hrecorded
  have hlength := SigningFaithful.signed_length_le_signing_tail adversary htail
  -- The target record, read at the carrier tail.
  have hcarrier : z.1 ∈ support (carrierTail keep127 adversary walk) := by
    rw [← SplitTail.map_splitCarrierTail _ AnswerFired.hash_ne_verification keep127 adversary
      walk, support_map]
    exact ⟨z, hz, rfl⟩
  obtain ⟨hcached, hnodup⟩ :=
    CarrierTailRecordings.recordFreshNodup_carrierTail keep127 adversary walk z.1 hcarrier
  have hclass := CarrierTailRecordings.recordClass_carrierTail keep127 Targeted
    targeted_of_keep127 adversary walk z.1 hcarrier
  have hright : ((z.1.2.2.2.map Prod.fst).length : ℝ≥0∞) ≤
      freshMass (Targeted walk) walk.2 z.1.2.1 := by
    refine length_le_freshMass _ _ _ _ hnodup fun input hinput => ?_
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hinput
    refine ⟨hclass entry hentry, ?_, hcached entry hentry⟩
    cases hwarm : walk.2 entry.1 with
    | none => rfl
    | some value =>
      obtain ⟨parent, hparent⟩ := WarmedCharges.walk_cache_canonical hwalk entry.1
        (by rw [hwarm]; simp)
      exact absurd (hparent ▸ hclass entry hentry) (not_targeted_canonical walk hpublic _ _ _)
  rw [List.length_map] at hright
  have hsum := freshMass_add (Deviating walk) (Targeted walk) walk.2 z.1.2.1
    fun input hdeviating htargeted =>
      not_deviating_of_targeted walk hpublic input htargeted hdeviating
  calc freshMass (Deviating walk) walk.2 z.1.2.1 + (z.1.2.2.2.length : ℝ≥0∞)
      ≤ freshMass (Deviating walk) walk.2 z.1.2.1 + freshMass (Targeted walk) walk.2 z.1.2.1 :=
        add_le_add le_rfl hright
    _ = freshMass (fun input => Deviating walk input ∨ Targeted walk input) walk.2 z.1.2.1 :=
        hsum
    _ ≤ ((z.1.1.1.1.counts.work + z.1.1.1.1.signed.length : Nat) : ℝ≥0∞) := hfresh
    _ ≤ ((z.1.1.1.1.counts.work + z.1.1.1.1.counts .signing : Nat) : ℝ≥0∞) := by
        exact_mod_cast Nat.add_le_add_left hlength _

end SlhDsaSecurity.BySourceAnswer
