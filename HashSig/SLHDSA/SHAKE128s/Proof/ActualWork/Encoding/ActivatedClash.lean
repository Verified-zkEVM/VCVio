/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Graph
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.Graph
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Encoding.EndFill
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw

/-! # Activation of encoding clashes on the guarded cache -/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

/-- A guarded result with the deferred graph state, touched cells, filled graph state and sampled
secret. -/
abbrev Filled := (Value × LabState FIPS205.core × List (DeriveQuery FIPS205.core ⊕
  NodeKey FIPS205.core)) × LabState FIPS205.core × Secret

/-- Both observers record the same metadata for each native query or source marker. -/
theorem labProgram_eq_native (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    labProgram s adv reserve true caps fallback =
      Native.deferredProgram s adv reserve caps fallback := by
  let f := fun event : Ev => StateT.mk fun metadata : Meta =>
    (pure (PUnit.unit, aux (spec := Lab) (metadataCost true s)
      (.inr event) PUnit.unit PUnit.unit PUnit.unit metadata) : OracleComp Lab (PUnit × Meta))
  let g := fun event : Ev => StateT.mk fun metadata : Meta =>
    (pure (PUnit.unit, match event with
      | .ambient phase input => (metadata.1 + metadataCost true s (.ambient phase input), phase)
      | .signingAttempt request => (metadata.1 + metadataCost true s (.signingAttempt request),
          .signer)) : OracleComp Lab (PUnit × Meta))
  have same : f = g := by funext event; cases event <;> rfl
  unfold labProgram Native.deferredProgram
  dsimp only
  change (simulateQ (QueryImpl.add _ f) _).run _ = (simulateQ (QueryImpl.add _ g) _).run _
  rw [same]

/-- Every actual byte-encoding clash at the end fill lies in an activated key event or the
weakness of the initially generated key, including branches on which the guard aborts. -/
theorem activated_clash (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    let G := slhGraph FIPS205.core s
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let program := labProgram s adv reserve true caps fallback
    ∀ r ∈ support (G.deferredFillDraw ($ᵗ Secret) program),
      (encoding s).Clash (E.merge r.2.2 (G.toSplitCache r.2.1)) →
      (signingActive r.1.1 ∧
        (HmsgAtPrfKey id r.2.2.2 r.2.1.1 ∨ r.2.2.2 = s)) ∨
        IsWeakKey FIPS205.params r.1.1.1.1.1.1.1 := by
  intro G E program r member clash
  rw [CanonicalGraph.deferredFillDraw] at member
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨pre, hp, filled, hf, secret, _, rfl⟩ := member
  have marginal := Native.native_deferred_marginal s adv reserve caps fallback 0 0
  dsimp only at marginal
  have sameProgram : program = Native.deferredProgram s adv reserve caps fallback :=
    labProgram_eq_native s adv reserve caps fallback
  rw [sameProgram] at hp
  rw [← support_eq_of_evalDistEq marginal, support_map] at hp
  obtain ⟨block, hb, rfl⟩ := hp
  have ht := (NoticingTape.mem_support_blockRunOf (Native.nativeRun s adv reserve caps fallback)
    0 0 block hb).2.2
  have pub := Native.native_public_provenance s adv reserve caps fallback
    block.1.1 block.1.2 block.2 ht
  have priv := Native.native_private_provenance s adv reserve caps fallback
    block.1.1 block.1.2 block.2 ht
  have result := FIPS205.activated_clash_of_endFill s _ _ _ _ _ _
    pub.1 pub.2 priv.1 priv.2 hf clash
  have same := RelabelState.fst_eq_of_mem_support_endFill hf
  rw [same]
  exact result.imp_left And.symm

/-- The model-transport event is bounded by the remaining winning or weak-key branches plus
a single charge on the deferred execution. Branches already paid by the charged hazards can be
excluded from the remaining probability. -/
theorem filled_le_remaining_add_charge (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    let G := slhGraph FIPS205.core s
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let nk := slhNodeKeys FIPS205.core s
    let program := labProgram s adv reserve true caps fallback
    let law := G.deferredFillDraw ($ᵗ Secret) program
    let event := fun r : Filled =>
      ∃ out, (observe r.1.1).2.1 = some out ∧ SigningView.Wins id out
    let charged := fun r : Filled =>
      (G.Conflict r.2.1 ∨ nk.TCHazard r.2.1) ∨ keyHazard s r.1.1 r.2.2 r.2.1
    Pr{let r ← law}[
      (event r ∨ (encoding s).Clash (E.merge r.2.2 (G.toSplitCache r.2.1))) ∨
      (∃ x, ((G.toSplitCache r.2.1).1 (E.enc r.2.2 x)).isSome) ∨ G.Conflict r.2.1] ≤
      Pr{let r ← law}[(event r ∨ IsWeakKey FIPS205.params r.1.1.1.1.1.1.1) ∧ ¬charged r] +
        ∫⁻ charge, charge ∂𝒟[(fun r =>
          2 * ((nk.keyEntries r.2.1.1).encard : ℝ≥0∞) / Nat.card FIPS205.core.Y +
            keyCharge s r.1 r.2.1.1) <$>
          (simulateQ G.deferredImpl program).run ((∅, ∅), [])] := by
  classical
  intro G E nk program law event charged
  let remaining := fun r => (event r ∨ IsWeakKey FIPS205.params r.1.1.1.1.1.1.1) ∧ ¬charged r
  apply le_trans (prEvent_mono_of_support law _ (fun r => remaining r ∨ charged r) ?_)
  · exact (prEvent_or_le law remaining charged).trans (add_le_add le_rfl
      (joint_hazards_le_expected_charge s adv reserve true caps fallback))
  · intro r member hit
    by_cases paid : charged r
    · exact Or.inr paid
    apply Or.inl
    refine ⟨?_, paid⟩
    rcases hit with (win | clash) | hidden | conflict
    · exact Or.inl win
    · rcases activated_clash s adv reserve caps fallback r member clash with key | weak
      · exact (paid (Or.inr (Or.inr key))).elim
      · exact Or.inr weak
    · exact (paid (Or.inr (Or.inl hidden))).elim
    · exact (paid (.inl (.inl conflict))).elim

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
