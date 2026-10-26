/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Phase
import HashSig.SLHDSA.SHAKE128s.Bridge.Transfer
import VCVio.OracleComp.Support

/-!
# Full outcomes and recorded hash counts

The shared counted experiment retains the original outcome and actual keygen and later hash
counts as one free-oracle program. Phase-coordinate invariants are derived from the actual
policy and returned joint results, including every optional signing reply.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

private theorem countedPhase_world {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK)
    (input : (Game.World Output).Domain) :
    (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk
      (liftM ((Game.World Output + Game.SigningSpec).query (.inl input)))).runAdd =
      (fun answer => ((answer, []), Pi.single .hash (Game.hashCost input))) <$>
        (query input : OracleComp (Game.World Output) _) := by
  simp [SigningView.countedPhase, SigningView.countedHandler, sourcePolicy,
    sourceKind, QueryImpl.withAddCost_apply]

private theorem countedPhase_sign {Output PK SK : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK) (request : Message) :
    (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk
      (liftM ((Game.World Output + Game.SigningSpec).query (.inr request)))).runAdd =
      (fun result => ((result.1, [⟨request, result.1⟩]),
        Pi.single .sign 1 + Pi.single .signer result.2)) <$>
        Game.countAllHashes (scheme.sign sk request) := by
  rw [SigningView.countedPhase_signingQuery]
  simp only [externalView]
  simp only [AddWriterT.runAdd_bind, AddWriterT.runAdd_pure,
    sourcePolicy]
  rw [costed_eq_countAllHashes .signer]
  simp [sourceKind]

private theorem countedPhase_step_world {Output PK SK α : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK)
    (input : (Game.World Output).Domain)
    (next : (Game.World Output).Range input →
      OracleComp (Game.World Output + Game.SigningSpec) α) :
    (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk
      (liftM ((Game.World Output + Game.SigningSpec).query (.inl input)) >>= next)).runAdd = do
      let answer ← query input
      let result ← (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk
        (next answer)).runAdd
      return (result.1, Pi.single .hash (Game.hashCost input) + result.2) := by
  rw [SigningView.countedPhase_bind]
  simp only [AddWriterT.runAdd_bind, AddWriterT.runAdd_pure, countedPhase_world,
    map_bind, bind_map_left, map_pure]
  simp [Prod.map]

private theorem countedPhase_step_sign {Output PK SK α : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK) (request : Message)
    (next : Option Bytes → OracleComp (Game.World Output + Game.SigningSpec) α) :
    (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk
      (liftM ((Game.World Output + Game.SigningSpec).query (.inr request)) >>= next)).runAdd = do
      let signed ← Game.countAllHashes (scheme.sign sk request)
      let result ← (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk
        (next signed.1)).runAdd
      return ((result.1.1, [⟨request, signed.1⟩] ++ result.1.2),
        Pi.single .sign 1 + Pi.single .signer signed.2 + result.2) := by
  rw [SigningView.countedPhase_bind]
  simp only [AddWriterT.runAdd_bind, AddWriterT.runAdd_pure, countedPhase_sign,
    map_bind, bind_map_left, map_pure]
  simp

/-- Every actual phase result has zero keygen and final-verifier charge. -/
private theorem countedPhase_unused {Output PK SK α : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK)
    (body : OracleComp (Game.World Output + Game.SigningSpec) α)
    {result : (α × Game.SigningLog) × SourceCounts}
    (reachable : result ∈ support
      (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk body).runAdd) :
    result.2 .keygen = 0 ∧ result.2 .verifier = 0 := by
  induction body using OracleComp.inductionOn generalizing result with
  | pure value =>
      have equal : result = ((value, []), 0) := by
        simpa [SigningView.countedPhase] using reachable
      subst result
      exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [countedPhase_step_world] at reachable
          obtain ⟨answer, _, reachable⟩ := mem_support_bind_peel _ _ reachable
          obtain ⟨rest, hrest, reachable⟩ := mem_support_bind_peel _ _ reachable
          have equal := eq_of_mem_support_pure _ reachable
          subst result
          simpa using ih answer hrest
      | inr request =>
          rw [countedPhase_step_sign] at reachable
          obtain ⟨signed, _, reachable⟩ := mem_support_bind_peel _ _ reachable
          obtain ⟨rest, hrest, reachable⟩ := mem_support_bind_peel _ _ reachable
          have equal := eq_of_mem_support_pure _ reachable
          subst result
          simpa using ih signed.1 hrest

private theorem count_pure {Output α : Type} (value : α) :
    Game.countAllHashes (pure value : OracleComp (Game.World Output) α) = pure (value, 0) := by
  simp [Game.countAllHashes]

private theorem count_bind {Output α β : Type} (body : OracleComp (Game.World Output) α)
    (next : α → OracleComp (Game.World Output) β) :
    Game.countAllHashes (body >>= next) = (do
      let first ← Game.countAllHashes body
      let last ← Game.countAllHashes (next first.1)
      return (last.1, first.2 + last.2)) := by
  simp [Game.countAllHashes, WriterT.run_bind, bind_map_left, Functor.map_map]

private theorem countedPhase_map {Output PK SK α β : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK) (f : α → β)
    (body : OracleComp (Game.World Output + Game.SigningSpec) α) :
    (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk (f <$> body)).runAdd =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk body).runAdd := by
  simp only [SigningView.countedPhase, simulateQ_map, WriterT.run_map',
    AddWriterT.runAdd_map]
  rfl

private theorem counts_total (keygen verifier : Nat) (cost : SourceCounts) :
    phaseCounts (Pi.single .keygen keygen + (cost + Pi.single .verifier verifier)) =
      phaseCounts cost + Game.Counts.single .verification verifier := by
  funext kind
  cases kind <;> simp [phaseCounts, Game.Counts.single]

private theorem later_total (keygen verifier : Nat) (cost : SourceCounts) :
    laterHashes (Pi.single .keygen keygen + (cost + Pi.single .verifier verifier)) =
      laterHashes cost + verifier := by
  simp [laterHashes, Nat.add_assoc]

/-- The complete original outcome and both actual hash counters agree before interpretation. -/
theorem recordedProgram {Output PK SK : Type} (scheme : Game.ExternalScheme Output PK SK)
    (adversary : Game.Adversary Output PK) :
    (do
      let (keys, keygenHashes) ← Game.countAllHashes scheme.keygen
      let (outcome, laterCount) ← Game.countAllHashes (Game.afterKeygen scheme adversary keys)
      return (outcome, keygenHashes, laterCount)) =
      (fun observed => (legacyOutcome observed, observed.cost .keygen,
        laterHashes observed.cost)) <$> canonicalExperiment scheme adversary := by
  have keygenEq : (externalView scheme).keygen = Prod.swap <$> scheme.keygen := rfl
  have verifyEq : ∀ pk request signature,
      (externalView scheme).verify pk request signature = scheme.verify pk request signature := by
    intro pk request signature
    rfl
  have phaseEq (sk : SK) (pk : PK) :=
    countAllHashes_runPhase scheme pk sk (adversary.main pk) []
  simp only [canonicalExperiment, legacyOutcome]
  simp only [SigningView.countedExperiment, AddWriterT.runAdd_bind, AddWriterT.runAdd_pure,
    externalMain]
  simp only [keygenEq, verifyEq, costed_eq_countAllHashes, sourceKind,
    Bridge.countAllHashes_map, countedPhase_map]
  simp only [map_bind, bind_map_left, Functor.map_map, map_pure]
  simp_rw [Game.afterKeygen_eq_runPhase, count_bind, count_pure]
  simp_rw [phaseEq, countAllHashes_countQueries_verification]
  simp only [bind_map_left, pure_bind, bind_assoc, Prod.map_apply, id_eq,
    add_zero, List.nil_append]
  apply bind_congr
  intro keygen
  apply OracleComp.bind_congr_of_forall_mem_support
  intro phase reachable
  have unused := countedPhase_unused scheme keygen.1.2 keygen.1.1
    (adversary.main keygen.1.2) reachable
  apply bind_congr
  intro verifier
  simp [counts_total, later_total, unused.1]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
