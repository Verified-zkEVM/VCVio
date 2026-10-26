/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Component
public import HashSig.SLHDSA.SHAKE128s.Statement.Game.QueryBudget

/-!
# Complete source counts and reply logs of the adversary phase

The shared counted phase recovers the original phase counters, chronological signing log and
actual total hash count from every initial signing prefix. Actual signer traffic contributes
to the total hash count, while every returned reply, including rejection, remains in the log.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment

private theorem countAllHashes_pure {Output α : Type} (value : α) :
    Game.countAllHashes (pure value : OracleComp (Game.World Output) α) = pure (value, 0) := by
  simp [Game.countAllHashes]

private theorem countAllHashes_bind_exact {Output α β : Type}
    (body : OracleComp (Game.World Output) α)
    (next : α → OracleComp (Game.World Output) β) :
    Game.countAllHashes (body >>= next) = (do
      let first ← Game.countAllHashes body
      let last ← Game.countAllHashes (next first.1)
      return (last.1, first.2 + last.2)) := by
  simp [Game.countAllHashes, WriterT.run_bind, bind_map_left, Functor.map_map]

private theorem countAllHashes_query {Output : Type} (input : (Game.World Output).Domain) :
    Game.countAllHashes (query input : OracleComp (Game.World Output) _) =
      (fun answer => (answer, Game.hashCost input)) <$>
        (query input : OracleComp (Game.World Output) _) := by
  simp [Game.countAllHashes, addCostOracle, QueryImpl.withAddCost_apply]

private theorem phaseCounts_add (left right : SourceCounts) :
    phaseCounts (left + right) =
      phaseCounts left + phaseCounts right := by
  funext kind
  cases kind <;> rfl

private theorem laterHashes_add (left right : SourceCounts) :
    laterHashes (left + right) =
      laterHashes left + laterHashes right := by
  simp only [laterHashes, Pi.add_apply]
  omega

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

private theorem phaseCounts_single (kind : Unforgeability.QueryKind) (amount : Nat) :
    phaseCounts (Pi.single kind amount) =
      match kind with
      | .sign => Game.Counts.single .signing amount
      | .hash => Game.Counts.single .hash amount
      | .verifier => Game.Counts.single .verification amount
      | .keygen | .signer => 0 := by
  cases kind <;> funext index <;> cases index <;>
    simp [phaseCounts, Game.Counts.single]

private theorem laterHashes_single (kind : Unforgeability.QueryKind) (amount : Nat) :
    laterHashes (Pi.single kind amount) =
      match kind with
      | .hash | .signer | .verifier => amount
      | .keygen | .sign => 0 := by
  cases kind <;> simp [laterHashes]

/-- The full arbitrary-prefix phase observation retains every reply and actual hash charge. -/
theorem countAllHashes_runPhase {Output PK SK α : Type}
    (scheme : Game.ExternalScheme Output PK SK) (pk : PK) (sk : SK)
    (body : OracleComp (Game.World Output + Game.SigningSpec) α)
    (oldLog : Game.SigningLog) :
    Game.countAllHashes (Game.runPhase scheme sk body oldLog) =
      (fun result => (((result.1.1, phaseCounts result.2), oldLog ++ result.1.2),
        laterHashes result.2)) <$>
        (SigningView.countedPhase sourcePolicy (externalView scheme) pk sk body).runAdd := by
  induction body using OracleComp.inductionOn generalizing oldLog with
  | pure value =>
      have zeroCounts : phaseCounts (0 : SourceCounts) = 0 := by
        funext index
        cases index <;> rfl
      simp [Game.runPhase_pure, countAllHashes_pure, SigningView.countedPhase,
        laterHashes, zeroCounts]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [Game.runPhase_query_bind_world]
          simp only [countAllHashes_bind_exact, countAllHashes_pure, countAllHashes_query,
            pure_bind, bind_map_left]
          simp only [SigningView.countedPhase_bind, AddWriterT.runAdd_bind,
            AddWriterT.runAdd_pure, countedPhase_world, map_bind, bind_map_left, map_pure]
          simp_rw [ih]
          simp only [bind_map_left, Prod.map_apply,
            id_eq, add_zero, List.nil_append, bind_assoc, pure_bind]
          apply bind_congr
          intro first
          apply bind_congr
          intro last
          simp [phaseCounts_add, laterHashes_add, phaseCounts_single, laterHashes_single]
      | inr request =>
          rw [Game.runPhase_query_bind_sign]
          simp only [countAllHashes_bind_exact, countAllHashes_pure, pure_bind]
          simp only [SigningView.countedPhase_bind, AddWriterT.runAdd_bind,
            AddWriterT.runAdd_pure, countedPhase_sign, map_bind, bind_map_left, map_pure]
          simp_rw [ih]
          simp only [bind_map_left, Prod.map_apply,
            id_eq, add_zero, bind_assoc, pure_bind]
          apply bind_congr
          intro first
          apply bind_congr
          intro last
          simp [phaseCounts_add, laterHashes_add, phaseCounts_single, laterHashes_single,
            List.append_assoc]

end SLHDSA.SHAKE128s.Bridge.SharedExperiment
