/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.Scheme
import all Mathlib.Control.Monad.Writer

/-!
# Public observations around the actual private seed sampler

The private uniform sampler contributes no public cost, public query log or cache update.
Its continuation retains all actual public root work and the complete joint observation.
-/

public section
open OracleComp OracleSpec SLHDSA
open SLHDSA.Security
open SLHDSA.SHAKE128s
namespace SLHDSA.SHAKE128s.Bridge

/-- Charge only the public oracle when comparing the two actual seed-sampling orders. -/
@[expose] def publicOnlyCost {C : Type} [Zero C] (cost : SHAKE128s.Bytes → C) :
    (SHAKE128s.Game.World SHAKE128s.FIPS205.Answer).Domain → C
  | .inl _ => 0
  | .inr input => cost input

/-- The ideal sampler and cached public oracle retain keys, cost, full public log and cache. -/
@[expose] noncomputable def keygenObservation {Keys C : Type} [AddMonoid C]
    (cost : SHAKE128s.Bytes → C)
    (program : OracleComp (SHAKE128s.Game.World SHAKE128s.FIPS205.Answer) Keys)
    (cache : (SHAKE128s.Bytes →ₒ SHAKE128s.FIPS205.Answer).QueryCache) :
    ProbComp (((Keys × C) × QueryLog (SHAKE128s.Bytes →ₒ SHAKE128s.FIPS205.Answer)) ×
      (SHAKE128s.Bytes →ₒ SHAKE128s.FIPS205.Answer).QueryCache) :=
  let R := SHAKE128s.Bytes →ₒ SHAKE128s.FIPS205.Answer
  let handler := (unifFwdImpl R).liftTarget (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) +
    R.randomOracle.withLogging
  ((simulateQ (handler.withAddCost (publicOnlyCost cost)) program).runAdd).run.run cache


private abbrev R := SHAKE128s.Bytes →ₒ SHAKE128s.FIPS205.Answer
private abbrev ObservationM (C : Type) :=
  AddWriterT C (WriterT (QueryLog R) (StateT R.QueryCache ProbComp))

private instance : LawfulMonadLift (StateT R.QueryCache ProbComp)
    (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) where
  monadLift_pure a := by
    apply WriterT.ext
    change ((fun x => (x, [])) <$> (pure a : StateT R.QueryCache ProbComp _)) = _
    simp
  monadLift_bind ma f := by
    apply WriterT.ext
    change ((fun x => (x, [])) <$> (ma >>= f)) =
      (((fun x => (x, [])) <$> ma) >>= fun aw =>
        (fun bw => (bw.1, aw.2 ++ bw.2)) <$> ((fun x => (x, [])) <$> f aw.1))
    simp [map_bind, bind_map_left]

private instance {C : Type} [AddMonoid C] :
    LawfulMonadLift (WriterT (QueryLog R) (StateT R.QueryCache ProbComp)) (ObservationM C) where
  monadLift_pure _ := by apply WriterT.ext; simp
  monadLift_bind _ _ := by
    apply WriterT.ext
    simp [map_bind, bind_map_left]

private noncomputable def observationHandler {C : Type} [AddMonoid C] (cost : SHAKE128s.Bytes → C) :
    QueryImpl (Game.World FIPS205.Answer) (ObservationM C) :=
  (((unifFwdImpl R).liftTarget (WriterT (QueryLog R) (StateT R.QueryCache ProbComp))) +
    R.randomOracle.withLogging).withAddCost (publicOnlyCost cost)

private theorem observationHandler_private {C : Type} [AddMonoid C]
    (cost : SHAKE128s.Bytes → C) (t : unifSpec.Domain) :
    observationHandler cost (.inl t) =
      (((unifFwdImpl R).liftTarget (WriterT (QueryLog R) (StateT R.QueryCache ProbComp))).liftTarget
        (ObservationM C)) t := by
  simp only [observationHandler, QueryImpl.withAddCost_apply, publicOnlyCost,
    QueryImpl.add_apply_inl]
  have zeroTell : AddWriterT.addTell (M := WriterT (QueryLog R) (StateT R.QueryCache ProbComp))
      (0 : C) = pure PUnit.unit := by
    apply WriterT.ext
    rfl
  rw [zeroTell, pure_bind]
  rfl

private theorem simulate_private {C α : Type} [AddMonoid C]
    (cost : SHAKE128s.Bytes → C) (seeds : ProbComp α) :
    simulateQ (observationHandler cost) (liftM seeds : OracleComp (Game.World FIPS205.Answer) α) =
      (liftM (liftM (simulateQ (unifFwdImpl R) seeds) :
        WriterT (QueryLog R) (StateT R.QueryCache ProbComp) α) : ObservationM C α) := by
  rw [← liftComp_eq_liftM,
    QueryImpl.simulateQ_liftComp_left_eq_of_apply _ _ (observationHandler_private cost),
    simulateQ_liftTarget, simulateQ_liftTarget]

/-- Sampling private seeds before public work preserves the full initial public observation. -/
theorem keygenObservation_private_bind {C α β : Type} [AddMonoid C]
    (cost : SHAKE128s.Bytes → C) (seeds : ProbComp α)
    (next : α → OracleComp (Game.World FIPS205.Answer) β)
    (cache : (SHAKE128s.Bytes →ₒ FIPS205.Answer).QueryCache) :
    keygenObservation cost
      ((liftM seeds : OracleComp (Game.World FIPS205.Answer) α) >>= next) cache =
      seeds >>= fun value => keygenObservation cost (next value) cache := by
  change ((simulateQ (observationHandler cost) (liftM seeds >>= next)).runAdd).run.run cache = _
  rw [simulateQ_bind, simulate_private]
  simp [keygenObservation, observationHandler, AddWriterT.runAdd_bind, WriterT.run_bind,
    StateT.run_bind, AddWriterT.runAdd_liftM, unifFwdImpl.simulateQ_run, Prod.map, id_eq]

/-- The actual independent seed law transports the complete joint public observation. -/
theorem keygenObservation_keygen_eq : (∀ {C β : Type} [AddMonoid C] (cost : Bytes → C)
  (cache : (Bytes →ₒ FIPS205.Answer).QueryCache)
  (next : ((((SecretKeyCore FIPS205.core × PublicKeyCore FIPS205.core) × C) ×
    QueryLog (Bytes →ₒ FIPS205.Answer)) × (Bytes →ₒ FIPS205.Answer).QueryCache) → ProbComp β),
  (keygenObservation cost
    (Prod.map Bridge.skMap Bridge.pkMap <$>
      simulateQ (Bridge.relabel Bridge.answerEquiv)
        (Scheme.keygen : OracleComp OracleWorld (SecretKey × PublicKey))) cache >>= next) =ᵈ
  (keygenObservation cost FIPS205.scheme.keygen cache >>= next)) := by
  intro C β inst cost cache next
  rw [Bridge.simulateQ_relabel_keygen, map_bind, Bridge.scheme_keygen]
  simp_rw [Bridge.keygenInternal_eq]
  rw [keygenObservation_private_bind, keygenObservation_private_bind]
  simp only [bind_assoc]
  let continuation (t : FIPS205.core.PkSeed × FIPS205.core.SkSeed × FIPS205.core.SkPrf) :
      ProbComp β :=
    keygenObservation cost
      ((fun keys => (keys.2, keys.1)) <$> simulateQ (encImpl FIPS205.params) (do
        let root ← GeneralScheme.keygenInternalWithSecretM FIPS205.core
          (oracleSecret FIPS205.core (Equiv.refl _) t.1 t.2.1) t.1
        pure ((⟨t.1, root⟩ : PublicKeyCore FIPS205.core),
          (⟨t.2.1, t.2.2, t.1, root⟩ : SecretKeyCore FIPS205.core)))) cache >>= next
  change (Bridge.paperSeeds >>= fun t => continuation (Bridge.seedMap t)) =ᵈ
    (Bridge.fipsSeeds >>= continuation)
  simpa only [bind_map_left] using Bridge.map_seedMap_paperSeeds.bind_left continuation


end SLHDSA.SHAKE128s.Bridge
