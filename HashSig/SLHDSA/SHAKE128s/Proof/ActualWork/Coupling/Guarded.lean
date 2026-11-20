/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
public import HashSig.SLHDSA.Security.SeedCoupling
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint

/-! # Joint cache consistency of the guarded SHAKE-128s experiment -/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

/-- The secret-key seed and the message PRF key used to resolve private derivations. -/
abbrev Secret := FIPS205.core.SkSeed × FIPS205.core.SkPrf
/-- The marked experiment output with its budget state, raw query cache and phase metadata. -/
abbrev Value := (((Full × (PUnit × Paid)) × Raw.QueryCache) × Meta)
/-- The two public keys and optional forgery outcome, together with the raw cache, metadata and
budget state. -/
abbrev Observation := (PK × PK) × Option RawOutcome × Raw.QueryCache × Meta × Paid

/-- A guarded observation censors only the signing-experiment output after an abort. -/
def observe (val : Value) : Observation :=
  let full := val.1.1.1
  let paid := val.1.1.2.2
  (full.1, if paid.2 then none else some full.2, val.1.2, val.2, paid)

/-- Run the fixed-seed source with the budget guard, routing raw requests and observing phase
markers. -/
noncomputable abbrev freeProgram (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat) : OracleComp (deriveSpec FIPS205.core) Value :=
  letI : MonadLiftT (OracleComp DCommon) (StateT PUnit (OracleComp DCommon)) :=
    ⟨fun action => StateT.lift action⟩
  let forwarder := (QueryImpl.id' DCommon).liftTarget (StateT PUnit (OracleComp DCommon))
  let fixedGuarded := (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : DNative.Domain => (0, 0)) (policy reserve s))
    forwarder (deriveFallback s)) (fixedSource s adv)).run (PUnit.unit, ((0, 0), false))
  (simulateQ (observeD s trackRaw) ((simulateQ (routeD s) fixedGuarded).run ∅)).run (0, .keygen)

/-- Observe the guarded experiment on the labelled graph interface with the supplied fallback
answers. -/
noncomputable abbrev labProgram (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) : OracleComp Lab Value :=
  letI : MonadLiftT (OracleComp Lab) (StateT Meta (OracleComp Lab)) :=
    ⟨fun action => StateT.lift action⟩
  let observer : QueryImpl (Lab + O) (StateT Meta (OracleComp Lab)) :=
    QueryImpl.add ((QueryImpl.id' Lab).liftTarget (StateT Meta (OracleComp Lab)))
      (fun event => StateT.mk fun metadata => pure (PUnit.unit,
        aux (spec := Lab) (metadataCost trackRaw s)
          (.inr event) PUnit.unit PUnit.unit PUnit.unit metadata))
  (simulateQ observer (guardedRoutedSource s adv reserve caps fallback)).run (0, .keygen)

/-- The two eager runs preserve the entire clipped observation together with their graph state. -/
theorem eager_joint (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (event : Observation → LabState FIPS205.core → Prop) :
    Pr{let r ← (simulateQ (slhGraph FIPS205.core s).eagerImpl
      (liftComp (freeProgram s adv reserve trackRaw caps) Lab)).run (∅, ∅)}[
      event (observe r.1) r.2] =
    Pr{let r ← (simulateQ (slhGraph FIPS205.core s).eagerImpl
      (labProgram s adv reserve trackRaw caps fallback)).run (∅, ∅)}[event (observe r.1) r.2] := by
  let flattened := fun r : (PK × PK) × Option RawOutcome × Raw.QueryCache × Meta × Paid ×
      LabState FIPS205.core =>
    event (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1) r.2.2.2.2.2
  have stage := guarded_eager_lab_stage s adv reserve trackRaw caps fallback
  dsimp only at stage
  have result := stage.prEvent_eq flattened
  rw [← Guarded.observe_eager_square s trackRaw (guardedRoutedSource s adv reserve caps fallback)
    (0, .keygen) (∅, ∅)] at result
  simpa only [observe, labProgram, freeProgram, flattened, prEvent_map, Functor.map_map,
    Guarded.observeLab, Function.comp_def] using result

/-- Every event of the real fixed-seed handler's jointly retained output and typed cache
transports to a deferred marked execution and its end fill, up to a hidden-input hit or conflict.
The sampling law of the fresh private seed is arbitrary. -/
theorem real_free_le_filled (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input)
    (seeds : ProbComp Secret) (event : Secret → Observation → H.QueryCache → Prop) :
    let E := secretEncoding FIPS205.core (Equiv.refl _) s
    let G := slhGraph FIPS205.core s
    Pr{let secret ← seeds
       let r ← (simulateQ (E.realImpl secret) (freeProgram s adv reserve trackRaw caps)).run ∅}[
      event secret (observe r.1) r.2] ≤
      Pr{let r ← G.deferredFillDraw seeds (labProgram s adv reserve trackRaw caps fallback)}[
        let split := G.toSplitCache r.2.1
        event r.2.2 (observe r.1.1) (E.merge r.2.2 split) ∨
        (∃ x, (split.1 (E.enc r.2.2 x)).isSome) ∨ G.Conflict r.2.1] := by
  intro E G
  let free := freeProgram s adv reserve trackRaw caps
  let lab := labProgram s adv reserve trackRaw caps fallback
  let filled : ProbComp (Value × LabState FIPS205.core) := do
    let r ← (simulateQ G.deferredImpl lab).run ((∅, ∅), [])
    let graph ← RelabelState.endFill r.2
    return (r.1, graph)
  let ideal := fun secret obs graph =>
    let split := G.toSplitCache graph
    event secret obs (E.merge secret split) ∨
      (∃ x, (split.1 (E.enc secret x)).isSome) ∨ G.Conflict graph
  have fixed (secret : Secret) :
      Pr{let r ← (simulateQ (E.realImpl secret) free).run ∅}[event secret (observe r.1) r.2] ≤
      Pr{let r ← filled}[ideal secret (observe r.1) r.2] := by
    have h := E.prEvent_realImpl_le_or secret free (fun r => event secret (observe r.1) r.2)
    have g := G.prEvent_idealImpl_le_eagerImpl_liftComp free (fun r =>
      event secret (observe r.1) (E.merge secret r.2) ∨ ∃ x, (r.2.1 (E.enc secret x)).isSome)
    have eager := eager_joint s adv reserve trackRaw caps fallback (ideal secret)
    have lhs : Pr{let r ← (simulateQ (E.realImpl secret) free).run ∅}[
          event secret (observe r.1) r.2] ≤
        Pr{let r ← (simulateQ G.eagerImpl lab).run (∅, ∅)}[ideal secret (observe r.1) r.2] := by
      rw [← eager]
      simpa only [ideal, or_assoc] using h.trans g
    have defer := G.prEvent_eagerImpl_le_deferredImpl_empty lab
      (fun r => ideal secret (observe r.1) r.2)
    exact lhs.trans (defer.trans_eq (by
      simp only [filled, ideal, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def,
        or_assoc, or_self]))
  have lifted := prEvent_bind_mono_of_support seeds _ _ (fun secret _ => fixed secret)
  have swap := prEvent_bind_map_swap seeds filled (fun secret r => ideal secret (observe r.1) r.2)
  refine le_trans lifted ?_
  rw [swap]
  simp only [CanonicalGraph.deferredFillDraw, filled, ideal, lab, prEvent_norm, bind_assoc]
  exact le_rfl

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
