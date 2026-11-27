/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Joint
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-! # Physical and typed observations at the FIPS key sampler -/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- The physical key pair and the complete outcome of the signing experiment. -/
abbrev FullActual := (PK × SecretKeyCore FIPS205.core) × RawOutcome
/-- The physical experiment output, budget state, marker cost and final signing phase. -/
abbrev Observed := (FullActual × Paid) × Meta

/-- Apply the work and signing-attempt caps to a source, starting with zero cost and a clear abort
flag. -/
noncomputable abbrev guarded {α : Type} (s : FIPS205.core.PkSeed) (reserve : Bool)
    (caps : Nat × Nat) (fallback : (i : Common.Domain) → Common.Range i)
    (source : OracleComp Common α) :=
  letI : MonadLiftT (OracleComp Common) (StateT PUnit (OracleComp Common)) :=
    ⟨fun action => StateT.lift action⟩
  (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve s))
    ((QueryImpl.id' Common).liftTarget (StateT PUnit (OracleComp Common)))
    fallback) source).run (PUnit.unit, ((0, 0), false))

/-- Record the marker cost and current signing phase while running the guarded source on native
queries. -/
noncomputable abbrev observedProgram {α : Type} (s : FIPS205.core.PkSeed) (reserve : Bool)
    (caps : Nat × Nat) (fallback : (i : Common.Domain) → Common.Range i)
    (charge : Ev → Nat) (source : OracleComp Common α) : OracleComp Native ((α × Paid) × Meta) :=
  let observer :=
    ((eraseObsImpl (Ev := Ev) (QueryImpl.id' Native)).liftTarget
      (StateT PUnit (OracleComp Native))).extendState (aux (spec := Native) charge)
  (fun r => ((r.1.1, r.1.2.2), r.2.2)) <$>
    (simulateQ observer (guarded s reserve caps fallback source)).run (PUnit.unit, (0, .keygen))

/-- Run the guard and the phase observer with a supplied native handler and its initial cache. -/
noncomputable abbrev observedRun {Cache α : Type}
    (handler : QueryImpl Native (StateT Cache ProbComp)) (initial : Cache)
    (s : FIPS205.core.PkSeed) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (i : Common.Domain) → Common.Range i) (charge : Ev → Nat)
    (source : OracleComp Common α) :=
  (simulateQ (QueryImpl.guardQueryBudget caps
    (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve s))
    ((eraseObsImpl (Ev := Ev) handler).extendState (aux (spec := Native) charge))
    fallback) source).run ((initial, (0, .keygen)), ((0, 0), false))

/-- Moving the guard and observer into the program preserves its output and the whole cache. -/
theorem observed_run {Cache α : Type} (handler : QueryImpl Native (StateT Cache ProbComp))
    (initial : Cache) (s : FIPS205.core.PkSeed) (reserve : Bool) (caps : Nat × Nat)
    (fallback : (i : Common.Domain) → Common.Range i) (charge : Ev → Nat)
    (source : OracleComp Common α) :
    (fun r => (((r.1, r.2.2), r.2.1.2), r.2.1.1)) <$>
      observedRun handler initial s reserve caps fallback charge source =
    (simulateQ handler (observedProgram s reserve caps fallback charge source)).run initial := by
  let observer :=
    ((eraseObsImpl (Ev := Ev) (QueryImpl.id' Native)).liftTarget
      (StateT PUnit (OracleComp Native))).extendState (aux (spec := Native) charge)
  let observed := (eraseObsImpl (Ev := Ev) handler).extendState (aux (spec := Native) charge)
  let whole := (handler.mapStateTBase observer).flattenStateT
  let project := fun state : (PUnit × Meta) × Cache => (state.2, state.1.2)
  have step (input : Common.Domain) (state : (PUnit × Meta) × Cache) :
      Prod.map id project <$> (whole input).run state =
        (observed input).run (project state) := by
    rcases state with ⟨⟨⟨⟩, metadata⟩, cache⟩
    rcases input with native | event
    · simp [whole, observer, observed, project, QueryImpl.flattenStateT_mapStateTBase_apply_run,
        QueryImpl.extendState_apply, eraseObsImpl_inl, QueryImpl.id'_apply,
        aux, Functor.map_map]
    · cases event <;> simp [whole, observer, observed, project,
        QueryImpl.flattenStateT_mapStateTBase_apply_run, QueryImpl.extendState_apply,
        eraseObsImpl_inr, aux]
  have obs := map_run_simulateQ_eq_of_query_map_eq whole observed project step
    (guarded s reserve caps fallback source) ((PUnit.unit, (0, .keygen)), initial)
  have gr := QueryImpl.map_run_simulateQ_guardQueryBudget_free_eq caps
    (Sum.elim (fun _ : Native.Domain => (0, 0)) (policy reserve s))
    observed fallback source (initial, (0, .keygen)) (0, 0) false
  change (fun r => (r.1.1, (r.2, r.1.2.2))) <$>
    (simulateQ observed (guarded s reserve caps fallback source)).run (initial, (0, .keygen)) =
      observedRun handler initial s reserve caps fallback charge source at gr
  rw [← gr, ← obs]
  simp only [observedProgram, simulateQ_map, StateT.run_map]
  conv_rhs => rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [whole, observer, project, Functor.map_map, Prod.map, id_eq]

/-- The uniformly sampled original FIPS public key seed and internally sampled signing key are
retained across the physical-byte to typed-encoded comparison, including its terminal cache. -/
theorem sampled_physical_le_fill_or_clash (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat)
    (fallback : (s : FIPS205.core.PkSeed) → (i : Common.Domain) → Common.Range i)
    (event : FIPS205.core.PkSeed → Observed → Raw.QueryCache → Prop) :
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← observedRun (Raw.romImpl ∘ₛ (encoding s).encodeImpl) ∅ s reserve caps
         (fallback s) (selectedRaw s) (mixedSourceAt s adv)}[
      event s ((r.1, r.2.2), r.2.1.2) r.2.1.1] ≤
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← observedRun (encoding s).typedImpl (∅, ∅) s reserve caps
         (fallback s) (selectedRaw s) (mixedSourceAt s adv)
       let physical ← (encoding s).fill r.2.1.1}[
      event s ((r.1, r.2.2), r.2.1.2) physical ∨ (encoding s).Clash r.2.1.1.1] := by
  apply prEvent_bind_mono_of_support
  intro s _
  let E := encoding s
  let source := mixedSourceAt s adv
  let program := observedProgram s reserve caps (fallback s) (selectedRaw s) source
  have single := observed_run E.singleImpl (∅ : Raw.QueryCache) s reserve caps
    (fallback s) (selectedRaw s) source
  have typed := observed_run E.typedImpl (∅, ∅) s reserve caps
    (fallback s) (selectedRaw s) source
  have bound := E.prEvent_simulateQ_singleImpl_run_le_fill_or_clash program
    (fun z => event s z.1 z.2)
  dsimp only at bound
  rw [← single, ← typed] at bound
  rw [← E.romImpl_compose_encodeImpl] at bound
  simp only [bind_map_left, prEvent_norm] at bound
  exact bound

/-- A surviving win at the strict reserve cap has a typed witness or an encoding clash.
The original five-counter certificate has already funded this physical cut. -/
theorem reserve_win_le_typed_win_or_clash (adv : Game.Adversary FIPS205.Answer PK) (q : Nat)
    (fallback : (s : FIPS205.core.PkSeed) → (i : Common.Domain) → Common.Range i) :
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← observedRun (Raw.romImpl ∘ₛ (encoding s).encodeImpl) ∅ s true (32*q-1, 2^64)
         (fallback s) (selectedRaw s) (mixedSourceAt s adv)}[
      SigningView.Wins id r.1.2 ∧ r.2.2.2 = false] ≤
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← observedRun (encoding s).typedImpl (∅, ∅) s true (32*q-1, 2^64)
         (fallback s) (selectedRaw s) (mixedSourceAt s adv)}[
      (SigningView.Wins id r.1.2 ∧ r.2.2.2 = false) ∨ (encoding s).Clash r.2.1.1.1] := by
  apply prEvent_bind_mono_of_support
  intro s _
  let E := encoding s
  let source := mixedSourceAt s adv
  let caps := (32*q-1, 2^64)
  let program := observedProgram s true caps (fallback s) (selectedRaw s) source
  have bound := E.prEvent_simulateQ_singleImpl_run_le program (fun out =>
    SigningView.Wins id out.1.1.2 ∧ out.1.2.2 = false)
  rw [← observed_run E.singleImpl ∅ s true caps (fallback s) (selectedRaw s) source,
    ← observed_run E.typedImpl (∅, ∅) s true caps (fallback s) (selectedRaw s) source,
    ← E.romImpl_compose_encodeImpl] at bound
  simpa only [prEvent_map] using bound

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
