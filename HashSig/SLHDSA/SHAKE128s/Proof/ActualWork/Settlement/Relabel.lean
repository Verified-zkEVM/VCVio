/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
import HashSig.SLHDSA.Security.Transport
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.SimSemantics.WriterT.Core
import all HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Pure
import all HashSig.SLHDSA.Security.CoverageRun
import all HashSig.SLHDSA.Security.NativeCounts
import all HashSig.SLHDSA.Security.NativeRelative
import all HashSig.SLHDSA.Security.SeedCoupling
import all VCVio.CryptoFoundations.SignatureAlg.CountedExperiment
import all VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Price.WinningEvent
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Tapes
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.KeySampler
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.Counters
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.DeferredLaw
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.CacheOrigins
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Transcript.KeyMarginal
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Settlement.Support

/-!
# Support under relabeling a nonaborting terminal run

The relabeling argument transports supported outputs through the merged cache.
The observation argument recovers the full output on branches that survive the guard.
-/

public section

section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded
open MeasureTheory
open SLHDSA.Security.CanonicalGames SLHDSA.DigestTransport
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

private theorem eq_of_observe_nonabort {v w : Value} (e : observe v = observe w)
    (nb : w.1.1.2.2.2 = false) : v = w := by
  rcases v with ⟨⟨⟨⟨kv, ov⟩, ⟨⟨⟩, cv, bv⟩⟩, rv⟩, mv⟩
  rcases w with ⟨⟨⟨⟨kw, ow⟩, ⟨⟨⟩, cw, bw⟩⟩, rw⟩, mw⟩
  change bw = false at nb
  subst bw
  cases bv <;> simp_all [observe]

/-- A conflict-free relabeled result can occur with the same value and merged cache in the real
experiment if the projected public cache contains no entry at any encoded secret input. -/
theorem realSupport_of_relabel (s : FIPS205.core.PkSeed)
    {α : Type} (free : OracleComp (deriveSpec FIPS205.core) α)
    (val : α) (filled : LabState FIPS205.core) (secret : Secret)
    (relabelSupport : (val, filled) ∈ support
      ((simulateQ (slhGraph FIPS205.core s).relabelImpl free).run (∅, ∅)))
    (hnoConflict : ¬(slhGraph FIPS205.core s).Conflict filled)
    (hnoSecretHit : ¬∃ x, (((slhGraph FIPS205.core s).toSplitCache filled).1
      ((secretEncoding FIPS205.core (Equiv.refl _) s).enc secret x)).isSome) :
    (val, (secretEncoding FIPS205.core (Equiv.refl _) s).merge secret
      ((slhGraph FIPS205.core s).toSplitCache filled)) ∈ support
      ((simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret) free).run
        ∅) := by
  classical
  let G := slhGraph FIPS205.core s
  let E := secretEncoding FIPS205.core (Equiv.refl _) s
  let idealOutput := (val, G.toSplitCache filled)
  have idealSupport : idealOutput ∈ support
      ((simulateQ (SecretEncoding.idealImpl H (DeriveQuery FIPS205.core)
        FIPS205.core.Y) free).run (∅, ∅)) := by
    have positive : 0 < Pr{let result ←
        (simulateQ G.relabelImpl free).run (∅, ∅)}[
          (result.1, G.toSplitCache result.2) = idealOutput ∧ ¬G.Conflict result.2] :=
      (prEvent_pos_iff _ _).2
        ⟨(val, filled), relabelSupport, rfl, hnoConflict⟩
    have upper := G.prEvent_relabelImpl_and_not_conflict_le free
      (fun result => result = idealOutput)
    obtain ⟨result, hresult, hresultEq⟩ :=
      (prEvent_pos_iff _ _).1 (lt_of_lt_of_le positive upper)
    simpa only [hresultEq] using hresult
  have flaggedSupport :
      (val, (G.toSplitCache filled, false)) ∈ support
        ((simulateQ (E.flaggedIdealImpl secret) free).run ((∅, ∅), false)) := by
    rw [← E.map_run_simulateQ_flaggedIdealImpl secret free (∅, ∅) false,
      support_map] at idealSupport
    obtain ⟨flagged, hflagged, hprojection⟩ := idealSupport
    have keyEq : flagged.2.1 = G.toSplitCache filled := congrArg Prod.snd hprojection
    have valueEq : flagged.1 = val := congrArg Prod.fst hprojection
    have noFlag : flagged.2.2 = false := by
      cases hflag : flagged.2.2
      · rfl
      · have hit := (E.flag_eq_true_iff_of_mem_support_flaggedIdealImpl
          secret free hflagged).1 hflag
        rw [keyEq] at hit
        exact (hnoSecretHit hit).elim
    have shape : flagged = (val, (G.toSplitCache filled, false)) := by
      exact Prod.ext valueEq (Prod.ext keyEq noFlag)
    simpa only [shape] using hflagged
  have coupledSupport :
      (val, (G.toSplitCache filled, false)) ∈ support
        ((simulateQ (E.coupledImpl secret) free).run ((∅, ∅), false)) := by
    let desired := (val, (G.toSplitCache filled, false))
    have positive : 0 < Pr{let result ←
        (simulateQ (E.flaggedIdealImpl secret) free).run ((∅, ∅), false)}[
          result = desired ∧ ¬result.2.2 = true] :=
      (prEvent_pos_iff _ _).2 ⟨desired, flaggedSupport, rfl, by simp [desired]⟩
    have upper := QueryImpl.AgreeUntilBad.prEvent_simulateQ_run_and_not_bad_le
      (E.agreeUntilBad_coupledImpl_flaggedIdealImpl secret).symm
        (E.flaggedIdealImpl_preservesInv secret) free ((∅, ∅), false)
        (fun result => result = desired)
    obtain ⟨result, hresult, hresultEq⟩ :=
      (prEvent_pos_iff _ _).1 (lt_of_lt_of_le positive upper)
    simpa only [hresultEq] using hresult
  have realSupport : (val, E.merge secret (G.toSplitCache filled)) ∈ support
      ((simulateQ (E.realImpl secret) free).run ∅) := by
    rw [← E.merge_empty secret,
      ← E.map_run_simulateQ_coupledImpl secret free ((∅, ∅), false), support_map]
    exact ⟨(val, (G.toSplitCache filled, false)), coupledSupport, rfl⟩
  exact realSupport

/-- Equality of event probabilities for the observation and state transfers support membership
for every nonaborting value paired with that state. -/
theorem mem_of_observed {σ : Type} {p q : ProbComp (Value × σ)}
    (same : ∀ event : Observation → σ → Prop,
      Pr{let x ← p}[event (observe x.1) x.2] = Pr{let x ← q}[event (observe x.1) x.2])
    (val : Value) (st : σ) (nb : val.1.1.2.2.2 = false)
    (hq : (val, st) ∈ support q) : (val, st) ∈ support p := by
  let event := fun obs state => obs = observe val ∧ state = st
  have pos : 0 < Pr{let r ← q}[event (observe r.1) r.2] :=
    (prEvent_pos_iff _ _).2 ⟨(val, st), hq, rfl, rfl⟩
  obtain ⟨r, hr, hval, hstate⟩ := (prEvent_pos_iff _ _).1 (pos.trans_eq (same event).symm)
  have eq : r = (val, st) := Prod.ext (eq_of_observe_nonabort hval nb) hstate
  exact eq ▸ hr

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
end
