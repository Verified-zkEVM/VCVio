/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Observation
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.KeySampler
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
import all HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Work.JointBudget

/-!
# The guarded FIPS experiment and its filled typed transcript

The sampled secret seeds and the guarded outcome reconstruct the FIPS secret key while retaining
the public key, replies, cache and costs. The FIPS winning probability is bounded by a win or a
cache hazard in the filled experiment, plus the weak-key contribution.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical

/-- Restore the actual secret key together with its original signed outputs, cache and costs. -/
def rebuild (secret : GuardedFill.Secret) (r : GuardedFill.Value × H.QueryCache) :
    FullActual × (((H.QueryCache × Raw.QueryCache) × Meta) × Paid) :=
  let full := r.1.1.1.1
  (((full.1.1, fillSecretKey FIPS205.core secret full.1.2), full.2),
    (((r.2, r.1.1.2), r.1.2), r.1.1.1.2.2))

/-- Original typed FIPS key sampling resolves a secret-independent guarded program.
All replies, both keys, the raw table, the typed cache and the exact paid and passive counts
are retained on every branch. -/
theorem typed_run_eq_fixed (s : FIPS205.core.PkSeed) (adv : Game.Adversary FIPS205.Answer PK)
    (reserve : Bool) (caps : Nat × Nat) :
    observedRun (encoding s).typedImpl (∅, ∅) s reserve caps (Native.mixedFallback s)
      (selectedRaw s) (mixedSourceAt s adv) = (do
      let secret ← ($ᵗ GuardedFill.Secret : ProbComp GuardedFill.Secret)
      rebuild secret <$> (simulateQ ((secretEncoding FIPS205.core (Equiv.refl _) s).realImpl secret)
        (GuardedFill.freeProgram s adv reserve true caps)).run ∅) := by
  have factor := (Native.actual_guarded_fixed_source_factor s adv reserve true caps ∅ ∅).1
  have square := Native.resolved_guarded_router_observer_square s adv reserve true caps
  have labels : mixedEventToRaw = Native.rawEvent := by
    funext event
    rcases event with ⟨phase, n | typed | bytes⟩ | request <;> simp [Native.rawEvent]
  have src : mixedSourceAt s adv = simulateQ Native.resolvedProjection
      (SigningView.Events.fullExperiment (Native.realView s) (Native.rawMain adv)) := by
    unfold Native.resolvedProjection
    rw [← labels]
    rfl
  rw [src]
  refine factor.trans ?_
  apply bind_congr
  intro secret
  have routed := square secret
  dsimp only at routed
  change _ = rebuild secret <$> _
  rw [← routed]
  simp only [Functor.map_map, rebuild, bind_pure_comp]

/-- A surviving original physical FIPS winning forgery at the strict reserve cap reaches the
filled graph with a surviving forgery, an encoding clash, a hidden-input hit, or a graph conflict.
Every hazard concerns the same run. -/
theorem reserve_physical_win_le_filled (adv : Game.Adversary FIPS205.Answer PK) (q : Nat)
    (fallback : (s : FIPS205.core.PkSeed) →
      (input : LabCommon.Domain) → LabCommon.Range input) :
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← observedRun (Raw.romImpl ∘ₛ (encoding s).encodeImpl) ∅ s true (32*q-1, 2^64)
         (Native.mixedFallback s) (selectedRaw s) (mixedSourceAt s adv)}[
      SigningView.Wins id r.1.2 ∧ r.2.2.2 = false] ≤
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← (slhGraph FIPS205.core s).deferredFillDraw ($ᵗ GuardedFill.Secret)
         (GuardedFill.labProgram s adv true true (32*q-1, 2^64) (fallback s))}[
      let obs := GuardedFill.observe r.1.1
      let G := slhGraph FIPS205.core s
      let E := secretEncoding FIPS205.core (Equiv.refl _) s
      let split := G.toSplitCache r.2.1
      ((∃ out, obs.2.1 = some out ∧ SigningView.Wins id out) ∨
        (encoding s).Clash (E.merge r.2.2 split)) ∨
        (∃ x, (split.1 (E.enc r.2.2 x)).isSome) ∨ G.Conflict r.2.1] := by
  apply (reserve_win_le_typed_win_or_clash adv q Native.mixedFallback).trans
  apply prEvent_bind_mono_of_support
  intro s _
  let event := fun (_ : GuardedFill.Secret) (obs : GuardedFill.Observation)
      (cache : H.QueryCache) =>
    (∃ out, obs.2.1 = some out ∧ SigningView.Wins id out) ∨ (encoding s).Clash cache
  have bound := GuardedFill.real_free_le_filled s adv true true (32*q-1, 2^64) (fallback s)
    ($ᵗ GuardedFill.Secret) event
  refine le_trans ?_ bound
  rw [typed_run_eq_fixed]
  simp only [prEvent_norm]
  apply prEvent_bind_mono_of_support
  intro secret _
  apply prEvent_mono
  intro r hit
  rcases hit with win | clash
  · have survive : r.1.1.1.2.2.2 = false := win.2
    exact Or.inl ⟨_, by simp [GuardedFill.observe, survive, rebuild], win.1⟩
  · exact Or.inr clash

/-- The original signing lifetime and its single almost-sure joint work budget suffice for the
filled hazard cut. The weak-key winning term is evaluated on the original physical execution. -/
theorem original_win_le_filled_add_weak (adv : Game.Adversary FIPS205.Answer PK) (q : Nat)
    (hlimit : Game.WithinSigningLimit FIPS205.scheme adv)
    (hbound : (Game.securityGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q)
    (fallback : (s : FIPS205.core.PkSeed) →
      (input : LabCommon.Domain) → LabCommon.Range input) :
    Pr{let out ← (Game.securityGame FIPS205.scheme).experiment () adv}[out.1 = true] ≤
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let r ← (slhGraph FIPS205.core s).deferredFillDraw ($ᵗ GuardedFill.Secret)
         (GuardedFill.labProgram s adv true true (32*q-1, 2^64) (fallback s))}[
      let obs := GuardedFill.observe r.1.1
      let G := slhGraph FIPS205.core s
      let E := secretEncoding FIPS205.core (Equiv.refl _) s
      let split := G.toSplitCache r.2.1
      ((∃ out, obs.2.1 = some out ∧ SigningView.Wins id out) ∨
        (encoding s).Clash (E.merge r.2.2 split)) ∨
        (∃ x, (split.1 (E.enc r.2.2 x)).isSome) ∨ G.Conflict r.2.1] +
    Pr{let s ← ($ᵗ FIPS205.core.PkSeed : ProbComp FIPS205.core.PkSeed)
       let physical := eraseObsImpl (Ev := Ev) (Raw.romImpl ∘ₛ (encoding s).encodeImpl)
       let observed := physical.extendState (aux (spec := Native) (selectedRaw s))
       let out ← ((simulateQ (observed.withAddCost
           (Sum.elim (fun _ : Native.Domain => (0,0)) (policy true s)))
         (mixedSourceAt s adv)).runAdd).run
         (∅, (0, .keygen))}[
      SigningView.Wins id out.1.1.2 ∧ IsWeakKey FIPS205.params out.1.1.1.1] := by
  have cut := (physical_reserve_nonweak_win_guard adv q hlimit hbound Native.mixedFallback).2
  simp only [prEvent_norm] at cut
  exact cut.trans (add_le_add (reserve_physical_win_le_filled adv q fallback) le_rfl)

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.Physical
