/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.RecordedTail

/-!
# Stripping the honest phase, with the record kept

`evalDist_run_recordedAfterSeeds` says that answering key generation and the signer from the
walk's table changes nothing about the law of the run of the game that **records** the
adversary's and the verifier's own inputs. The congruence argument never reads the writer the
phase carries, so it is stated over an arbitrary monoid (`writerRun`,
`evalDist_writerRun_congr`), and the recorded game's stripping is then three steps: key
generation agrees because its probes are the table's, the two signing oracles agree because the
stripped signer's run is the signer's (`evalDist_writerRun_signingOracle`), and the phase's law
follows by the congruence.

**It is an equality, not a bound.** Every step of the transport is, and a bound appearing in one
of them would mean a step was not the equality it is taken for.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedStripping

variable {α β : Type}

open Security RecordedQueries StrippedGame

/-! ## The writer's run, over an arbitrary monoid -/

/-- The run of a phase computation carrying a writer, from a log and a cache. -/
noncomputable def writerRun {ω : Type} [Monoid ω] {α : Type}
    (x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α) (log : SigningLog)
    (current : QueryCache HashSpec) :
    ProbComp (((α × ω) × SigningLog) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom ((WriterT.run x).run log)).run current

/-- `writerRun` of a bind runs the first part and then the continuation, multiplying the
writer values in order. -/
theorem writerRun_bind {ω : Type} [Monoid ω] {α β : Type}
    (x : WriterT ω (StateT SigningLog (OracleComp OracleWorld)) α)
    (next : α → WriterT ω (StateT SigningLog (OracleComp OracleWorld)) β)
    (log : SigningLog) (current : QueryCache HashSpec) :
    writerRun (x >>= next) log current =
      writerRun x log current >>= fun outer =>
        (fun inner => (((inner.1.1.1, outer.1.1.2 * inner.1.1.2), inner.1.2), inner.2)) <$>
          writerRun (next outer.1.1.1) outer.1.2 outer.2 := by
  simp only [writerRun, WriterT.run_bind, StateT.run_bind, StateT.run_map, simulateQ_bind,
    simulateQ_map, StateT.run_map]

/-- **A handler may be replaced by one with the same law**, at every cache carrying the warm
table. The argument never reads the writer the phase carries. -/
theorem evalDist_writerRun_congr {ω : Type} [Monoid ω] (warm : QueryCache HashSpec)
    (impl impl' : QueryImpl (OracleWorld + SigningSpec)
      (WriterT ω (StateT SigningLog (OracleComp OracleWorld))))
    (hagree : ∀ (t : (OracleWorld + SigningSpec).Domain) (log : SigningLog)
      (current : QueryCache HashSpec), Extends warm current →
      writerRun (impl t) log current =ᵈ writerRun (impl' t) log current)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (log : SigningLog) (current : QueryCache HashSpec), Extends warm current →
      writerRun (simulateQ impl computation) log current =ᵈ
        writerRun (simulateQ impl' computation) log current := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _ _; simp only [simulateQ_pure]; exact .rfl
  | query_bind t next ih =>
    intro log current hsub
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
      writerRun_bind, writerRun_bind]
    refine (OracleComp.EvalDistEq.bind_congr_of_support _ fun outer houter => ?_).trans
      ((hagree t log current hsub).bind_left _)
    exact (ih outer.1.1.1 outer.1.2 outer.2
      (extends_of_mem_support ((WriterT.run (impl t)).run log) warm current hsub outer
        houter)).map _

/-! ## The recorded game, stripped -/

/-- **The two recording signing oracles answer alike** at every cache carrying the warm table. -/
theorem evalDist_writerRun_signingOracle (warm : QueryCache HashSpec) (sk : SecretKey)
    (t : (OracleWorld + SigningSpec).Domain) (log : SigningLog)
    (current : QueryCache HashSpec) (hsub : Extends warm current) :
    writerRun ((recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk)) t) log
        current =ᵈ
      writerRun ((recordedAdversaryImpl +
        recordedSigningOracle (StrippedGame.strippedSign warm sk)) t) log current := by
  rcases t with world | request
  · exact .rfl
  · have heq : writerRun ((recordedAdversaryImpl + recordedSigningOracle (Scheme.sign sk))
          (.inr request)) log current =
        writerRun ((recordedAdversaryImpl +
          recordedSigningOracle (StrippedGame.strippedSign warm sk)) (.inr request)) log
          current := by
      change (simulateQ KeygenUniform.rom
          (((recordedSigningOracle (Scheme.sign sk) request).run).run log)).run current =
        (simulateQ KeygenUniform.rom
          (((recordedSigningOracle (StrippedGame.strippedSign warm sk) request).run).run
            log)).run current
      rw [run_recordedSigningOracle, run_recordedSigningOracle, simulateQ_bind, simulateQ_bind,
        StateT.run_bind, StateT.run_bind,
        run_strippedSign warm sk request current hsub]
    rw [heq]

/-- **Stripping the honest phase changes nothing about the law of the recorded run.** -/
theorem evalDist_run_recordedAfterSeeds (adversary : Adversary)
    (sds : Digest × Digest × Digest) (warm current : QueryCache HashSpec)
    (hsub : Extends warm current) :
    (simulateQ KeygenUniform.rom
        (RecordedQueries.recordedAfterSeeds adversary sds warm)).run current =ᵈ
      (simulateQ KeygenUniform.rom
        (RecordedTail.recordedAfterSeeds adversary sds)).run current := by
  unfold RecordedQueries.recordedAfterSeeds RecordedTail.recordedAfterSeeds
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    run_strippedKeygen warm sds current hsub]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ ?_
  rintro ⟨⟨sk, pk⟩, cache⟩ hstep
  have hcache : Extends warm cache :=
    extends_of_mem_support _ warm current hsub ((sk, pk), cache) hstep
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
  refine EvalDistEq.bind_left ?_ _
  exact evalDist_writerRun_congr warm _ _
    (fun t log inner hinner =>
      (evalDist_writerRun_signingOracle warm sk t log inner hinner).symm)
    (adversary.main pk) [] cache hcache

end SlhDsaSecurity.RecordedStripping
