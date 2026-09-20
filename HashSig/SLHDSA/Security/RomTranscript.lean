/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomRun
import all HashSig.SLHDSA.Security.CountedRom

/-!
# The settled transcript of the counted random-oracle run

`HashSig.SLHDSA.Security.RomRun`'s `romRunFull` returns the transcript of the EUF-CMA game — key
pair, signing log, forgery and verdict — together with the cache the shared lazy public-hash
oracle leaves behind.  This module reads every honest computation of that transcript off the
final cache.  `simulateQ_toPartialImpl_eq_some_of_mem_support_romRunFull` says that the final
cache, read as the partial oracle `QueryCache.toPartialImpl`, replays key generation
(Algorithm 18) on some seeds to the transcript's key pair, replays signing (Algorithm 19) on some
randomizer to every logged signature, and replays verification (Algorithm 20) of the forgery to
its verdict.  Every public hash any honest party computed is therefore settled in the final
cache at the value that party saw, and a bad-event analysis can read honest values from the
cache without reference to any total hash function.

The route: the cache only grows along a run (`le_snd_of_mem_support_run_romImpl`); a hash-only
program embedded in the shared world is answered by the lazy oracle alone, so its final cache
replays its output (`simulateQ_toPartialImpl_snd_of_mem_support_run_romImpl_toQueryImpl`, applied
to Algorithms 18--20 through `GeneralScheme.keygenInternalM_natural` and its siblings); a
transcript decomposes into its three stages
(`exists_mem_support_run_romImpl_of_mem_support_romRunFull`); every logged signature is a run of
the signing program between two intermediate caches
(`QueryImpl.exists_le_mem_support_run_of_mem_log_add_withLogging`); and a
reading that succeeds from an intermediate cache succeeds from the final one
(`QueryCache.simulateQ_toPartialImpl_mono`).

## Scope

* No bad event is defined here.  Which cache entries witness a collision, a hidden-value hit or
  an interleaved-target coverage, and the descent from the cached root that finds them, belong to
  a separate module.
* Nothing here is probabilistic.  Every statement is about the support of `romRunFull`; no mass
  of any event is bounded.
* The forger's own queries are not described.  The final cache also holds them, and nothing here
  distinguishes an honest entry from an adversarial one.
* Nothing here is quantum: the oracle is a classical lazily-sampled table.

## Labels

Eleven declarations.

*Settled transcript*:

* `le_snd_of_mem_support_run_romImpl`, `exists_mem_support_run_romImpl_of_liftM_bind`;
* `simulateQ_toPartialImpl_snd_of_mem_support_run_romImpl_toQueryImpl` and its instances
  `simulateQ_toPartialImpl_snd_keygenInternalM_of_mem_support_run_romImpl`,
  `simulateQ_toPartialImpl_snd_signInternalM_of_mem_support_run_romImpl`,
  `simulateQ_toPartialImpl_snd_verifyInternalM_of_mem_support_run_romImpl`;
* `exists_mem_support_run_keygenInternalM_of_mem_support_run_keygen`,
  `exists_mem_support_run_signInternalM_of_mem_support_run_sign`;
* `exists_mem_support_run_romImpl_of_mem_support_romRunFull`,
  `exists_mem_support_run_signInternalM_of_mem_log_romRunFull`;
* `simulateQ_toPartialImpl_eq_some_of_mem_support_romRunFull`.

## References

- NIST FIPS 205, §9, Algorithms 18--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-- The shared lazy interpretation of `romSpec`: private sampling forwarded, the public hash
answered from one cache. -/
local notation "romImpl" => unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core

/-! ## Runs under the lazy oracle -/

/-- A run under the lazy public-hash oracle only extends the cache. -/
theorem le_snd_of_mem_support_run_romImpl {α : Type} (oa : OracleComp romSpec α)
    {c : PublicHash.Cache core} {z : α × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl oa).run c)) : c ≤ z.2 :=
  OracleComp.le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl oa hz

/-- Private sampling at the head of a program leaves the cache untouched: a run of
`liftM oa >>= k` is a run of `k x` from the same cache, for some sample `x`. -/
theorem exists_mem_support_run_romImpl_of_liftM_bind {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp romSpec β) {c : PublicHash.Cache core} {z : β × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl (liftM oa >>= k)).run c)) :
    ∃ x, z ∈ support ((simulateQ romImpl (k x)).run c) := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨x, c'⟩, h₁, hz⟩ := hz
  rw [roSim.run_liftM, support_map] at h₁
  obtain ⟨_, _, h₁⟩ := h₁
  obtain ⟨-, rfl⟩ := Prod.mk.inj h₁
  exact ⟨x, hz⟩

/-- The final cache of a run of a hash-only program, embedded in the shared world through its
query capability, replays the program's output. -/
theorem simulateQ_toPartialImpl_snd_of_mem_support_run_romImpl_toQueryImpl {α : Type}
    (P : OracleComp (publicHashSpec core) α) {c : PublicHash.Cache core}
    {z : α × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl (simulateQ (HasQuery.toQueryImpl
      (spec := publicHashSpec core) (m := OracleComp romSpec)) P)).run c)) :
    simulateQ z.2.toPartialImpl P = some z.1 := by
  rw [QueryImpl.simulateQ_add_simulateQ_toQueryImpl_right] at hz
  exact QueryImpl.simulateQ_toPartialImpl_snd_of_mem_support_run_simulateQ_withCaching _ P hz

/-- The final cache of a run of Algorithm 18 replays the key pair it produced. -/
theorem simulateQ_toPartialImpl_snd_keygenInternalM_of_mem_support_run_romImpl
    (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed)
    {c : PublicHash.Cache core}
    {z : (PublicKeyCore core × SecretKeyCore core) × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl (GeneralScheme.keygenInternalM (m := OracleComp romSpec)
      vp core skSeed skPrf pkSeed)).run c)) :
    simulateQ z.2.toPartialImpl (GeneralScheme.keygenInternalM
      (m := OracleComp (publicHashSpec core)) vp core skSeed skPrf pkSeed) = some z.1 := by
  rw [← GeneralScheme.keygenInternalM_natural vp core (HasQuery.QueryHom.ofSimulateQ
    (spec := publicHashSpec core) (m := OracleComp romSpec)) skSeed skPrf pkSeed,
    HasQuery.QueryHom.ofSimulateQ_apply] at hz
  exact simulateQ_toPartialImpl_snd_of_mem_support_run_romImpl_toQueryImpl core _ hz

/-- The final cache of a run of Algorithm 19 replays the signature it produced. -/
theorem simulateQ_toPartialImpl_snd_signInternalM_of_mem_support_run_romImpl
    (msg : List Byte) (sk : SecretKeyCore core) (addrnd : core.Y) {c : PublicHash.Cache core}
    {z : GeneralScheme.SignatureCore vp core × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl (GeneralScheme.signInternalM (m := OracleComp romSpec)
      vp core msg sk addrnd)).run c)) :
    simulateQ z.2.toPartialImpl (GeneralScheme.signInternalM
      (m := OracleComp (publicHashSpec core)) vp core msg sk addrnd) = some z.1 := by
  rw [← GeneralScheme.signInternalM_natural vp core (HasQuery.QueryHom.ofSimulateQ
    (spec := publicHashSpec core) (m := OracleComp romSpec)) msg sk addrnd,
    HasQuery.QueryHom.ofSimulateQ_apply] at hz
  exact simulateQ_toPartialImpl_snd_of_mem_support_run_romImpl_toQueryImpl core _ hz

/-- The final cache of a run of Algorithm 20 replays the verdict it produced. -/
theorem simulateQ_toPartialImpl_snd_verifyInternalM_of_mem_support_run_romImpl
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core)
    {c : PublicHash.Cache core} {z : Bool × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl (GeneralScheme.verifyInternalM (m := OracleComp romSpec)
      vp core msg sig pk)).run c)) :
    simulateQ z.2.toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core msg sig pk) = some z.1 := by
  rw [← GeneralScheme.verifyInternalM_natural vp core (HasQuery.QueryHom.ofSimulateQ
    (spec := publicHashSpec core) (m := OracleComp romSpec)) msg sig pk,
    HasQuery.QueryHom.ofSimulateQ_apply] at hz
  exact simulateQ_toPartialImpl_snd_of_mem_support_run_romImpl_toQueryImpl core _ hz

/-! ## The transcript of the instrumented run -/

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]

/-- The oracle-parametric scheme the experiment runs, in the shared world. -/
local notation "romAlg" => generalAlgM (m := OracleComp romSpec) vp core

/-- A run of the key generator is a run of Algorithm 18 on some three seeds from the same
cache. -/
theorem exists_mem_support_run_keygenInternalM_of_mem_support_run_keygen
    {c : PublicHash.Cache core}
    {z : (PublicKeyCore core × SecretKeyCore core) × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl (romAlg).keygen).run c)) :
    ∃ (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed), z ∈ support
      ((simulateQ romImpl (GeneralScheme.keygenInternalM (m := OracleComp romSpec)
        vp core skSeed skPrf pkSeed)).run c) := by
  simp only [generalAlgM] at hz
  obtain ⟨skSeed, hz⟩ := exists_mem_support_run_romImpl_of_liftM_bind core _ _ hz
  obtain ⟨skPrf, hz⟩ := exists_mem_support_run_romImpl_of_liftM_bind core _ _ hz
  obtain ⟨pkSeed, hz⟩ := exists_mem_support_run_romImpl_of_liftM_bind core _ _ hz
  exact ⟨skSeed, skPrf, pkSeed, hz⟩

/-- A run of the hedged signer is a run of Algorithm 19 on some randomizer from the same
cache. -/
theorem exists_mem_support_run_signInternalM_of_mem_support_run_sign
    (pk : PublicKeyCore core) (sk : SecretKeyCore core) (msg : List Byte)
    {c : PublicHash.Cache core} {z : GeneralScheme.SignatureCore vp core × PublicHash.Cache core}
    (hz : z ∈ support ((simulateQ romImpl ((romAlg).sign pk sk msg)).run c)) :
    ∃ addrnd : core.Y, z ∈ support ((simulateQ romImpl (GeneralScheme.signInternalM
      (m := OracleComp romSpec) vp core (emptyContextMessage msg) sk addrnd)).run c) := by
  simp only [generalAlgM] at hz
  exact exists_mem_support_run_romImpl_of_liftM_bind core _ _ hz

/-- A transcript of the instrumented run arises from its three stages in sequence: key
generation from the empty cache, the logged forger from the key-generation cache, and
verification of the forgery from the forger's cache to the final one. -/
theorem exists_mem_support_run_romImpl_of_mem_support_romRunFull
    (adv : unforgeableAdv romAlg) {z : RomOutcome vp core × PublicHash.Cache core}
    (hz : z ∈ support (romRunFull core adv)) :
    ∃ cₖ c_f : PublicHash.Cache core,
      ((z.1.pk, z.1.sk), cₖ) ∈ support ((simulateQ romImpl (romAlg).keygen).run ∅) ∧
      (((z.1.msg, z.1.sig), z.1.log), c_f) ∈ support ((simulateQ romImpl (simulateQ
        ((HasQuery.toQueryImpl (spec := romSpec) (m := OracleComp romSpec)).liftTarget
          (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
            (OracleComp romSpec)) + (romAlg).signingOracle z.1.pk z.1.sk)
        (adv.main z.1.pk)).run).run cₖ) ∧
      (z.1.verified, z.2) ∈
        support ((simulateQ romImpl ((romAlg).verify z.1.pk z.1.msg z.1.sig)).run c_f) := by
  unfold romRunFull romGameCoreFull at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨pk, sk⟩, cₖ⟩, hk, ⟨⟨⟨msg, sig⟩, log⟩, c_f⟩, hf, ⟨verified, c_v⟩, hv, hz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨cₖ, c_f, hk, hf, hv⟩

/-- Every logged signature of the instrumented run was produced by a run of Algorithm 19 between
two intermediate caches, the second of which the final cache extends. -/
theorem exists_mem_support_run_signInternalM_of_mem_log_romRunFull
    (adv : unforgeableAdv romAlg) {z : RomOutcome vp core × PublicHash.Cache core}
    (hz : z ∈ support (romRunFull core adv))
    {e : (t : (List Byte →ₒ GeneralScheme.SignatureCore vp core).Domain) ×
      (List Byte →ₒ GeneralScheme.SignatureCore vp core).Range t} (he : e ∈ z.1.log) :
    ∃ (addrnd : core.Y) (c₁ c₂ : PublicHash.Cache core), c₂ ≤ z.2 ∧ (e.2, c₂) ∈ support
      ((simulateQ romImpl (GeneralScheme.signInternalM (m := OracleComp romSpec) vp core
        (emptyContextMessage e.1) z.1.sk addrnd)).run c₁) := by
  obtain ⟨cₖ, c_f, -, hf, hv⟩ :=
    exists_mem_support_run_romImpl_of_mem_support_romRunFull core adv hz
  obtain ⟨c₁, c₂, -, hc₂, hmem⟩ :=
    QueryImpl.exists_le_mem_support_run_of_mem_log_add_withLogging romImpl
      (fun ob _ _ hz => le_snd_of_mem_support_run_romImpl core ob hz) ((romAlg).sign z.1.pk z.1.sk)
      (adv.main z.1.pk) hf he
  obtain ⟨addrnd, hmem⟩ :=
    exists_mem_support_run_signInternalM_of_mem_support_run_sign core _ _ e.1 hmem
  have hcv := le_snd_of_mem_support_run_romImpl core _ hv
  exact ⟨addrnd, c₁, c₂, hc₂.trans hcv, hmem⟩

/-- **Every honest computation of the instrumented run is read off its final cache.**  Key
generation, each logged signature and the final verification are replayed by the final cache
as a partial oracle: the cache settles every hash any honest party computed. -/
theorem simulateQ_toPartialImpl_eq_some_of_mem_support_romRunFull
    (adv : unforgeableAdv romAlg) {z : RomOutcome vp core × PublicHash.Cache core}
    (hz : z ∈ support (romRunFull core adv)) :
    (∃ (skSeed : core.SkSeed) (skPrf : core.SkPrf) (pkSeed : core.PkSeed),
      simulateQ z.2.toPartialImpl (GeneralScheme.keygenInternalM
        (m := OracleComp (publicHashSpec core)) vp core skSeed skPrf pkSeed) =
          some (z.1.pk, z.1.sk)) ∧
    (∀ e ∈ z.1.log, ∃ addrnd : core.Y,
      simulateQ z.2.toPartialImpl (GeneralScheme.signInternalM
        (m := OracleComp (publicHashSpec core)) vp core (emptyContextMessage e.1) z.1.sk addrnd) =
          some e.2) ∧
    simulateQ z.2.toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core (emptyContextMessage z.1.msg) z.1.sig
        z.1.pk) = some z.1.verified := by
  obtain ⟨cₖ, c_f, hk, hf, hv⟩ :=
    exists_mem_support_run_romImpl_of_mem_support_romRunFull core adv hz
  have hkf : cₖ ≤ c_f := le_snd_of_mem_support_run_romImpl core _ hf
  have hcv := le_snd_of_mem_support_run_romImpl core _ hv
  refine ⟨?_, fun e he => ?_, ?_⟩
  · obtain ⟨skSeed, skPrf, pkSeed, hk⟩ :=
      exists_mem_support_run_keygenInternalM_of_mem_support_run_keygen core hk
    exact ⟨skSeed, skPrf, pkSeed, QueryCache.simulateQ_toPartialImpl_mono (hkf.trans hcv) _
      (simulateQ_toPartialImpl_snd_keygenInternalM_of_mem_support_run_romImpl core _ _ _ hk)⟩
  · obtain ⟨addrnd, c₁, c₂, hc₂, hmem⟩ :=
      exists_mem_support_run_signInternalM_of_mem_log_romRunFull core adv hz he
    exact ⟨addrnd, QueryCache.simulateQ_toPartialImpl_mono hc₂ _
      (simulateQ_toPartialImpl_snd_signInternalM_of_mem_support_run_romImpl core _ _ _ hmem)⟩
  · simp only [generalAlgM] at hv
    exact simulateQ_toPartialImpl_snd_verifyInternalM_of_mem_support_run_romImpl core _ _ _ hv

end SLHDSA.Security
