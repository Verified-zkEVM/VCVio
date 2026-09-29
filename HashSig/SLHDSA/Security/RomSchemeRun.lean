/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomDescentSecret
public import VCVio.CryptoFoundations.SignatureAlg.Transcript

/-!
# The run of SLH-DSA in the random oracle model, and its settled transcript

`romSchemeRun` runs the unforgeability experiment of `HashSig.SLHDSA.Security.Target`'s
`romScheme`, returning its transcript (`SignatureAlg.unforgeableTranscriptExperiment`) under one
lazy random oracle for every hash, `PRF` and `PRF_msg` query, from the empty cache, together with
the final cache.  The transcript is read as a `RomOutcome` (`RomOutcome.ofTranscript`), the type
the events of `HashSig.SLHDSA.Security.RomDescentSecret` are stated over.  The success bit of the
experiment is `RomOutcome.wins` of the transcript (`wins_ofTranscript`), so the forging advantage
in the random-oracle runtime is the probability that the run's transcript wins
(`unforgeableAdvantage_romScheme_eq`).

`settled_of_mem_support_romSchemeRun` reads every honest computation of the run off the public-hash
part of the final cache (`QueryCache.fst`): key generation at the oracle-backed provider settles
the top-tree root at the public root, and the secret key carries the public seed and root of the
public key; every logged signature is settled at its own randomizer; and the verification of the
forgery is settled at its verdict.  The route is the generic
`OracleComp.simulateQ_toPartialImpl_fst_of_mem_support_run_romImpl`, applied through the lift
lemmas of `HashSig.SLHDSA.Security.CacheSecret`.

## Scope

* Everything here is deterministic on the support of `romSchemeRun`; no probability is bounded.
* The forger's own queries are not described; the final cache also holds them.
* Nothing here is quantum.

## Labels

*The run*: `RomOutcome.ofTranscript`, `wins_ofTranscript`, `romSchemeRun`,
`unforgeableAdvantage_romScheme_eq`.

*Runs under the lazy oracle* (private): `le_snd_of_mem_support_run_romI`,
`exists_mem_support_run_romI_of_liftM_bind`, `simulateQ_fst_of_mem_support_run_romI`.

*The settled transcript*: `settled_of_mem_support_romSchemeRun`.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- A transcript of the unforgeability experiment of an SLH-DSA scheme, read as a `RomOutcome`. -/
@[expose] def RomOutcome.ofTranscript
    (o : UnforgeableTranscript (List Byte) (PublicKeyCore core) (SecretKeyCore core)
      (GeneralScheme.SignatureCore vp core)) : RomOutcome vp core :=
  ⟨o.pk, o.sk, o.log, o.msg, o.sig, o.verified⟩

/-- The success bit of a transcript is that of the `RomOutcome` it is read as. -/
theorem wins_ofTranscript
    (o : UnforgeableTranscript (List Byte) (PublicKeyCore core) (SecretKeyCore core)
      (GeneralScheme.SignatureCore vp core)) :
    (RomOutcome.ofTranscript core o).wins = o.wins := by
  rw [Bool.eq_iff_iff, RomOutcome.wins_eq_true_iff, UnforgeableTranscript.wins_eq_true_iff]
  rfl

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.Y]
  [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- The transcript of the unforgeability experiment of `romScheme` under one lazy random oracle
for every hash, `PRF` and `PRF_msg` query, run from the empty cache, together with the final
cache. -/
@[expose] noncomputable def romSchemeRun (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) :
    ProbComp (RomOutcome vp core × (hashSpec core).QueryCache) :=
  (simulateQ (hashSpec core).romImpl
    (RomOutcome.ofTranscript core <$> unforgeableTranscriptExperiment adv)).run ∅

/-- The forging advantage against `romScheme` in the random-oracle runtime is the probability that
the transcript of `romSchemeRun` wins. -/
theorem unforgeableAdvantage_romScheme_eq (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec core)) adv =
      Pr{let z ← romSchemeRun core e optRand pkSeedDist adv}[z.1.wins = true] := by
  rw [prEvent_eq_evalDist_decide, unforgeableAdvantage, ProbCompRuntime.rom_evalDist,
    ← map_wins_unforgeableTranscriptExperiment, romSchemeRun]
  congr 1
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, bind_pure_comp,
    wins_ofTranscript, Bool.decide_eq_true]

/-! ## Runs under the lazy oracle -/

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] in
/-- A run under the lazy oracle only extends the cache. -/
private theorem le_snd_of_mem_support_run_romI {α : Type}
    (oa : OracleComp (unifSpec + hashSpec core) α) (s : (hashSpec core).QueryCache)
    (z : α × (hashSpec core).QueryCache)
    (hz : z ∈ support ((simulateQ (hashSpec core).romImpl oa).run s)) :
    s ≤ z.2 :=
  le_snd_of_mem_support_run_unifFwdImpl_add_withCaching uniformSampleImpl oa hz

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] in
/-- Private sampling at the head of a program leaves the cache untouched. -/
private theorem exists_mem_support_run_romI_of_liftM_bind {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp (unifSpec + hashSpec core) β) {c : (hashSpec core).QueryCache}
    {z : β × (hashSpec core).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec core).romImpl (liftM oa >>= k)).run c)) :
    ∃ x, z ∈ support ((simulateQ (hashSpec core).romImpl (k x)).run c) := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨_, ⟨x, -, rfl⟩, hz⟩ := roSim.run_liftM_support _ _ _ ▸ hz
  exact ⟨x, hz⟩

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] in
/-- A run of a public-hash program issued in the whole oracle world settles, in the public-hash
part of its final cache, the value it returned. -/
private theorem simulateQ_fst_of_mem_support_run_romI {α : Type}
    (P : OracleComp (publicHashSpec core) α) {c : (hashSpec core).QueryCache}
    {z : α × (hashSpec core).QueryCache}
    (hz : z ∈ support ((simulateQ (hashSpec core).romImpl
      ((HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core)
        (m := OracleComp (unifSpec + hashSpec core))).toMonadHom P)).run c)) :
    simulateQ z.2.fst.toPartialImpl P = some z.1 :=
  simulateQ_toPartialImpl_fst_of_mem_support_run_romImpl P hz

/-! ## The settled transcript -/

/-- **Every honest computation of the run is read off the public-hash part of its final
cache.**  Key generation at the oracle-backed provider settles the top-tree root at the public
root, and the secret key carries the public key's seed and root; every logged signature is settled
at its own randomizer; and the verification of the forgery is settled at its verdict. -/
theorem settled_of_mem_support_romSchemeRun (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    {z : RomOutcome vp core × (hashSpec core).QueryCache}
    (hz : z ∈ support (romSchemeRun core e optRand pkSeedDist adv)) :
    z.1.sk.pkSeed = z.1.pk.pkSeed ∧ z.1.sk.pkRoot = z.1.pk.pkRoot ∧
    simulateQ z.2.fst.toPartialImpl (GeneralScheme.keygenInternalWithSecretM core
      (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) z.1.pk.pkSeed) = some z.1.pk.pkRoot ∧
    (∀ x ∈ z.1.log, simulateQ z.2.fst.toPartialImpl
      (GeneralScheme.signInternalWithSecretRandomizerM core
        (oracleSecret core e z.1.pk.pkSeed z.1.sk.skSeed) x.1 z.1.pk.pkSeed z.1.pk.pkRoot
        x.2.randomness) = some x.2) ∧
    simulateQ z.2.fst.toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core z.1.msg z.1.sig z.1.pk) =
        some z.1.verified := by
  unfold romSchemeRun at hz
  rw [simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨⟨w, c⟩, hw, rfl⟩ := hz
  obtain ⟨s₁, s₂, hk, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment
      (hashSpec core).romImpl adv hw
  have h₁₂ : s₁ ≤ s₂ := le_snd_of_mem_support_run_romI core _ _ _ hf
  have h₂c : s₂ ≤ c := le_snd_of_mem_support_run_romI core _ _ _ hv
  -- key generation
  obtain ⟨pkSeed, hk⟩ := exists_mem_support_run_romI_of_liftM_bind core _ _ hk
  unfold romKeygenAt at hk
  obtain ⟨skSeed, hk⟩ := exists_mem_support_run_romI_of_liftM_bind core _ _ hk
  obtain ⟨skPrf, hk⟩ := exists_mem_support_run_romI_of_liftM_bind core _ _ hk
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hk
  obtain ⟨⟨pkRoot, s₀⟩, hroot, hk⟩ := hk
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hk
  obtain ⟨hks, rfl⟩ := Prod.mk.inj hk
  rw [keygenInternalWithSecretM_oracleSecret_eq_ofSimulateQ] at hroot
  have hroot := simulateQ_fst_of_mem_support_run_romI core _ hroot
  obtain ⟨hpk, hsk⟩ := Prod.mk.inj hks
  simp only [RomOutcome.ofTranscript]
  rw [hpk, hsk]
  refine ⟨rfl, rfl, QueryCache.simulateQ_toPartialImpl_mono
    (QueryCache.fst_mono (h₁₂.trans h₂c)) _ hroot, fun x hx => ?_, ?_⟩
  · -- a logged signature
    obtain ⟨t₁, t₂, ht₂, hsign⟩ := exists_mem_support_run_sign_of_mem_log
      (hashSpec core).romImpl
      (fun ob s z hz => le_snd_of_mem_support_run_romI core ob s z hz) adv hw hx
    rw [romScheme_sign] at hsign
    obtain ⟨addrnd, hsign⟩ := exists_mem_support_run_romI_of_liftM_bind core _ _ hsign
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hsign
    obtain ⟨⟨R, t₃⟩, -, hsign⟩ := hsign
    rw [hsk] at hsign
    rw [signInternalWithSecretRandomizerM_oracleSecret_eq_ofSimulateQ] at hsign
    have hread := QueryCache.simulateQ_toPartialImpl_mono (QueryCache.fst_mono ht₂) _
      (simulateQ_fst_of_mem_support_run_romI core _ hsign)
    obtain ⟨hR, -⟩ :=
      components_of_simulateQ_toPartialImpl_signInternalWithSecretRandomizerM core _ _ _ _ _ _
        hread
    simp only at hR hread ⊢
    rw [← hR] at hread
    exact hread
  · -- the verification
    rw [romScheme_verify, ← GeneralScheme.verifyInternalM_natural vp core
      (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core)
        (m := OracleComp (unifSpec + hashSpec core)))] at hv
    rw [hpk] at hv
    exact simulateQ_fst_of_mem_support_run_romI core _ hv

end SLHDSA.Security
