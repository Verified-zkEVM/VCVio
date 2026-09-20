/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CountedRom
public import VCVio.OracleComp.QueryTracking.RandomOracle.CachePartial
public import VCVio.OracleComp.QueryTracking.WriterCost
import all HashSig.SLHDSA.Security.CountedRom

/-!
# The instrumented counted random-oracle run for SLH-DSA

`HashSig.SLHDSA.Security.CountedRom`'s `romGameCore` returns only the success bit of the EUF-CMA
game.  A bad-event analysis needs the whole transcript: the key pair, the signing log, the
forgery and the verification verdict, together with the public-hash cache the lazy random oracle
leaves behind.  `romGameCoreFull` is `romGameCore` returning that transcript as a `RomOutcome`,
`romRunFull` runs it under the same shared lazy oracle from the empty cache and keeps the final
cache, and the two projection theorems (`romGameCore_eq_map`, `fst_map_countedRomExperiment`)
say the counted experiment's success bit is a function of this run.  `romForgeAdvantage_eq`
restates the advantage as the mass of the winning event of `romRunFull`, so a bound on that mass
is a bound on `romForgeAdvantage`.

## Scope

* No bad event is defined here.  The three-disjunct bad event of the random-oracle bridge
  (same-address target collision, hidden-value hit, interleaved-target coverage) and the
  descent from the cached root that produces it belong to a separate module.
* The only probabilistic statement is `romForgeAdvantage_eq`, a change of variables along
  `fst_map_countedRomExperiment`.  No bound on `romForgeAdvantage`, and no bound on the mass of
  any event of `romRunFull`, is proved here.
* The routing lemma (a hash-only sub-computation lifted into `unifSpec + publicHashSpec core` is
  simulated by `PublicHash.randomOracle` alone, with no uniform query) is not here.
* `romGameCoreFull` and `romRunFull` are exposed, so a bridge module can unfold them without
  `import all`.  `RomOutcome.wins` is not exposed; `RomOutcome.wins_eq_true_iff` characterises
  it without reference to the decidability instances it fixes.
* Nothing here is quantum: the oracle is a classical lazily-sampled table.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

/-- The transcript of one execution of the EUF-CMA game: key pair, signing log, forgery and
verification verdict. -/
structure RomOutcome (vp : ValidatedParams) (core : CorePrimitives vp.params) where
  /-- The public key handed to the forger. -/
  pk : PublicKeyCore core
  /-- The secret key used by the signing oracle. -/
  sk : SecretKeyCore core
  /-- The signing oracle's log of queried messages and returned signatures. -/
  log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core)
  /-- The forger's message. -/
  msg : List Byte
  /-- The forger's signature. -/
  sig : GeneralScheme.SignatureCore vp core
  /-- Whether the forgery verifies. -/
  verified : Bool

/-- The EUF-CMA success bit of a transcript: the forgery verifies and its message was never
signed. -/
noncomputable def RomOutcome.wins {vp : ValidatedParams} {core : CorePrimitives vp.params}
    (o : RomOutcome vp core) : Bool :=
  letI : DecidableEq (List Byte) := Classical.decEq _
  letI : DecidableEq (GeneralScheme.SignatureCore vp core) := Classical.decEq _
  !o.log.wasQueried o.msg && o.verified

/-- A transcript wins exactly when its message is absent from the signing log and the forgery
verifies. -/
theorem RomOutcome.wins_eq_true_iff {vp : ValidatedParams} {core : CorePrimitives vp.params}
    (o : RomOutcome vp core) :
    o.wins = true ↔ o.msg ∉ o.log.map (fun e => e.1) ∧ o.verified = true := by
  simp only [RomOutcome.wins, QueryLog.wasQueried, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, QueryLog.getQ_ne_nil_iff_mem_map_fst]

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

section Counted

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-- `romGameCore` returning its whole transcript instead of the success bit. -/
@[expose] noncomputable def romGameCoreFull
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    OracleComp romSpec (RomOutcome vp core) := do
  let alg := generalAlgM (m := OracleComp romSpec) vp core
  let (pk, sk) ← alg.keygen
  let impl : QueryImpl (romSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
        (OracleComp romSpec)) :=
    (HasQuery.toQueryImpl (spec := romSpec) (m := OracleComp romSpec)).liftTarget
        (WriterT (QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp core))
          (OracleComp romSpec)) +
      alg.signingOracle pk sk
  let ((msg, sig), log) ← (simulateQ impl (adv.main pk)).run
  let verified ← alg.verify pk msg sig
  return ⟨pk, sk, log, msg, sig, verified⟩

/-- The success bit of `romGameCore` is `RomOutcome.wins` of the transcript. -/
theorem romGameCore_eq_map
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    romGameCore core adv = RomOutcome.wins <$> romGameCoreFull core adv := by
  simp only [romGameCore, romGameCoreFull, map_eq_bind_pure_comp, bind_assoc]
  exact bind_congr fun ⟨pk, sk⟩ => bind_congr fun ⟨⟨msg, sig⟩, log⟩ => by
    simp only [pure_bind, Function.comp_def, RomOutcome.wins]

variable [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

/-- The transcript of the game under the shared lazy public-hash oracle, run from the empty
cache, together with the final cache. -/
@[expose] noncomputable def romRunFull
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    ProbComp (RomOutcome vp core × PublicHash.Cache core) :=
  (simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core)
    (romGameCoreFull core adv)).run ∅

/-- The success bit of the counted experiment is `RomOutcome.wins` of the instrumented run's
transcript. -/
theorem fst_map_countedRomExperiment
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    Prod.fst <$> countedRomExperiment core adv =
      (fun z => z.1.wins) <$> romRunFull core adv := by
  unfold countedRomExperiment countedRomImpl romRunFull
  rw [← StateT.run'_map', QueryImpl.fst_map_runAdd_withAddCost, StateT.run'_eq,
    romGameCore_eq_map, simulateQ_map, StateT.run_map, Functor.map_map]

/-- The forging advantage of the counted experiment is the mass of the winning event of the
instrumented run. -/
theorem romForgeAdvantage_eq [MeasurableSpace (RomOutcome vp core × PublicHash.Cache core)]
    [DiscreteMeasurableSpace (RomOutcome vp core × PublicHash.Cache core)]
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    romForgeAdvantage core adv = 𝒟[romRunFull core adv] {z | z.1.wins = true} := by
  rw [romForgeAdvantage, fst_map_countedRomExperiment, evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
  rfl

end Counted

end SLHDSA.Security
