/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.RomTranscript
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import all HashSig.SLHDSA.Security.CountedRom

/-!
# The joint counted-and-logged random-oracle run for SLH-DSA

`HashSig.SLHDSA.Security.CountedRom`'s `countedRomExperiment` carries the public-hash query count
and discards the signing log; `HashSig.SLHDSA.Security.RomRun`'s `romRunFull` carries the whole
transcript, and with it the log, but no count.  The two query budgets `HasHashQueryBound` and
`HasSignQueryBound` are support conditions on those two different runs, so nothing relates them
until one run carries both.  `jointRomRun` is that run: the shared lazy public-hash oracle of
`romRunFull` with the query counter of `countedRomExperiment` carried alongside the cache as an
auxiliary state component.  `proj_jointRomRun_eq_romRunFull` and
`proj_jointRomRun_eq_countedRomExperiment` are equalities of `ProbComp` computations, so the
instrumentation changes neither run and both budgets become conditions on the support of the one
joint run.

`length_log_le_hashCount_of_mem_support_jointRomRun` then bounds, on every path of the joint run,
the number of signing queries by the number of public-hash queries: FIPS 205 Algorithm 19 opens
with the `H_msg` query, so every signature spends at least one query of the hash budget.

## What the relation says

The content is the implication `hasSignQueryBound_of_hasHashQueryBound`: a hash-query budget is
also a signing-query budget.  It is not an inequality between the two budget parameters.  Both
predicates are upper bounds, hence upward closed by `hasSignQueryBound_mono`, so from a signing
budget every larger number is again a signing budget while the hash budget stays put, and
`HashSigTest.SLHDSA.JointRom` refutes that reading.  The inequality that does hold is
`sInf_signBound_le_sInf_hashBound`, between the least witnesses rather than arbitrary ones.

## What the relation buys

A bound stated against a signature budget separate from the hash budget carries a soundness side
obligation: that the separated budget is a budget at all, that is, that every signing query the
signature budget counts is also charged to the hash budget.  The implication discharges exactly
that obligation, and nothing more.  It gives nothing quantitative: no statement in this module
produces a signature budget below a given hash budget, and the gain from a smaller signature
budget comes from assuming one.

## Scope

* The hash count includes key generation, signing and the final verification, not only the
  forger's own queries, because `HasHashQueryBound` does.  A signature is therefore charged for
  the honest signer's `H_msg` query, which is what makes the implication true.
* `HasHashQueryBound` is a condition on the whole support rather than a complexity assumption:
  running time, memory and private sampling are unconstrained.  No declaration in this
  repository constructs a witness for it; every consumer assumes one.
* Nothing here is probabilistic.  Every statement is an equality of `ProbComp` computations or a
  condition on a support; no mass of any event is bounded.
* Nothing here is quantum: the oracle is a classical lazily-sampled table and the count is a
  classical query count.

## Labels

Fourteen declarations.

*The joint run*: `hashCost`, `jointRomImpl`, `jointRomRun`.

*The two projections*: `proj_jointRomRun_eq_romRunFull`, `countedRomImpl_eq_withAddCost`,
`proj_jointRomRun_eq_countedRomExperiment`.

*The pathwise bound*: `le_cnt_of_mem_support_run_jointRomImpl`,
`succ_le_cnt_of_mem_support_run_jointRomImpl_sign`,
`length_log_le_hashCount_of_mem_support_jointRomRun`.

*Both budgets on the joint run*: `hashCount_le_of_hasHashQueryBound`,
`logLength_le_of_hasSignQueryBound`.

*The budget relation*: `hasSignQueryBound_of_hasHashQueryBound`, `hasSignQueryBound_mono`,
`sInf_signBound_le_sInf_hashBound`.

## References

- NIST FIPS 205, §9, Algorithms 19--20
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed]
  [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [SampleableType (Bytes vp.params.m)]

/-- The oracle family the whole experiment runs in: private sampling together with the public
hash. -/
local notation "romSpec" => unifSpec + publicHashSpec core

/-! ## The joint run -/

/-- The charge of one `romSpec` query: a public-hash query costs `1`, private sampling `0`.

*The joint run.* -/
@[expose] def hashCost : (unifSpec + publicHashSpec core).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- **The joint interpretation.**  The shared lazy public-hash oracle of `romRunFull`, with the
`hashCost` charge accumulated in an auxiliary state component beside the cache.

*The joint run.* -/
@[expose] noncomputable def jointRomImpl :
    QueryImpl romSpec (StateT (PublicHash.Cache core × ℕ) ProbComp) :=
  QueryImpl.extendState (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core)
    (fun t _ _ _ n => n + hashCost core t)

/-- **The joint run**: the whole EUF-CMA transcript — key pair, signing log, forgery, verdict —
together with the final cache and the total number of public-hash queries.

*The joint run.* -/
@[expose] noncomputable def jointRomRun
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    ProbComp (RomOutcome vp core × (PublicHash.Cache core × ℕ)) :=
  (simulateQ (jointRomImpl core) (romGameCoreFull core adv)).run (∅, 0)

/-! ## The two projections -/

/-- **Forgetting the counter recovers `romRunFull`** on the nose, as `ProbComp` computations: the
counter is a passive auxiliary and the instrumentation does not change the game.

*The two projections.* -/
theorem proj_jointRomRun_eq_romRunFull
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    Prod.map id Prod.fst <$> jointRomRun core adv = romRunFull core adv :=
  OracleComp.extendState_run_proj_eq _ _ _ _ _

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- `countedRomImpl` is the shared lazy oracle instrumented with `hashCost` in an `AddWriterT`
layer.  The body of `countedRomImpl` is not exposed, so this is what identifies its charge with
the one `jointRomImpl` carries in its state.

*The two projections.* -/
theorem countedRomImpl_eq_withAddCost :
    countedRomImpl core
      = (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core).withAddCost
          (hashCost core) := by
  unfold countedRomImpl
  rfl

/-- **Reading the counter off the joint run recovers `countedRomExperiment`**: the success bit of
the transcript paired with the final count is the counted experiment, as `ProbComp`
computations.

*The two projections.* -/
theorem proj_jointRomRun_eq_countedRomExperiment
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) :
    (fun z => (z.1.wins, z.2.2)) <$> jointRomRun core adv = countedRomExperiment core adv := by
  rw [jointRomRun, jointRomImpl, OracleComp.run_extendState_eq_map_runAdd_withAddCost,
    countedRomExperiment, countedRomImpl_eq_withAddCost, romGameCore_eq_map, simulateQ_map,
    AddWriterT.runAdd_map, StateT.run'_eq, StateT.run_map]
  simp [Functor.map_map, Prod.map]

/-! ## The pathwise bound -/

omit [SampleableType core.SkSeed] [SampleableType core.SkPrf] [SampleableType core.PkSeed] in
/-- The joint run's hash-query counter never decreases.

*The pathwise bound.* -/
theorem le_cnt_of_mem_support_run_jointRomImpl {α : Type} (oa : OracleComp romSpec α)
    (s : PublicHash.Cache core × ℕ) {z : α × (PublicHash.Cache core × ℕ)}
    (hz : z ∈ support ((simulateQ (jointRomImpl core) oa).run s)) : s.2 ≤ z.2.2 :=
  OracleComp.le_cnt_of_mem_support_run_extendState _ (hashCost core) oa s.1 s.2 hz

/-- **Signing is counted.**  FIPS 205 Algorithm 19 opens with the `H_msg` query, which `hashCost`
charges `1`, so every run of the signing oracle's program raises the joint run's hash-query
counter by at least one.

The charge `fun t _ _ _ n => n + hashCost core t` depends only on the query input, and not on the
cache, the answer or the post-state, so a cache hit and a repeated message are charged alike: the
counter counts invocations, not distinct points.

*The pathwise bound.* -/
theorem succ_le_cnt_of_mem_support_run_jointRomImpl_sign
    (pk : PublicKeyCore core) (sk : SecretKeyCore core) (t : List Byte)
    (s : PublicHash.Cache core × ℕ)
    {z : GeneralScheme.SignatureCore vp core × (PublicHash.Cache core × ℕ)}
    (hz : z ∈ support ((simulateQ (jointRomImpl core)
      ((generalAlgM (m := OracleComp romSpec) vp core).sign pk sk t)).run s)) :
    s.2 + 1 ≤ z.2.2 := by
  rw [generalAlgM_sign] at hz
  refine OracleComp.succ_le_cnt_of_mem_support_run_extendState_bind _ (hashCost core) _ _
    (fun addrnd s' n' z' hz' => ?_) s.1 s.2 hz
  exact OracleComp.succ_le_cnt_of_mem_support_run_extendState_query_bind _ (hashCost core)
    (Sum.inr (PublicHashQuery.hmsg (core.PRFmsg sk.skPrf addrnd (emptyContextMessage t))
      sk.pkSeed sk.pkRoot (emptyContextMessage t))) le_rfl _ s' n' hz'

/-- **The budget relation, pathwise.**  On every path of the joint run the number of signing
queries is at most the number of public-hash queries.

*The pathwise bound.* -/
theorem length_log_le_hashCount_of_mem_support_jointRomRun
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    {z : RomOutcome vp core × (PublicHash.Cache core × ℕ)}
    (hz : z ∈ support (jointRomRun core adv)) : z.1.log.length ≤ z.2.2 := by
  rw [jointRomRun, romGameCoreFull] at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨⟨pk, sk⟩, cₖ⟩, hk, ⟨⟨⟨msg, sig⟩, log⟩, c_f⟩, hf, ⟨verified, c_v⟩, hv, rfl⟩ := hz
  have hmid := QueryImpl.length_log_le_cnt_of_mem_support_run_add_withLogging (jointRomImpl core)
      Prod.snd (fun ob s w hw => le_cnt_of_mem_support_run_jointRomImpl core ob s hw)
      ((generalAlgM (m := OracleComp romSpec) vp core).sign pk sk)
      (fun t s w hw => succ_le_cnt_of_mem_support_run_jointRomImpl_sign core pk sk t s hw)
      (adv.main pk) hf
  have hver := le_cnt_of_mem_support_run_jointRomImpl core _ c_f hv
  dsimp only at hmid hver ⊢
  omega

/-! ## Both budgets on the joint run -/

/-- The hash budget of `HasHashQueryBound` is read off the joint run's counter.

*Both budgets on the joint run.* -/
theorem hashCount_le_of_hasHashQueryBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (qh : ℕ)
    (h : HasHashQueryBound core adv qh)
    {z : RomOutcome vp core × (PublicHash.Cache core × ℕ)}
    (hz : z ∈ support (jointRomRun core adv)) : z.2.2 ≤ qh := by
  refine h (z.1.wins, z.2.2) ?_
  rw [← proj_jointRomRun_eq_countedRomExperiment core adv, support_map]
  exact ⟨z, hz, rfl⟩

/-- The signing budget of `HasSignQueryBound` is read off the joint run's transcript.

*Both budgets on the joint run.* -/
theorem logLength_le_of_hasSignQueryBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (qs : ℕ)
    (h : HasSignQueryBound core adv qs)
    {z : RomOutcome vp core × (PublicHash.Cache core × ℕ)}
    (hz : z ∈ support (jointRomRun core adv)) : z.1.log.length ≤ qs := by
  refine h (z.1, z.2.1) ?_
  rw [← proj_jointRomRun_eq_romRunFull core adv, support_map]
  exact ⟨z, hz, rfl⟩

/-! ## The budget relation -/

/-- **A hash-query budget is also a signing-query budget**: every signing query spends at least
one query of the hash budget on its own `H_msg` call.  This implication, and not any inequality
between the two budget parameters, is the content of the relation between `HasHashQueryBound` and
`HasSignQueryBound`.

*The budget relation.* -/
theorem hasSignQueryBound_of_hasHashQueryBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) (q : ℕ)
    (h : HasHashQueryBound core adv q) : HasSignQueryBound core adv q := by
  intro w hw
  rw [← proj_jointRomRun_eq_romRunFull core adv, support_map] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact le_trans (length_log_le_hashCount_of_mem_support_jointRomRun core adv hz)
    (hashCount_le_of_hasHashQueryBound core adv q h hz)

/-- The signing budget is an upper bound, not an exact count: every larger number is again a
signing budget.

*The budget relation.* -/
theorem hasSignQueryBound_mono
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core)) {qs qs' : ℕ}
    (hle : qs ≤ qs') (h : HasSignQueryBound core adv qs) : HasSignQueryBound core adv qs' :=
  fun w hw => le_trans (h w hw) hle

/-- **The inequality that does hold between the budgets**: the least signing-query budget is at
most the least hash-query budget.  This is the quantitative reading of the relation, stated
between the least witnesses rather than between arbitrary ones.

*The budget relation.* -/
theorem sInf_signBound_le_sInf_hashBound
    (adv : unforgeableAdv (generalAlgM (m := OracleComp romSpec) vp core))
    (hne : ∃ q, HasHashQueryBound core adv q) :
    sInf {qs | HasSignQueryBound core adv qs} ≤ sInf {qh | HasHashQueryBound core adv qh} :=
  Nat.sInf_le (hasSignQueryBound_of_hasHashQueryBound core adv _ (Nat.sInf_mem hne))

end SLHDSA.Security
