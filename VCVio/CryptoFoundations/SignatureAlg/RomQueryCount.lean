/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Tagged
public import VCVio.OracleComp.QueryTracking.QueryBound.Counter
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# Counting an adversary's hash queries in the random oracle model

A signature scheme in the random oracle model runs over `unifSpec + hs`: private uniform sampling
and a hash oracle `hs`. Its unforgeability adversary additionally holds a signing oracle, so its
queries are private samples, hash queries (`IsHashQuery`) and signing queries (`IsSignQuery`).
`UnforgeableAdversary.RomQueryBound adv qh qs` bounds the last two on every path of the
adversary's own program, for every public key. It says nothing about the queries key generation,
signing and verification make on the adversary's behalf.

The adversary's hash queries are nonetheless counted on every run of the experiment. The
*tagged experiment* `taggedUnforgeableExperiment adv` runs the scheme tagged `false` and the
adversary tagged `true`, and `forgerCountingRomImpl hs` answers it through `romImpl hs` while
counting the hash queries tagged `true`, cache hits included:

* `map_run_forgerCountingRomImpl`: dropping the counter gives the run of the unforgeability
  experiment under `romImpl hs`, from the same cache.
* `forgerCount_le_of_mem_support_run`: on every outcome, the counter is at most the adversary's
  hash budget.
-/

public section

open OracleSpec OracleComp QueryImpl

namespace SignatureAlg

variable {ι : Type} {hs : OracleSpec ι} {M PK SK S : Type}

/-- A query of an unforgeability adversary in the random oracle model to the hash oracle, as
opposed to private sampling or the signing oracle. -/
@[expose] def IsHashQuery : ((unifSpec + hs) + (M →ₒ S)).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- A query of an unforgeability adversary to the signing oracle. -/
@[expose] def IsSignQuery : ((unifSpec + hs) + (M →ₒ S)).Domain → Prop
  | .inr _ => True
  | _ => False

instance : DecidablePred (IsHashQuery (hs := hs) (M := M) (S := S)) := by
  rintro ((_ | _) | _) <;> simp only [IsHashQuery] <;> infer_instance

instance : DecidablePred (IsSignQuery (hs := hs) (M := M) (S := S)) := by
  rintro ((_ | _) | _) <;> simp only [IsSignQuery] <;> infer_instance

/-- The adversary makes, on every path of its program and for every public key, at most `qh`
hash queries and at most `qs` signing queries. -/
@[expose] def UnforgeableAdversary.RomQueryBound
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) (qh qs : ℕ) : Prop :=
  ∀ pk, IsQueryBoundP (adv.main pk) (IsHashQuery (hs := hs) (M := M) (S := S)) qh ∧
    IsQueryBoundP (adv.main pk) (IsSignQuery (hs := hs) (M := M) (S := S)) qs

/-- A tagged query that is a hash query issued by the adversary, tagged `true`. -/
@[expose] def IsForgerHashQuery : Bool × (unifSpec + hs).Domain → Prop
  | (true, .inr _) => True
  | _ => False

instance : DecidablePred (IsForgerHashQuery (hs := hs)) := by
  rintro ⟨_ | _, _ | _⟩ <;> simp only [IsForgerHashQuery] <;> infer_instance

variable [DecidableEq ι] [∀ t, SampleableType (hs.Range t)]

/-- The random oracle model on the tagged interface, with a counter of the hash queries tagged
`true`. Every such query adds one, whether or not its answer is cached. -/
noncomputable def forgerCountingRomImpl (hs : OracleSpec ι) [∀ t, SampleableType (hs.Range t)] :
    QueryImpl ((unifSpec + hs).tagged Bool) (StateT (hs.QueryCache × ℕ) ProbComp) :=
  ((romImpl hs) ∘ₛ untag).extendState fun kt _ _ _ c =>
    c + if IsForgerHashQuery (hs := hs) kt then 1 else 0

/-- The unforgeability experiment with the scheme's queries tagged `false` and the adversary's
ambient queries tagged `true`. -/
noncomputable abbrev taggedUnforgeableExperiment
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) : OracleComp ((unifSpec + hs).tagged Bool) Bool :=
  unforgeableExperiment (sigAlg := sigAlg.map (simulateQ' (tagWith false)))
    (adv.mapOracles (tagWith true))

/-- Dropping the counter of the counted tagged run gives the run of the unforgeability experiment
in the random oracle model. -/
theorem map_run_forgerCountingRomImpl
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (adv : UnforgeableAdversary sigAlg) (cache : hs.QueryCache) :
    Prod.map id Prod.fst <$>
        (simulateQ (forgerCountingRomImpl hs) (taggedUnforgeableExperiment adv)).run (cache, 0) =
      (simulateQ (romImpl hs) (unforgeableExperiment adv)).run cache := by
  rw [forgerCountingRomImpl, extendState_run_proj_eq, QueryImpl.simulateQ_compose,
    simulateQ_untag_unforgeableExperiment_tagWith]

/-- **The adversary's hash queries, counted on every run.** If the adversary makes at most `qh`
hash queries on every path of its program, then on every outcome of the counted tagged run the
counter is at most `qh`. -/
theorem forgerCount_le_of_mem_support_run
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {adv : UnforgeableAdversary sigAlg} {qh : ℕ}
    (hadv : ∀ pk, IsQueryBoundP (adv.main pk) (IsHashQuery (hs := hs) (M := M) (S := S)) qh)
    {cache : hs.QueryCache} {z : Bool × hs.QueryCache × ℕ}
    (hz : z ∈ support
      ((simulateQ (forgerCountingRomImpl hs) (taggedUnforgeableExperiment adv)).run (cache, 0))) :
    z.2.2 ≤ qh := by
  have hq := isQueryBoundP_unforgeableExperiment_tagWith (k₀ := false) (k₁ := true)
    (q := IsForgerHashQuery (hs := hs)) (by rintro (_ | _) <;> simp [IsForgerHashQuery])
    (by rintro (_ | _) h <;> simp_all [IsForgerHashQuery, IsHashQuery]) hadv
  simpa using IsQueryBoundP.cnt_le_of_mem_support_run_extendState _
    (fun _ _ _ _ _ => le_rfl) hq hz

end SignatureAlg
