/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.MacAlg
public import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Relabel
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Hash-and-MAC

A MAC for short messages `D` and a keyed hash family `H : M → D` give a MAC for long messages `M`:
the key is a MAC key `k` together with a hash key `s`, and the tag of `msg` is the tag of
`H.hash s msg` under `k`. If the MAC is secure and the hash family is collision resistant, the
composed MAC is secure: a forgery `(msg, τ)` either verifies on a digest that no tagging query
produced, which is a forgery against the MAC, or shares its digest with a queried message, which is
a collision of the hash.

The bound is proved for both forgery notions of `MacAlg`, with the same two reductions:
`macReduction` runs the forger with a hash key of its own and forwards each tagging query as the
query on its digest, and `crReduction` runs the forger with a MAC key of its own and returns the
first logged message whose digest collides with the forged one.

## Main definitions

- `HashAndMac.scheme` — the hash-and-MAC construction.
- `HashAndMac.macReduction` — the forger against the short-message MAC.
- `HashAndMac.forgeryRun` — the run of the forger shared by the three experiments.
- `HashAndMac.crReduction` — the keyed-CR adversary against the hash family.

## Main statements

- `HashAndMac.strongUnforgeableAdvantage_le` — the SUF-CMA advantage against `scheme` is at most
  the SUF-CMA advantage of `macReduction` plus the keyed-CR advantage of `crReduction`.
- `HashAndMac.unforgeableAdvantage_le` — the same bound for UF-CMA.

## References

- [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §8.2, Theorem 8.1]
  (https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
- Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd ed., §6.3.1
  (hash-and-MAC).
-/

public section

open OracleSpec OracleComp ENNReal CollisionResistance

namespace HashAndMac

variable {D K T Kh M : Type}

/-! ## Construction -/

/-- The hash-and-MAC construction: the key pairs a MAC key with a hash key, and a long message is
tagged and verified through its digest. -/
@[expose] def scheme (mac : MacAlg ProbComp D K T) (H : KeyedHashFamily Kh M D) :
    MacAlg ProbComp M (K × Kh) T where
  keygen := do
    let k ← mac.keygen
    let s ← H.keygen
    return (k, s)
  tag key msg := mac.tag key.1 (H.hash key.2 msg)
  verify key msg τ := mac.verify key.1 (H.hash key.2 msg) τ

/-! ## Reductions -/

/-- The forger against the short-message MAC: sample a hash key, run the long-message forger with
each tagging query `msg` forwarded as the query `H.hash s msg`, and output the digest of the forged
message with the forged tag. -/
@[expose] def macReduction (mac : MacAlg ProbComp D K T) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme mac H).UnforgeableAdversary) : mac.UnforgeableAdversary where
  main := do
    let s ← H.keygen
    let (msg, τ) ← adversary.main.mapLens (translateLens unifSpec (H.hash s))
    return (H.hash s msg, τ)

/-- The keyed-CR adversary against the hash family: given the hash key, sample a MAC key, run the
forger against the honest tagging oracle, and return the forged message paired with the first logged
message of the same digest (`QueryLog.collisionCandidate`). -/
@[expose] def crReduction [DecidableEq M] [DecidableEq D] (mac : MacAlg ProbComp D K T)
    (H : KeyedHashFamily Kh M D) (adversary : (scheme mac H).UnforgeableAdversary) :
    KeyedCRAdversary Kh M := fun s => do
  let k ← mac.keygen
  let ((msg, _), log) ← (scheme mac H).runWithTaggingOracle (k, s) adversary.main
  return QueryLog.collisionCandidate (H.hash s) msg log

/-! ## Simulation -/

/-- Running `macReduction` against the honest tagging oracle under `k` samples a hash key `s` and
runs the forger against the tagging oracle of `scheme` under `(k, s)`, with the forged message
replaced by its digest and the tagging log relabelled by the hash. -/
theorem runWithTaggingOracle_macReduction (mac : MacAlg ProbComp D K T)
    (H : KeyedHashFamily Kh M D) (adversary : (scheme mac H).UnforgeableAdversary) (k : K) :
    mac.runWithTaggingOracle k (macReduction mac H adversary).main = (do
      let s ← H.keygen
      let ((msg, τ), log) ← (scheme mac H).runWithTaggingOracle (k, s) adversary.main
      return ((H.hash s msg, τ), QueryLog.relabel (H.hash s) log)) := by
  have htr := fun s => QueryImpl.run_simulateQ_withLogging_mapLens_translateLens ⟨mac.tag k⟩
    ⟨(scheme mac H).tag (k, s)⟩ (H.hash s) (fun _ => rfl) adversary.main
  have hkey := QueryImpl.run_simulateQ_passthrough_add_liftM (QueryImpl.withLogging ⟨mac.tag k⟩)
    H.keygen
  simp only [MacAlg.runWithTaggingOracle_def, macReduction, MacAlg.taggingOracle, simulateQ_bind,
    WriterT.run_bind']
  erw [hkey]
  simp only [htr]
  simp [bind_map_left]

/-! ## The common run

All three experiments in the security bound are, in distribution, the same run of the forger
followed by different tests. -/

/-- The run shared by the three experiments: sample a MAC key and a hash key, then run the forger
against the tagging oracle of `scheme`. -/
@[expose] def forgeryRun (mac : MacAlg ProbComp D K T) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme mac H).UnforgeableAdversary) :
    ProbComp (K × Kh × ((M × T) × QueryLog (M →ₒ T))) := do
  let k ← mac.keygen
  let s ← H.keygen
  let r ← (scheme mac H).runWithTaggingOracle (k, s) adversary.main
  return (k, s, r)

/-- Whether the run `a` contains a collision of the hash under its key: a logged message that
differs from the forged one and has the same digest (`QueryLog.hasCollision`). -/
@[expose] def collides [DecidableEq M] [DecidableEq D] (H : KeyedHashFamily Kh M D)
    (a : K × Kh × ((M × T) × QueryLog (M →ₒ T))) : Bool :=
  QueryLog.hasCollision (H.hash a.2.1) a.2.2.1.1 a.2.2.2

/-- The keyed-CR experiment against `crReduction` is the common run followed by the collision
test. -/
theorem evalDist_keyedCRExperiment_crReduction [DecidableEq M] [DecidableEq D]
    (mac : MacAlg ProbComp D K T) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme mac H).UnforgeableAdversary) :
    𝒟[keyedCRExperiment H (crReduction mac H adversary)] =
      𝒟[forgeryRun mac H adversary >>= fun a => pure (collides H a)] := by
  simp only [keyedCRExperiment, crReduction, bind_pure_comp, ne_eq, Bool.decide_and, decide_not,
    map_bind, Functor.map_map, forgeryRun, collides, QueryLog.hasCollision]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-! ## Security -/

/-- **Hash-and-MAC, strong unforgeability.** The SUF-CMA advantage against the hash-and-MAC
construction is at most the SUF-CMA advantage of `macReduction` against the short-message MAC plus
the keyed-CR advantage of `crReduction` against the hash family. -/
theorem strongUnforgeableAdvantage_le [DecidableEq M] [DecidableEq D] [DecidableEq T]
    (mac : MacAlg ProbComp D K T) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme mac H).UnforgeableAdversary) :
    MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adversary ≤
      MacAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
          (macReduction mac H adversary) +
        keyedCRAdvantage H (crReduction mac H adversary) := by
  have hscheme : MacAlg.strongUnforgeableExperiment adversary =
      forgeryRun mac H adversary >>= fun a => do
        let v ← mac.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!MacAlg.taggingLogContains a.2.2.2 a.2.2.1.1 a.2.2.1.2 && v) := by
    simp [MacAlg.strongUnforgeableExperiment, forgeryRun, scheme]
  have hmac : MacAlg.strongUnforgeableExperiment (macReduction mac H adversary) =
      forgeryRun mac H adversary >>= fun a => do
        let v ← mac.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!MacAlg.taggingLogContains (QueryLog.relabel (H.hash a.2.1) a.2.2.2)
          (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2 && v) := by
    simp [MacAlg.strongUnforgeableExperiment, runWithTaggingOracle_macReduction, forgeryRun]
  rw [MacAlg.strongUnforgeableAdvantage, MacAlg.strongUnforgeableAdvantage,
    ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist, hscheme, hmac,
    keyedCRAdvantage, evalDist_keyedCRExperiment_crReduction]
  refine OracleComp.evalDist_bind_and_le_add_of_not_bad _ _ (collides H) _ _
    fun ⟨k, s, ⟨msg, τ⟩, log⟩ _ hc hw => ?_
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw ⊢
  cases hmem : MacAlg.taggingLogContains (QueryLog.relabel (H.hash s) log) (H.hash s msg) τ
  · rfl
  · simp only [MacAlg.taggingLogContains, decide_eq_true_eq] at hmem hw
    exact absurd (QueryLog.mem_of_mem_relabel _ _ _ _ hc hmem) (by simpa using hw)

/-- **Hash-and-MAC, unforgeability.** The UF-CMA advantage against the hash-and-MAC construction is
at most the UF-CMA advantage of `macReduction` against the short-message MAC plus the keyed-CR
advantage of `crReduction` against the hash family. -/
theorem unforgeableAdvantage_le [DecidableEq M] [DecidableEq D]
    (mac : MacAlg ProbComp D K T) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme mac H).UnforgeableAdversary) :
    MacAlg.unforgeableAdvantage ProbCompRuntime.probComp adversary ≤
      MacAlg.unforgeableAdvantage ProbCompRuntime.probComp (macReduction mac H adversary) +
        keyedCRAdvantage H (crReduction mac H adversary) := by
  have hscheme : MacAlg.unforgeableExperiment adversary =
      forgeryRun mac H adversary >>= fun a => do
        let v ← mac.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!a.2.2.2.wasQueried a.2.2.1.1 && v) := by
    simp [MacAlg.unforgeableExperiment, forgeryRun, scheme]
  have hmac : MacAlg.unforgeableExperiment (macReduction mac H adversary) =
      forgeryRun mac H adversary >>= fun a => do
        let v ← mac.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!(QueryLog.relabel (H.hash a.2.1) a.2.2.2).wasQueried (H.hash a.2.1 a.2.2.1.1) &&
          v) := by
    simp [MacAlg.unforgeableExperiment, runWithTaggingOracle_macReduction, forgeryRun]
  rw [MacAlg.unforgeableAdvantage, MacAlg.unforgeableAdvantage,
    ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist, hscheme, hmac,
    keyedCRAdvantage, evalDist_keyedCRExperiment_crReduction]
  refine OracleComp.evalDist_bind_and_le_add_of_not_bad _ _ (collides H) _ _
    fun ⟨k, s, ⟨msg, τ⟩, log⟩ _ hc hw => ?_
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw ⊢
  cases hmem : (QueryLog.relabel (H.hash s) log).wasQueried (H.hash s msg)
  · rfl
  · rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq] at hmem
    rw [QueryLog.wasQueried_eq_decide_mem_map_fst] at hw
    exact absurd (QueryLog.mem_map_fst_of_mem_map_fst_relabel _ _ _ hc hmem) (by simpa using hw)

end HashAndMac
