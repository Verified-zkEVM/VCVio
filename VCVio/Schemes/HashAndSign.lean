/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Relabel
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Hash-and-sign

A signature scheme for short messages `D` and a keyed hash family `H : M → D` give a signature
scheme for long messages `M`: key generation adds a hash key `s` to the public key, and a long
message is signed and verified through its digest `H.hash s msg`. If the signature scheme is secure
and the hash family is collision resistant, the composed scheme is secure: a forgery `(msg, σ)`
either verifies on a digest that no signing query produced, which is a forgery against the
short-message scheme, or shares its digest with a queried message, which is a collision of the hash.

The hash key is public, so the forger may choose its messages depending on it; the reductions
therefore sample the key and give it to the forger as part of the public key. The bound is proved
for EUF-CMA and SUF-CMA. `sigReduction` (and `strongSigReduction`) run the forger with a hash key of
their own and forward each signing query as the query on its digest; `crReduction` (and
`strongCRReduction`) run the forger with a key pair of their own and return the first logged
message whose digest collides with the forged one.

## Main definitions

- `HashAndSign.scheme` — the hash-and-sign construction.
- `HashAndSign.sigReduction`, `HashAndSign.strongSigReduction` — the forgers against the
  short-message scheme.
- `HashAndSign.crReduction`, `HashAndSign.strongCRReduction` — the keyed-CR adversaries against
  the hash family.

## Main statements

- `HashAndSign.unforgeableAdvantage_le` — the EUF-CMA advantage against `scheme` is at most the
  EUF-CMA advantage of `sigReduction` plus the keyed-CR advantage of `crReduction`.
- `HashAndSign.strongUnforgeableAdvantage_le` — the same bound for SUF-CMA.

## References

- Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd ed., §13.3
  (the hash-and-sign paradigm).
-/

public section

open OracleSpec OracleComp ENNReal CollisionResistance

namespace HashAndSign

variable {D PK SK S Kh M : Type}

/-! ## Construction -/

/-- The hash-and-sign construction: the public key pairs a public key of `sig` with a hash key, and
a long message is signed and verified through its digest. -/
@[expose] def scheme (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D) :
    SignatureAlg ProbComp M (PK × Kh) SK S where
  keygen := do
    let (pk, sk) ← sig.keygen
    let s ← H.keygen
    return ((pk, s), sk)
  sign pk sk msg := sig.sign pk.1 sk (H.hash pk.2 msg)
  verify pk msg σ := sig.verify pk.1 (H.hash pk.2 msg) σ

/-! ## Reductions -/

/-- The program of the forger against the short-message scheme: given `pk`, sample a hash key `s`,
run the long-message forger on `(pk, s)` with each signing query `msg` forwarded as the query
`H.hash s msg`, and output the digest of the forged message with the forged signature. -/
@[expose] def reductionMain (H : KeyedHashFamily Kh M D)
    (main : PK × Kh → OracleComp (unifSpec + (M →ₒ S)) (M × S)) (pk : PK) :
    OracleComp (unifSpec + (D →ₒ S)) (D × S) := do
  let s ← H.keygen
  let (msg, σ) ← (main (pk, s)).mapLens (translateLens unifSpec (H.hash s))
  return (H.hash s msg, σ)

/-- The EUF-CMA forger against the short-message scheme built from one against `scheme`. -/
@[expose] def sigReduction (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme sig H).UnforgeableAdversary) : sig.UnforgeableAdversary where
  main := reductionMain H adversary.main

/-- The SUF-CMA forger against the short-message scheme built from one against `scheme`. -/
@[expose] def strongSigReduction (sig : SignatureAlg ProbComp D PK SK S)
    (H : KeyedHashFamily Kh M D) (adversary : (scheme sig H).StrongUnforgeableAdversary) :
    sig.StrongUnforgeableAdversary where
  main := reductionMain H adversary.main

/-- The program of the keyed-CR adversary against the hash family: given the hash key `s`, sample
a key pair of `sig`, run the forger on `(pk, s)` against the honest signing oracle, and return the
forged message paired with the first logged message of the same digest
(`QueryLog.collisionCandidate`). -/
@[expose] def crReductionMain [DecidableEq M] [DecidableEq D]
    (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (main : PK × Kh → OracleComp (unifSpec + (M →ₒ S)) (M × S)) : KeyedCRAdversary Kh M :=
  fun s => do
    let (pk, sk) ← sig.keygen
    let ((msg, _), log) ← (scheme sig H).runWithSigningOracle (pk, s) sk (main (pk, s))
    return QueryLog.collisionCandidate (H.hash s) msg log

/-- The keyed-CR adversary built from an EUF-CMA forger against `scheme`. -/
@[expose] def crReduction [DecidableEq M] [DecidableEq D] (sig : SignatureAlg ProbComp D PK SK S)
    (H : KeyedHashFamily Kh M D) (adversary : (scheme sig H).UnforgeableAdversary) :
    KeyedCRAdversary Kh M :=
  crReductionMain sig H adversary.main

/-- The keyed-CR adversary built from a SUF-CMA forger against `scheme`. -/
@[expose] def strongCRReduction [DecidableEq M] [DecidableEq D]
    (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme sig H).StrongUnforgeableAdversary) : KeyedCRAdversary Kh M :=
  crReductionMain sig H adversary.main

/-! ## Simulation -/

/-- Running `reductionMain` against the honest signing oracle under `(pk, sk)` samples a hash key
`s` and runs the forger on `(pk, s)` against the signing oracle of `scheme`, with the forged message
replaced by its digest and the signing log relabelled by the hash. -/
theorem runWithSigningOracle_reductionMain (sig : SignatureAlg ProbComp D PK SK S)
    (H : KeyedHashFamily Kh M D) (main : PK × Kh → OracleComp (unifSpec + (M →ₒ S)) (M × S))
    (pk : PK) (sk : SK) :
    sig.runWithSigningOracle pk sk (reductionMain H main pk) = (do
      let s ← H.keygen
      let ((msg, σ), log) ← (scheme sig H).runWithSigningOracle (pk, s) sk (main (pk, s))
      return ((H.hash s msg, σ), QueryLog.relabel (H.hash s) log)) := by
  have htr := fun s => QueryImpl.run_simulateQ_withLogging_mapLens_translateLens ⟨sig.sign pk sk⟩
    ⟨(scheme sig H).sign (pk, s) sk⟩ (H.hash s) (fun _ => rfl) (main (pk, s))
  have hkey := QueryImpl.run_simulateQ_passthrough_add_liftM
    (QueryImpl.withLogging ⟨sig.sign pk sk⟩) H.keygen
  simp only [SignatureAlg.runWithSigningOracle_def, reductionMain, SignatureAlg.signingOracle,
    simulateQ_bind, WriterT.run_bind']
  erw [hkey]
  simp only [htr]
  simp [bind_map_left]

/-! ## The common run -/

/-- The run shared by the experiments: sample a key pair and a hash key, then run the forger on
the public key of `scheme` against its signing oracle. -/
@[expose] def forgeryRun (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (main : PK × Kh → OracleComp (unifSpec + (M →ₒ S)) (M × S)) :
    ProbComp (PK × Kh × ((M × S) × QueryLog (M →ₒ S))) := do
  let (pk, sk) ← sig.keygen
  let s ← H.keygen
  let r ← (scheme sig H).runWithSigningOracle (pk, s) sk (main (pk, s))
  return (pk, s, r)

/-- Whether the run `a` contains a collision of the hash under its key. -/
@[expose] def collides [DecidableEq M] [DecidableEq D] (H : KeyedHashFamily Kh M D)
    (a : PK × Kh × ((M × S) × QueryLog (M →ₒ S))) : Bool :=
  QueryLog.hasCollision (H.hash a.2.1) a.2.2.1.1 a.2.2.2

/-- The keyed-CR experiment against `crReductionMain` is the common run followed by the collision
test. -/
theorem evalDist_keyedCRExperiment_crReductionMain [DecidableEq M] [DecidableEq D]
    (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (main : PK × Kh → OracleComp (unifSpec + (M →ₒ S)) (M × S)) :
    𝒟[keyedCRExperiment H (crReductionMain sig H main)] =
      𝒟[forgeryRun sig H main >>= fun a => pure (collides H a)] := by
  simp only [keyedCRExperiment, crReductionMain, bind_pure_comp, ne_eq, Bool.decide_and, decide_not,
    map_bind, Functor.map_map, forgeryRun, collides, QueryLog.hasCollision]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

/-! ## Security -/

/-- **Hash-and-sign, existential unforgeability.** The EUF-CMA advantage against the hash-and-sign
construction is at most the EUF-CMA advantage of `sigReduction` against the short-message scheme
plus the keyed-CR advantage of `crReduction` against the hash family. -/
theorem unforgeableAdvantage_le [DecidableEq M] [DecidableEq D]
    (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme sig H).UnforgeableAdversary) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adversary ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (sigReduction sig H adversary) +
        keyedCRAdvantage H (crReduction sig H adversary) := by
  have hscheme : SignatureAlg.unforgeableExperiment adversary =
      forgeryRun sig H adversary.main >>= fun a => do
        let v ← sig.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!a.2.2.2.wasQueried a.2.2.1.1 && v) := by
    simp only [SignatureAlg.unforgeableExperiment, scheme, bind_pure_comp, bind_assoc,
      bind_map_left, forgeryRun]
    congr!
  have hsig : SignatureAlg.unforgeableExperiment (sigReduction sig H adversary) =
      forgeryRun sig H adversary.main >>= fun a => do
        let v ← sig.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!(QueryLog.relabel (H.hash a.2.1) a.2.2.2).wasQueried (H.hash a.2.1 a.2.2.1.1) &&
          v) := by
    simp only [SignatureAlg.unforgeableExperiment, sigReduction, runWithSigningOracle_reductionMain,
      bind_pure_comp, bind_assoc, bind_map_left, forgeryRun]
    congr!
  rw [SignatureAlg.unforgeableAdvantage, SignatureAlg.unforgeableAdvantage,
    ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist, hscheme, hsig,
    keyedCRAdvantage, crReduction, evalDist_keyedCRExperiment_crReductionMain]
  refine OracleComp.evalDist_bind_and_le_add_of_not_bad _ _ (collides H) _ _
    fun ⟨pk, s, ⟨msg, σ⟩, log⟩ _ hc hw => ?_
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw ⊢
  cases hmem : (QueryLog.relabel (H.hash s) log).wasQueried (H.hash s msg)
  · rfl
  · rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_true_eq] at hmem
    rw [QueryLog.wasQueried_eq_decide_mem_map_fst] at hw
    exact absurd (QueryLog.mem_map_fst_of_mem_map_fst_relabel _ _ _ hc hmem) (by simpa using hw)

/-- **Hash-and-sign, strong unforgeability.** The SUF-CMA advantage against the hash-and-sign
construction is at most the SUF-CMA advantage of `strongSigReduction` against the short-message
scheme plus the keyed-CR advantage of `strongCRReduction` against the hash family. -/
theorem strongUnforgeableAdvantage_le [DecidableEq M] [DecidableEq D]
    (sig : SignatureAlg ProbComp D PK SK S) (H : KeyedHashFamily Kh M D)
    (adversary : (scheme sig H).StrongUnforgeableAdversary) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adversary ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
          (strongSigReduction sig H adversary) +
        keyedCRAdvantage H (strongCRReduction sig H adversary) := by
  classical
  have hscheme : SignatureAlg.strongUnforgeableExperiment adversary =
      forgeryRun sig H adversary.main >>= fun a => do
        let v ← sig.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!SignatureAlg.signingLogContains a.2.2.2 a.2.2.1.1 a.2.2.1.2 && v) := by
    simp only [SignatureAlg.strongUnforgeableExperiment, scheme, bind_pure_comp, bind_assoc,
      bind_map_left, forgeryRun]
    congr!
  have hsig : SignatureAlg.strongUnforgeableExperiment (strongSigReduction sig H adversary) =
      forgeryRun sig H adversary.main >>= fun a => do
        let v ← sig.verify a.1 (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2
        return (!SignatureAlg.signingLogContains (QueryLog.relabel (H.hash a.2.1) a.2.2.2)
          (H.hash a.2.1 a.2.2.1.1) a.2.2.1.2 && v) := by
    simp only [SignatureAlg.strongUnforgeableExperiment, strongSigReduction,
      runWithSigningOracle_reductionMain, bind_pure_comp, bind_assoc, bind_map_left, forgeryRun]
    congr!
  rw [SignatureAlg.strongUnforgeableAdvantage, SignatureAlg.strongUnforgeableAdvantage,
    ProbCompRuntime.probComp_evalDist, ProbCompRuntime.probComp_evalDist, hscheme, hsig,
    keyedCRAdvantage, strongCRReduction, evalDist_keyedCRExperiment_crReductionMain]
  refine OracleComp.evalDist_bind_and_le_add_of_not_bad _ _ (collides H) _ _
    fun ⟨pk, s, ⟨msg, σ⟩, log⟩ _ hc hw => ?_
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hw ⊢
  cases hmem : SignatureAlg.signingLogContains (QueryLog.relabel (H.hash s) log) (H.hash s msg) σ
  · rfl
  · simp only [SignatureAlg.signingLogContains, decide_eq_true_eq] at hmem hw
    exact absurd (QueryLog.mem_of_mem_relabel _ _ _ _ hc hmem) (by simpa using hw)

end HashAndSign
