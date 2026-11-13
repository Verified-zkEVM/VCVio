/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme

/-!
# Full-range signing interactions

Projecting the full-range secret preserves the actual common signing handler, adaptive interaction
and the entire returned strong-unforgeability measure, including failed and repeated requests.
-/

public section

namespace GXMSS.Interval

open SyncSignatureUnforgeability IncomparableEncoding OracleSpec

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The signing handlers agree after projecting a full-range interval secret. Used epochs
still reject before calling either signer, and a failed fresh request is recorded in both. -/
theorem signingOracle_full [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H h v (GXMSS.IntervalMerkle.Interval.full h)) :
    signingOracle (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) sk =
      signingOracle (GXMSS.scheme hash enc K) (projectSecret sk) := by
  have hsign : (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)).sign sk =
      (GXMSS.scheme hash enc K).sign (projectSecret sk) := by
    funext ep msg
    exact sign_full hash enc K sk ep msg
  change signingKernelOracle _ = signingKernelOracle _
  rw [hsign]

/-- Full-range interval interaction and complete interaction agree as oracle programs,
including duplicate requests and fresh requests whose signer returns failure. -/
theorem interaction_full [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (adv : Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    interaction (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) adv =
      interaction (GXMSS.scheme hash enc K) adv := by
  unfold interaction ExperimentResult
  simp only [scheme, GXMSS.scheme, keygen, GXMSS.keygen,
    GXMSS.IntervalMerkle.sampleFillers_full, keys, GXMSS.keys,
    GXMSS.IntervalMerkle.root_full, monad_norm]
  congr 1
  funext pp
  congr 1
  funext starts
  let skI := (keys hash (GXMSS.IntervalMerkle.Interval.full h) pp starts
    (fun x => isEmptyElim x)).2
  let skB := (GXMSS.keys hash pp starts).2
  have hs : signingOracle (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) skI =
      signingOracle (GXMSS.scheme hash enc K) skB := by
    simpa [skI, skB, keys, GXMSS.keys, projectSecret] using
      signingOracle_full hash enc K skI
  have hinner : (simulateQ
      ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (History (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) ProbComp) +
        signingOracle (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) skI)
      (adv.forge (GXMSS.keys hash pp starts).1)).run emptyHistory =
    (simulateQ
      ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (History (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) ProbComp) +
        signingOracle (GXMSS.scheme hash enc K) skB)
      (adv.forge (GXMSS.keys hash pp starts).1)).run emptyHistory := by
    rw [hs]
  exact congrArg (fun run => run >>= pure ∘ Prod.mk
    ({ root := hash.merkleRoot pp (GXMSS.endpoints hash pp starts), seed := pp } :
      GXMSS.PublicKey PP H)) hinner

/-- The full-range strong SUF-CMA experiments have equal entire returned Boolean measures.
No positivity or query-bound premise is needed for this structural correspondence. -/
theorem strongUnforgeableExp_full [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (runtime : ProbCompRuntime ProbComp)
    (adv : Adversary unifSpec (GXMSS.PublicKey PP H)
      (Fin (2 ^ h)) M (GXMSS.Signature R H h v)) :
    strongUnforgeableExp (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) runtime adv =
      strongUnforgeableExp (GXMSS.scheme hash enc K) runtime adv := by
  unfold strongUnforgeableExp outputMeasure
  have hv : strongValid (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) =
      strongValid (GXMSS.scheme hash enc K) := by
    funext out
    simp [strongValid, scheme, GXMSS.scheme, verify_eq_base]
  rw [hv, interaction_full]

end GXMSS.Interval
