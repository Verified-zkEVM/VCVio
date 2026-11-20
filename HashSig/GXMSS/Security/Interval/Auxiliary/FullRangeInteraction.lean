/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
import all HashSig.GXMSS.Interval.Scheme
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg

/-! # FullRangeInteraction

Generalized XMSS definitions and proved laws.
-/

public section

namespace GXMSS.Interval

open SyncSignatureUnforgeability Encoding OracleSpec

variable {PP T X H M R : Type} {h w v : ℕ}

/-- The signing handlers agree after projecting a full-range interval secret. Used epochs
still reject before calling either signer, and a failed fresh request is recorded in both. -/
theorem signingOracle_full [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w)) (K : ℕ)
    (sk : SecretKey PP H h v (GXMSS.IntervalMerkle.Interval.full h)) :
    signingOracle (scheme hash enc K (GXMSS.IntervalMerkle.Interval.full h)) sk =
      signingOracle (GXMSS.scheme hash enc K) (projectSecret sk) := by
  funext query history
  rcases query with ⟨ep, msg⟩
  by_cases hh : history ep = none
  · simp [signingOracle, hh, scheme, GXMSS.scheme, sign_full, projectSecret]
  · cases hx : history ep with
    | none => exact (hh hx).elim
    | some entry => simp [signingOracle, hx]

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
