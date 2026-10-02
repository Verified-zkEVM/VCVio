/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.FiatShamir.QueryBounds
public import VCVio.CryptoFoundations.FiatShamir.WithAbort

/-!
# EUF-CMA security of Fiat-Shamir with aborts

Statistical CMA-to-NMA reduction for the Fiat-Shamir-with-aborts transform,
matching Theorem 3 of Barbosa et al. (CRYPTO 2023). Instantiates
`FiatShamir.signHashQueryBound` at the with-aborts signature type and exposes
`cmaToNmaLoss` plus `euf_cma_bound` / `euf_cma_bound_perfectHVZK`.

The scheme-specific NMA-to-hard-problem reduction lives with each concrete
scheme (e.g. the ML-DSA MLWE + SelfTargetMSIS reduction).
-/

@[expose] public section

universe u v

open OracleComp OracleSpec

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}

namespace FiatShamirWithAbort

section EUF_CMA

variable [SampleableType Stmt]
variable [DecidableEq Commit] [SampleableType Chal]
variable (ids : IdenSchemeWithAbort Stmt Wit Commit PrvState Chal Resp rel)
  (hr : GenerableRelation Stmt Wit rel)
  (M : Type) [DecidableEq M] (maxAttempts : ℕ)

/-- The exact classical ROM statistical loss from the Fiat-Shamir-with-aborts
CMA-to-NMA reduction (Theorem 3, CRYPTO 2023), parameterized by the HVZK simulator
error `ζ_zk`.

The paper proves

`Adv_EUF-CMA(A) ≤ Adv_EUF-NMA(B)
  + 2·qS·(qH+1)·ε/(1-p)
  + qS·ε·(qS+1)/(2·(1-p)^2)
  + qS·ζ_zk
  + δ`

where:
- `qS`: number of signing-oracle queries
- `qH`: number of adversarial random-oracle queries
- `ε`: commitment-guessing bound
- `p`: effective abort probability
- `ζ_zk`: total-variation error of the HVZK simulator for one signing transcript
- `δ`: regularity failure probability

The `qH + 1` term comes from applying the paper's hybrid bounds to the forging
experiment, which adds one final verification query to the random oracle. -/
noncomputable def cmaToNmaLoss (qS qH : ℕ) (ε p ζ_zk δ : ℝ) (_hp : p < 1) : ℝ :=
  2 * qS * (qH + 1) * ε / (1 - p) +
  qS * ε * (qS + 1) / (2 * (1 - p) ^ 2) +
  qS * ζ_zk +
  δ

/-- The CMA-to-witness reduction of the with-aborts transform: the composite of the CMA-to-NMA
simulation, through the HVZK simulator `sim` and the commitment recovery `recover`, with the
NMA-to-witness forking reduction, as `FiatShamir.cmaReduction` composes them for the plain
transform. It is not constructed yet: a named placeholder, carried by the axiom baseline, so that
`euf_cma_bound` names the reduction it bounds. -/
noncomputable def cmaReduction
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (recover : Stmt → Chal → Resp → Commit)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort.inROM ids hr M maxAttempts))
    (qH : ℕ) : Stmt → ProbComp Wit :=
  sorry

/-- **CMA-to-NMA reduction for Fiat-Shamir with aborts (Theorem 3, CRYPTO 2023).**

For any EUF-CMA adversary `A` making at most `qS` signing-oracle queries and `qH`
random-oracle queries, the reduction `cmaReduction` finds a witness with probability at least
the advantage of `A` less the statistical loss `L`:

  `Adv^{EUF-CMA}(A) ≤ Pr[cmaReduction A finds a witness] + L`

The reduction uses:
1. The quantitative HVZK simulator `sim` to answer signing queries without the secret key
2. Commitment recoverability `recover` to map between the standard and commitment-recoverable
   variants of the signature scheme
3. Nested hybrid arguments over ROM reprogramming (accepted and rejected transcripts)

The statistical loss `L` involves the commitment guessing probability `ε`, the effective
abort probability `p_abort`, the simulator error `ζ_zk`, the regularity failure probability `δ`,
and the query bounds `qS`, `qH`; it is captured here by `cmaToNmaLoss`, with `ε`, `p_abort` and
`δ` nonnegative and `p_abort < 1`.

The scheme-specific reduction from NMA to computational assumptions (e.g., MLWE +
SelfTargetMSIS for ML-DSA) is stated separately with each scheme; see
`MLDSA.euf_cma_security`.

**WARNING: this is a placeholder statement.** Its reduction `cmaReduction` is a named placeholder
and its proof is deferred. One defect of the statement remains: `ε`, `p_abort` and `δ` are not
identified with the commitment-guessing probability, abort probability and regularity failure
probability of `ids`, which `IdenSchemeWithAbort` does not define yet; the final statement takes
them as those probabilities rather than as free parameters. -/
theorem euf_cma_bound
    (hc : ids.Complete)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (ζ_zk : ℝ)
    (hζ : 0 ≤ ζ_zk)
    (hhvzk : ids.HVZK sim (ENNReal.ofReal ζ_zk))
    (recover : Stmt → Chal → Resp → Commit)
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort.inROM ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hε : 0 ≤ ε) (hp0 : 0 ≤ p_abort) (hp : p_abort < 1)
    (hδ : 0 ≤ δ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    SignatureAlg.unforgeableAdvantage (runtime M) adv ≤
      Pr{let b ←
          hardRelationExperiment hr (cmaReduction ids hr M maxAttempts sim recover adv qH)}[
        b = true] +
        ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort ζ_zk δ hp) := by
  let _ := hc
  let _ := hζ
  let _ := hhvzk
  let _ := hcr
  let _ := hε
  let _ := hp0
  let _ := hδ
  let _ := hQ
  sorry

/-- Perfect-HVZK special case of `euf_cma_bound`, where the simulator contributes no
`qS · ζ_zk` loss term.

**WARNING: this is a placeholder statement.** It inherits the placeholder reduction and the
remaining defect of `euf_cma_bound` (`ε`, `p_abort` and `δ` as free nonnegative parameters);
see that theorem's docstring. -/
theorem euf_cma_bound_perfectHVZK
    (hc : ids.Complete)
    (sim : Stmt → ProbComp (Option (Commit × Chal × Resp)))
    (hhvzk : ids.PerfectHVZK sim)
    (recover : Stmt → Chal → Resp → Commit)
    (hcr : ids.CommitmentRecoverable recover)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort.inROM ids hr M maxAttempts))
    (qS qH : ℕ) (ε p_abort δ : ℝ) (hε : 0 ≤ ε) (hp0 : 0 ≤ p_abort) (hp : p_abort < 1)
    (hδ : 0 ≤ δ)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound M
      (S' := Option (Commit × Resp)) (oa := adv.main pk) qS qH) :
    SignatureAlg.unforgeableAdvantage (runtime M) adv ≤
      Pr{let b ←
          hardRelationExperiment hr (cmaReduction ids hr M maxAttempts sim recover adv qH)}[
        b = true] +
        ENNReal.ofReal (cmaToNmaLoss qS qH ε p_abort 0 δ hp) :=
  euf_cma_bound (ids := ids) (M := M) (maxAttempts := maxAttempts)
    (hc := hc) (sim := sim) (ζ_zk := 0) (hζ := le_rfl)
    (hhvzk := by simpa using (IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero ids sim).mp hhvzk)
    (recover := recover) (hcr := hcr) (adv := adv)
    (qS := qS) (qH := qH) (ε := ε) (p_abort := p_abort) (δ := δ) (hε := hε) (hp0 := hp0)
    (hp := hp) (hδ := hδ) (hQ := hQ)

end EUF_CMA

end FiatShamirWithAbort
