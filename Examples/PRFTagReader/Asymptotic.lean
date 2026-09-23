/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.UnlinkReduction
public import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Asymptotic Unlinkability

Paper-shaped packaging of the tag/reader unlinkability bound. For a security-parameter-indexed
family of PRF tag/reader instances whose two derived PRF schemes are asymptotically secure and
whose nonce/digest spaces grow superpolynomially, every polynomial-query adversary family has
negligible unlinkability advantage.

## Framework idiom

The advantages `unlinkabilityAdvantage` and `PRFScheme.prfAdvantage` are `ℝ≥0∞`-valued, as is
the asymptotic-security vocabulary of `VCVio.CryptoFoundations.Asymptotics.{Negligible,Security}`,
so the hypotheses and the headline are plain `negligible` statements over a `ℕ`-indexed instance
family. The concrete bound is `ℝ≥0∞`-valued too, and its summands combine through
`negligible_add`.

## Base bound

The base is the bound `unlinkabilityAdvantage_le_two_prf_plus_collision`, stated for
the concrete reductions `unlinkToMultiplePRFReduction` and `unlinkToSinglePRFReduction` applied to
the adversary.

## Hypotheses of the headline

* PRF asymptotic security: the multiple- and single-session PRF advantage of *each* concrete
  reduction family is negligible. The protocol genuinely uses two PRF schemes
  (`multiplePRFScheme`, `singlePRFScheme`), so two independent assumptions are honest.
* Superpolynomial growth of `|Nonce λ|` and `|Digest λ|`, phrased as negligibility of their
  reciprocals.
* Polynomial query / instance bounds: `qReader λ`, `qTag λ`, `|TagId λ|`, and `sessionsPerTag λ`
  are each bounded by a fixed polynomial in `λ`. The cell-count slack
  `qReader · |TagId| · sessionsPerTag / |Digest|` forces the *numerator* to be polynomial, so the
  polynomial bounds on `|TagId λ|` and `sessionsPerTag λ` are real modeling assumptions, surfaced
  explicitly.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Filter

namespace PRFTagReader

/-! ## Security-parameter-indexed instance family -/

/-- A security-parameter-indexed family of tag/reader instances. For each `λ` it carries the slot
budget `sessionsPerTag λ` and the keyed-hash packaging `prfs λ` over the per-`λ` carrier types.
The carrier types and their instances are supplied as section variables on the asymptotic theorem;
this structure bundles only the per-`λ` data the concrete unlinkability bound consumes. -/
structure AsymptoticInstance
    (TagId Nonce Digest K : ℕ → Type) (sessionsPerTag : ℕ → ℕ) where
  /-- The keyed-hash packaging at each security parameter. -/
  prfs : (lam : ℕ) → TagReaderPRFs (K lam) (TagId lam) (Nonce lam) (Digest lam) (sessionsPerTag lam)

namespace AsymptoticInstance

variable {TagId Nonce Digest K : ℕ → Type}
  [∀ lam, DecidableEq (TagId lam)] [∀ lam, Fintype (TagId lam)]
  [∀ lam, DecidableEq (Nonce lam)] [∀ lam, SampleableType (Nonce lam)] [∀ lam, Fintype (Nonce lam)]
  [∀ lam, DecidableEq (Digest lam)] [∀ lam, SampleableType (Digest lam)]
  [∀ lam, Fintype (Digest lam)]
  {sessionsPerTag : ℕ → ℕ} [∀ lam, NeZero (sessionsPerTag lam)]

/-- **Asymptotic unlinkability.** For a security-parameter-indexed family of PRF tag/reader
instances, suppose:

* both derived PRF families are asymptotically secure — the multiple- and single-session PRF
  advantage of the concrete reduction of the adversary is negligible;
* the nonce and digest spaces grow superpolynomially — `(|Nonce λ|)⁻¹` and `(|Digest λ|)⁻¹` are
  negligible;
* the adversary is a polynomial-query family and the instance parameters are polynomially bounded —
  `qReader`, `qTag`, `|TagId|`, and `sessionsPerTag` are each bounded by a fixed polynomial in `λ`.

Then the unlinkability advantage `unlinkabilityAdvantage` is negligible. -/
theorem negligible_unlinkabilityAdvantage
    (inst : AsymptoticInstance TagId Nonce Digest K sessionsPerTag)
    (adversary : (lam : ℕ) → UnlinkAdversary (TagId lam) (Nonce lam) (Digest lam))
    (qReader qTag : ℕ → ℕ)
    (hqReader : ∀ lam, OracleComp.IsQueryBoundP (adversary lam) (·.isRight) (qReader lam))
    (hqTag : ∀ lam, OracleComp.IsQueryBoundP (adversary lam) (·.isLeft) (qTag lam))
    -- PRF asymptotic security of the two named reductions:
    (hPRFmulti : negligible (fun lam =>
      (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam)))))
    (hPRFsingle : negligible (fun lam =>
      (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam)))))
    -- Superpolynomial growth of the nonce and digest spaces:
    (hNonce : negligible (fun lam => (Fintype.card (Nonce lam) : ℝ≥0∞)⁻¹))
    (hDigest : negligible (fun lam => (Fintype.card (Digest lam) : ℝ≥0∞)⁻¹))
    -- Polynomial bounds on the query counts and instance parameters:
    (pReader pTag pTagId pSessions : Polynomial ℕ)
    (hpReader : ∀ lam, qReader lam ≤ pReader.eval lam)
    (hpTag : ∀ lam, qTag lam ≤ pTag.eval lam)
    (hpTagId : ∀ lam, Fintype.card (TagId lam) ≤ pTagId.eval lam)
    (hpSessions : ∀ lam, sessionsPerTag lam ≤ pSessions.eval lam) :
    negligible (fun lam => unlinkabilityAdvantage (inst.prfs lam) (adversary lam)) := by
  classical
  -- Negligibility of the collision term: bounded by `sessionsPerTag² · |TagId| / |Nonce|`.
  have hCollision : negligible (fun lam =>
      𝒟[(fun z : Bool × MultipleBadState (TagId lam) (Nonce lam) (Digest lam)
          (sessionsPerTag lam) => z.2.2.bad) <$>
        (simulateQ (multipleBadQueryImpl (TagId lam) (Nonce lam) (Digest lam)
          (sessionsPerTag lam)) (adversary lam)).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)] {true}) := by
    refine negligible_of_le (g := fun lam => ENNReal.ofReal
      (((sessionsPerTag lam ^ 2 * Fintype.card (TagId lam) : ℕ) : ℝ) /
        (Fintype.card (Nonce lam) : ℝ))) (fun lam => ?_)
      (negligible_ofReal_natDiv_of_poly_bound (g := fun lam =>
        sessionsPerTag lam ^ 2 * Fintype.card (TagId lam))
        (p := pSessions ^ 2 * pTagId) hNonce (fun lam => ?_))
    · let : MeasurableSpace (Nonce lam) := ⊤
      have hmax : ∀ nonce : Nonce lam,
          (Pr{let n ← $ᵗ Nonce lam}[n = nonce]).toReal ≤ (Fintype.card (Nonce lam) : ℝ)⁻¹ := by
        intro nonce
        simp only [prEvent_eq_evalDist_singleton, SampleableType.evalDist_uniformSample_singleton,
          ENNReal.toReal_inv, ENNReal.toReal_natCast, le_refl]
      refine (ENNReal.le_ofReal_iff_toReal_le (MeasureTheory.measure_ne_top _ _)
        (by positivity)).2 ?_
      simpa only [div_eq_mul_inv] using multipleBad_bad_le_sessionCollisionBound
        (sessionsPerTag := sessionsPerTag lam) (adversary lam) _ hmax
    · rw [Polynomial.eval_mul, Polynomial.eval_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (hpSessions lam) 2) (hpTagId lam)
  -- Negligibility of each unconditional slack term.
  have hSlack1 : negligible (fun lam =>
      ((qReader lam * Fintype.card (TagId lam) : ℕ) : ℝ≥0∞) /
        (Fintype.card (Digest lam) : ℝ≥0∞)) := by
    simpa only [div_eq_mul_inv] using negligible_natMul_of_poly_bound hDigest
      (g := fun lam => qReader lam * Fintype.card (TagId lam)) (p := pReader * pTagId)
      (fun lam => by rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hpReader lam) (hpTagId lam))
  have hSlack2 : negligible (fun lam =>
      ((qReader lam * qTag lam : ℕ) : ℝ≥0∞) / (Fintype.card (Nonce lam) : ℝ≥0∞)) := by
    simpa only [div_eq_mul_inv] using negligible_natMul_of_poly_bound hNonce
      (g := fun lam => qReader lam * qTag lam) (p := pReader * pTag)
      (fun lam => by rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hpReader lam) (hpTag lam))
  have hSlack3 : negligible (fun lam =>
      ((qReader lam * Fintype.card (TagId lam) * sessionsPerTag lam : ℕ) : ℝ≥0∞) /
        (Fintype.card (Digest lam) : ℝ≥0∞)) := by
    simpa only [div_eq_mul_inv] using negligible_natMul_of_poly_bound hDigest
      (g := fun lam => qReader lam * Fintype.card (TagId lam) * sessionsPerTag lam)
      (p := pReader * pTagId * pSessions) (fun lam => by
        rw [Polynomial.eval_mul, Polynomial.eval_mul]
        exact Nat.mul_le_mul (Nat.mul_le_mul (hpReader lam) (hpTagId lam)) (hpSessions lam))
  exact negligible_of_le
    (fun lam => unlinkabilityAdvantage_le_two_prf_plus_collision
      (inst.prfs lam) (adversary lam) (qReader lam) (qTag lam) (hqReader lam) (hqTag lam))
    (negligible_add (negligible_add (negligible_add (negligible_add
      (negligible_add hPRFmulti hPRFsingle) hCollision) hSlack1) hSlack2) hSlack3)

end AsymptoticInstance

end PRFTagReader
