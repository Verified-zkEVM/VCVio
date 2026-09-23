/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Examples.PRFTagReader.UnlinkReduction
public import VCVio.CryptoFoundations.Asymptotics.Security

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
family. The concrete bound's collision and slack terms are `ℝ`-valued; an `ℝ`-valued error family
`ε : ℕ → ℝ` is *negligible* when `fun λ => ENNReal.ofReal (ε λ)` is `negligible`, and sums of such
families are handled by `negligible_ofReal_add`.

## Base bound

The base is the bound `unlinkabilityAdvantage_le_two_prf_plus_collision`, stated for
the concrete reductions `unlinkToMultiplePRFReduction` and `unlinkToSinglePRFReduction` (applied to
the adversary and to its output-negated variant). Its two `NeverFail` hypotheses are inherited
unchanged: they are necessary because an `UnlinkAdversary`
may itself contain `failure`, in which case the one-sided gap `Pr[Multiple] − Pr[Single]` stops
being odd under output negation.

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
  advantage of the concrete reduction of the adversary (and of its output-negated variant) is
  negligible;
* the nonce and digest spaces grow superpolynomially — `(|Nonce λ|)⁻¹` and `(|Digest λ|)⁻¹` are
  negligible;
* the adversary is a polynomial-query family and the instance parameters are polynomially bounded —
  `qReader`, `qTag`, `|TagId|`, and `sessionsPerTag` are each bounded by a fixed polynomial in `λ`;
* both experiments are failure-free at every `λ`.

Then the unlinkability advantage `unlinkabilityAdvantage` is negligible. -/
theorem negligible_unlinkabilityAdvantage
    (inst : AsymptoticInstance TagId Nonce Digest K sessionsPerTag)
    (adversary : (lam : ℕ) → UnlinkAdversary (TagId lam) (Nonce lam) (Digest lam))
    (qReader qTag : ℕ → ℕ)
    (hqReader : ∀ lam, OracleComp.IsQueryBoundP (adversary lam) (·.isRight) (qReader lam))
    (hqTag : ∀ lam, OracleComp.IsQueryBoundP (adversary lam) (·.isLeft) (qTag lam))
    (hMnf : ∀ lam, NeverFail (unlinkMultipleExp (inst.prfs lam) (adversary lam)))
    (hSnf : ∀ lam, NeverFail (unlinkSingleExp (inst.prfs lam) (adversary lam)))
    -- PRF asymptotic security (multiple + single, adversary + negated adversary):
    (hPRFmulti : negligible (fun lam =>
      (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam)))))
    (hPRFsingle : negligible (fun lam =>
      (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam) (adversary lam)))))
    (hPRFmulti' : negligible (fun lam =>
      (PRFScheme.prfAdvantage (inst.prfs lam).multiplePRFScheme
        (unlinkToMultiplePRFReduction (sessionsPerTag := sessionsPerTag lam)
          (adversary lam >>= fun b => pure (!b) :
            OracleComp (UnlinkOracleSpec (TagId lam) (Nonce lam) (Digest lam)) Bool)))))
    (hPRFsingle' : negligible (fun lam =>
      (PRFScheme.prfAdvantage (inst.prfs lam).singlePRFScheme
        (unlinkToSinglePRFReduction (sessionsPerTag := sessionsPerTag lam)
          (adversary lam >>= fun b => pure (!b) :
            OracleComp (UnlinkOracleSpec (TagId lam) (Nonce lam) (Digest lam)) Bool)))))
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
  have hCollision : negligible (fun lam => ENNReal.ofReal
      (Pr[fun z : Bool × MultipleBadState (TagId lam) (Nonce lam) (Digest lam) (sessionsPerTag lam)
          => z.2.2.bad |
        (simulateQ (multipleBadQueryImpl (TagId lam) (Nonce lam) (Digest lam) (sessionsPerTag lam))
          (adversary lam)).run
          ((UnlinkState.init, ∅), UnlinkBadState.init)]).toReal) := by
    refine negligible_of_le (g := fun lam => ENNReal.ofReal
      (((sessionsPerTag lam ^ 2 * Fintype.card (TagId lam) : ℕ) : ℝ) /
        (Fintype.card (Nonce lam) : ℝ))) (fun lam => ?_)
      (negligible_ofReal_natDiv_of_poly_bound (g := fun lam =>
        sessionsPerTag lam ^ 2 * Fintype.card (TagId lam))
        (p := pSessions ^ 2 * pTagId) hNonce (fun lam => ?_))
    · refine ENNReal.ofReal_le_ofReal ?_
      have hmax : ∀ nonce : Nonce lam,
          (Pr[= nonce | ($ᵗ Nonce lam : ProbComp (Nonce lam))]).toReal ≤
            ((Fintype.card (Nonce lam) : ℝ)⁻¹) := by
        intro nonce; simp [probOutput_uniformSample, ENNReal.toReal_inv]
      have hbad := multipleBad_bad_le_sessionCollisionBound (sessionsPerTag := sessionsPerTag lam)
        (adversary lam) ((Fintype.card (Nonce lam) : ℝ)⁻¹) (fun nonce => by
          let : MeasurableSpace (Nonce lam) := ⊤
          rw [prEvent_eq_evalDist_singleton]
          simpa only [evalDist_apply_singleton] using hmax nonce)
      simp only [evalDist_apply_singleton, probOutput_map] at hbad
      rwa [← div_eq_mul_inv] at hbad
    · rw [Polynomial.eval_mul, Polynomial.eval_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (hpSessions lam) 2) (hpTagId lam)
  -- Negligibility of each unconditional slack term.
  have hSlack1 : negligible (fun lam => ENNReal.ofReal
      (((qReader lam * Fintype.card (TagId lam) : ℕ) : ℝ) / (Fintype.card (Digest lam) : ℝ))) :=
    negligible_ofReal_natDiv_of_poly_bound (p := pReader * pTagId) hDigest (fun lam => by
      rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hpReader lam) (hpTagId lam))
  have hSlack2 : negligible (fun lam => ENNReal.ofReal
      (((qReader lam * qTag lam : ℕ) : ℝ) / (Fintype.card (Nonce lam) : ℝ))) :=
    negligible_ofReal_natDiv_of_poly_bound (p := pReader * pTag) hNonce (fun lam => by
      rw [Polynomial.eval_mul]; exact Nat.mul_le_mul (hpReader lam) (hpTag lam))
  have hSlack3 : negligible (fun lam => ENNReal.ofReal
      (((qReader lam * Fintype.card (TagId lam) * sessionsPerTag lam : ℕ) : ℝ) /
        (Fintype.card (Digest lam) : ℝ))) :=
    negligible_ofReal_natDiv_of_poly_bound (p := pReader * pTagId * pSessions) hDigest
      (fun lam => by
        rw [Polynomial.eval_mul, Polynomial.eval_mul]
        exact Nat.mul_le_mul (Nat.mul_le_mul (hpReader lam) (hpTagId lam)) (hpSessions lam))
  -- The PRF hypotheses in `ENNReal.ofReal ∘ toReal` form, matching the real-valued bound.
  have hofReal {f : ℕ → ℝ≥0∞} (hf : negligible f) (hfin : ∀ lam, f lam ≠ ⊤) :
      negligible (fun lam => ENNReal.ofReal (f lam).toReal) :=
    negligible_of_le (fun lam => (ENNReal.ofReal_toReal (hfin lam)).le) hf
  -- Pointwise `unlink = ofReal unlink.toReal ≤ ofReal (Σ termᵢ)` by the concrete bound; the
  -- bounding family is negligible as an `ofReal` of eight negligible real summands.
  exact negligible_of_le
    (fun lam => (ENNReal.ofReal_toReal (MeasureTheory.Measure.boolDist_ne_top _ _)).symm.le.trans
      (ENNReal.ofReal_le_ofReal (unlinkabilityAdvantage_le_two_prf_plus_collision
        (inst.prfs lam) (adversary lam) (qReader lam) (qTag lam) (hqReader lam) (hqTag lam)
        (hMnf lam) (hSnf lam))))
    (negligible_ofReal_add (negligible_ofReal_add (negligible_ofReal_add (negligible_ofReal_add
      (negligible_ofReal_add (negligible_ofReal_add (negligible_ofReal_add
        (hofReal hPRFmulti fun _ => MeasureTheory.Measure.boolDist_ne_top _ _)
        (hofReal hPRFsingle fun _ => MeasureTheory.Measure.boolDist_ne_top _ _))
        (hofReal hPRFmulti' fun _ => MeasureTheory.Measure.boolDist_ne_top _ _))
        (hofReal hPRFsingle' fun _ => MeasureTheory.Measure.boolDist_ne_top _ _))
        hCollision) hSlack1) hSlack2) hSlack3)

end AsymptoticInstance

end PRFTagReader
